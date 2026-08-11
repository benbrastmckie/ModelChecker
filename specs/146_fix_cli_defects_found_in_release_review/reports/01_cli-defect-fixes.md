# CLI Defect Fixes — Research Report

**Task**: 146 — Fix user-visible CLI defects surfaced by the 2026-08-11 release review
(`specs/reviews/review-20260811.md`, issues 8, 9, 11, 12, 13, 15)

**Scope constraint**: no behavior change beyond the six named items; no wholesale parser
refactor. Each fix independently verifiable; at least a minimal assertion per item (broad CLI
end-to-end coverage is a separate, dependent task).

All line numbers below were re-read directly from the current tree (not copied from the review)
and are current as of this report.

---

## Issue 8 — `-p` silently no-ops

**Files**: `code/src/model_checker/__main__.py`, `code/src/model_checker/settings/settings.py`

`ParseFileFlags.parse()` builds `self._short_to_long` at `__main__.py:202-216`:

```python
self._short_to_long = {
    'c': 'contingent',
    'd': 'disjoint',
    'e': 'non_empty',
    'l': 'load_theory',
    'm': 'maximize',
    'n': 'non_null',
    'q': 'sequential',
    's': 'save',
    'i': 'print_impossible',
    'v': 'version',
    'u': 'upgrade',
    'z': 'print_z3',
    'a': 'align_vertically'
}
```

`p` (→ `print_constraints`) is missing, even though `-p`/`--print_constraints` is a registered
argparse action (`__main__.py:153-158`). Root cause chain, confirmed by reading both files:

1. `argparse` itself parses `-p` fine and sets `module_flags.print_constraints = True` — the
   flag *is* correctly captured by argparse.
2. The bug is downstream, in `SettingsManager._extract_user_provided_flags`
   (`settings/settings.py:202-233`), which does NOT read `module_flags.print_constraints`
   directly. Instead it re-derives "what did the user type" from the *raw argv strings*
   (`module_flags._parsed_args`, set at `__main__.py:220,227`) via the same
   `_short_to_long` dict, to decide which settings-manager overrides to honor
   (`_apply_overrides`, `settings/settings.py:236-266`, gated by
   `if is_mock or key in user_provided_flags:` at line 257).
3. Because `'p'` has no entry in `_short_to_long`, `-p` never lands in
   `user_provided_flags`, so `_apply_overrides` skips `print_constraints` even though argparse
   set it to `True`. `--print_constraints` (long form) works because the long-form branch
   (`arg.startswith('--')`, line 221) needs no dict lookup at all.

**Minimal fix**: add `'p': 'print_constraints'` to the dict.

**Making the bug class unrepresentable** (task explicitly asks for this, offering two
options): the dict is a second, hand-maintained enumeration of every short flag already
registered on the parser (`__main__.py:70-186` lists 13 short options via
`add_argument('--long', '-x', ...)`, of which `_short_to_long` only encodes 13 of what should
be a 14-flag surface including `-p`; `--z3`/`--cvc5` have no short form, `--version`/`-v` is an
`action='version'`, `--upgrade`/`-u` and `--load_theory`/`-l` are not "settings" keys but are
still in the dict). Two viable directions, either acceptable per the task's phrasing:
  - **Derive from the parser**: iterate `self.parser._actions` (or, more robustly, avoid the
    private `_actions` attribute by tracking `(long, short)` pairs at `add_argument()` call
    sites) and build `_short_to_long` mechanically, e.g. by inspecting each `Action.option_strings`
    for a `--xxx`/`-x` pair and stripping the leading dashes. This removes the parallel literal
    entirely so a newly added short flag can never again be forgotten in a second location.
  - **Add a regression test**: a unit test that walks `parser._actions`, collects every
    single-character short option string, and asserts each has a matching entry in
    `_short_to_long` (and vice versa) — cheaper to implement, does not touch production code
    path, and satisfies "make the class unrepresentable" in the weaker sense of "make it
    immediately test-caught." Given the constraint against wholesale parser refactor, the
    test-based option is the lower-risk choice for this task; deriving from `_actions` is more
    robust long-term but touches the parsing code path itself. Recommend the test-based
    approach for this task, noting the derive-from-parser approach as a documented follow-up
    if the team prefers zero-literal enforcement over test-covered literal.

**Second, narrower gap (task asks to explicitly decide, not silently fix)**: the user-provided
flag extraction only recognizes single-character short tokens (`elif arg.startswith('-') and
len(arg) == 2:`, `settings/settings.py:225`). Clustered short flags like `-cn` (bundling
`-c` and `-n`) are accepted by argparse (argparse decomposes clusters of `store_true` flags
natively) and set both `contingent` and `non_null` correctly at the argparse level — but
`_extract_user_provided_flags` will not recognize `-cn` as either flag being user-provided
(it's not `len(arg)==2`), so **both** flags silently fail to override settings, the same class
of bug as issue 8 itself, just for clustered invocations. This is not one of the six named
defects and is explicitly out of scope for a behavior change per the task's constraints, but
per the task's own instruction ("decide explicitly whether to fix or document this") the
recommendation is: **document it** (e.g. a short comment on `_extract_user_provided_flags`
noting clustering is unsupported by the override-detection path) rather than fix it in this
task, since fixing it means either exploding cluster tokens char-by-char (a parsing-path
change, arguably within "wholesale parser refactor" territory) or accepting a second
non-trivial behavior change beyond the six named items.

**Verification**: a unit test asserting `-p` and `--print_constraints` produce identical
resulting settings (e.g. construct `ParseFileFlags`, monkeypatch `sys.argv` to
`['prog', '-p', 'file.py']` vs `['prog', '--print_constraints', 'file.py']`, run both through
`SettingsManager.apply_flag_overrides`, assert `print_constraints is True` in both). This can
live alongside the new short-flag-coverage test described above. No test file currently imports
`ParseFileFlags` (confirmed via `grep -rln "ParseFileFlags" code`, only `__main__.py` itself
matches) — this task should be the first to add one, most naturally under
`code/tests/unit/` (a new `test_main_cli.py` or similar; `code/tests/unit/` currently only has a
`syntactic/` subpackage, so a top-level file is consistent with existing layout) or under
`code/src/model_checker/tests/` if there is a package-local unit test convention — check
existing sibling packages (e.g. `builder/tests/`) for the preferred pattern before creating the
file.

---

## Issue 9 — `--load_theory` help text stale, no `choices=`

**Files**: `code/src/model_checker/__main__.py:72-78`, `code/src/model_checker/registry.py`

Current code:

```python
theory_group.add_argument(
    '--load_theory',
    '-l',
    type=str,
    metavar='THEORY',
    help='Load semantic theory: bimodal.'
)
```

Confirmed the registry is the intended single source of truth:
- `registry.get_registered() -> List[str]` (`registry.py:154-156`) returns registered theory
  names **in registration order**.
- `registry.iter_theories() -> Iterator[TheoryEntry]` (`registry.py:207-210`) yields the same
  set as full entries.
- `theory_lib/__init__.py:482`: `AVAILABLE_THEORIES = _core_registry.get_registered()` —
  confirms `theory_lib` itself treats the registry as canonical and does not hardcode the list
  either.
- `builder/project.py:111-119`: `BuildProject.__init__` already defaults `theory` to
  `registry.get_registered()[0]` instead of a literal name, exactly the precedent the task
  description points to.
- Import-order caveat: `registry.get_registered()` only returns entries that have been
  registered, and registration happens as a side effect of importing `theory_lib`
  (`theory_lib/__init__.py:462` calls `_core_registry.get_registered()` for
  `already_registered` dedup, and registers each theory during that module's own init). Because
  `__main__.py` already does `from model_checker.builder import (BuildProject, BuildModule)` at
  module scope (`__main__.py:13-16`), and `model_checker.builder` presumably imports
  `theory_lib` transitively (verify at implementation time — if not, add an explicit
  `from model_checker import theory_lib` import, or import `registry` lazily inside
  `_create_parser()` after confirming registration has occurred) — the parser-construction code
  must call `registry.get_registered()` only after theories are guaranteed registered, not at
  raw module import time before any such side effect fires.

**Fix**: build both `help=` and `choices=` from `registry.get_registered()` at parser-build
time (inside `_create_parser()`, which already runs once per `ParseFileFlags()` instantiation —
not at module import time), e.g.:

```python
from model_checker import registry
theories = registry.get_registered()
theory_group.add_argument(
    '--load_theory',
    '-l',
    type=str,
    metavar='THEORY',
    choices=theories,
    help=f"Load semantic theory: {', '.join(theories)}."
)
```

This makes an invalid `--load_theory` name fail fast at argparse time with a standard
`invalid choice` error instead of surfacing later as a `FileNotFoundError` inside
`BuildProject.__init__` (`builder/project.py:135-138`) or, per issue 6 of the review, an
unvalidated string that only fails once `BuildProject.generate()` tries to read
`self.source_dir`.

**Behavior-change caution**: adding `choices=` is itself new validation behavior (a previously
late/generic error becomes an early/specific one) but is explicitly what issue 9 asks for
("validates nothing" is named as the defect) — this is in scope, not an extra change. Confirm
the pre-existing test `test_invalid_theory_name` in
`code/tests/integration/test_error_handling.py:28-32` (asserts `returncode != 0` and
`'theory' in error_output.lower() or 'invalid' in error_output.lower()`) still passes: argparse's
own `invalid choice: 'invalid_theory' (choose from ...)` message satisfies both substring checks,
so this existing test should continue to pass unmodified and doubles as a regression check for
the fix, though it was written before `choices=` existed and was presumably passing via the
`FileNotFoundError` path previously — worth running explicitly post-fix.

**Verification**: (a) `model-checker --help` (or `--load_theory --help`) shows all four theory
names; (b) a unit test asserting `parser.parse_args(['--load_theory', 'logos', ...])` succeeds
and `parser.parse_args(['--load_theory', 'nonsense', ...])` raises `SystemExit` (argparse's
standard behavior for invalid `choices`); (c) re-run
`code/tests/integration/test_error_handling.py::TestCLIErrorHandling::test_invalid_theory_name`.

---

## Issue 11 — `--save jupyter` accepted, then silently discarded; stale help text

**Files**: `code/src/model_checker/__main__.py:115-123`,
`code/src/model_checker/output/config.py:39-79`

`__main__.py:115-123`:

```python
output_group.add_argument(
    '--save',
    '-s',
    nargs='*',
    choices=['markdown', 'json', 'jupyter'],
    default=None,
    help='Save results. Formats: markdown, json, jupyter. '
         'No args = all formats. With args = specified only'
)
```

`output/config.py:53-79` (`create_output_config`), confirmed by direct read:

```python
formats = []
save_output = False

if hasattr(args, 'save') and args.save is not None:
    save_output = True
    if len(args.save) == 0:
        # --save with no args means all formats
        formats = ['markdown', 'json']
    else:
        for fmt in args.save:
            if fmt in ('markdown', 'md'):
                formats.append('markdown')
            elif fmt == 'json':
                formats.append('json')
```

Two confirmed defects:
1. `jupyter` is accepted by argparse (`choices=[...,'jupyter']`) but silently dropped by the
   `if/elif` chain in `create_output_config` — no `elif fmt == 'jupyter':` branch exists.
   `--save jupyter` therefore yields `OutputConfig(formats=[], save_output=True)`: the
   `should_save()` gate downstream (referenced in `builder/module.py:167,175`,
   `_initialize_output_management`) will be true, so an output directory is created
   (`self.output_manager.create_output_directory()`), but nothing is ever written to it because
   `formats` is empty — no error, no output, an empty directory as the only trace.
2. `--save` with **zero** args is documented as "No args = all formats" but the code hardcodes
   `formats = ['markdown', 'json']` — `jupyter` is never included even in the "all formats"
   case, so the phrase "all formats" is inaccurate today independent of whether jupyter format
   support is implemented at all.

**Task's own instruction**: "Either implement the format or remove it from `choices`." This is
a product decision the task grants either resolution for. Given the CONSTRAINTS
("no behavior change beyond these six items... do not refactor the parser wholesale") and no
evidence in this codebase of any Jupyter export pipeline (searched — no `jupyter` format writer
exists anywhere under `code/src/model_checker/output/`; the only Jupyter-related code is the
unrelated dependency pre-check at issue 13's `__main__.py:252-270`, which checks
`ipywidgets`/`matplotlib`/`networkx` for interactive notebook *usage*, not for an export
format), implementing a genuine new jupyter-notebook output writer is a much larger surface
than "polish defect" scope. **Recommendation: remove `'jupyter'` from `choices=` in
`__main__.py:119`** and drop the word "jupyter" from the help string
(`__main__.py:121`), which resolves both the silent-discard defect and (trivially) removes the
now-impossible choice from being advertised. This is the minimal, scope-respecting fix.

Independently, fix the "No args = all formats" wording to match the actual (post-fix, two
supported formats) behavior, e.g. `'No args = markdown + json. With args = specified formats
only'` — a pure doc-string edit, zero runtime behavior change.

**Note for whoever implements**: removing `'jupyter'` from `choices=` is itself a small,
argparse-level *behavior* change (a previously-accepted-but-broken value becomes a rejected
value with a standard "invalid choice" argparse error) — this is exactly what issue 11 asks
for, not scope creep, but flag it in the implementation summary since the review's own
"CONSTRAINTS" line says "no behavior change beyond these six items," which should be read as
"beyond what each of the six items itself calls for."

**Verification**: (a) `model-checker --save jupyter examples.py` now exits non-zero with an
argparse `invalid choice` error rather than silently succeeding with no output; (b) a unit
test on `create_output_config` (or an equivalent argparse-choices test) asserting `'jupyter'`
is no longer in `parser._option_string_actions['--save'].choices` (or, more directly, that
`parser.parse_args(['--save', 'jupyter'])` raises `SystemExit`); (c) `--save` with zero args
still yields `formats == ['markdown', 'json']` (unchanged) and the help string no longer
mentions "jupyter" or overstates "all formats."

---

## Issue 12 — `--sequential`/`-q` advertised but raises `NotImplementedError`

**Files**: `code/src/model_checker/__main__.py:124-129`,
`code/src/model_checker/builder/module.py:158-178`

`__main__.py:124-129`:

```python
output_group.add_argument(
    '--sequential',
    '-q',
    action='store_true',
    help='Prompt to save each model individually (interactive mode)'
)
```

`builder/module.py:158-178` (`_initialize_output_management`), confirmed by direct read — the
raise is unconditional whenever `config.sequential` is truthy, with a comment already
explaining *why* (the supporting classes were deliberately deleted in a prior task, not a bug):

```python
self.prompt_manager = None
if config.sequential:
    raise NotImplementedError(
        "Interactive sequential-save mode (--sequential / settings "
        "'sequential') is not supported: SequentialSaveManager and "
        "ConsoleInputProvider were removed from model_checker.output "
        "and are not being restored. Use the default batch mode with "
        "--save instead."
    )
```

Key finding: **the failure message is already clear and user-facing** — this is not a bare
traceback from an undocumented internal exception; it's a deliberately-raised
`NotImplementedError` with an explanatory string. But it is still an *uncaught* exception at the
top level: `main()` in `__main__.py` has no try/except around `BuildModule(module_flags)`
(`__main__.py:306`), so the user still sees a full Python traceback (`Traceback (most recent
call last): ... NotImplementedError: Interactive sequential-save mode...`) rather than a clean
one-line CLI error. The task offers two resolutions: "hide the flag until implemented" or "fail
with a clear user-facing message instead of a traceback."

**Recommendation**: keep the flag registered (hiding it is also valid per the task, but removing
a documented, if broken, flag from `--help` without an alternative could itself read as a
regression to a user who has `--sequential` in a saved script — though `-q` was never usable in
the first place per this issue, so hiding is defensible too). The lower-risk fix given the
CONSTRAINTS ("no behavior change beyond these six items") is to **catch `NotImplementedError` at
the `main()` call site (or one layer down, wherever `BuildModule(...)` is constructed) and print
a clean one-line error + exit non-zero**, rather than removing/hiding the flag, since hiding
changes `--help` output surface area beyond just fixing the traceback. Concretely: wrap
`module = BuildModule(module_flags)` at `__main__.py:306` (or, more locally, wrap only the
`_initialize_output_management` call inside `BuildModule.__init__`) in a
`try/except NotImplementedError as e: print(f"Error: {e}"); sys.exit(1)`-style handler. This
converts an unhandled traceback into the same "Error: ..." + clean exit pattern already used
elsewhere in `__main__.py` for other failure paths (e.g. `__main__.py:288-291` for the cvc5
`ImportError` case, `__main__.py:297-298` for the upgrade `CalledProcessError` case) — i.e. this
fix follows an existing, established error-handling convention in the same file rather than
inventing a new one.

Given the task phrasing explicitly allows "hide the flag" as an alternative, note it here for
completeness: hiding would mean removing `-q`/`--sequential` from `_create_parser()` and from
`_short_to_long['q']`, and deleting the now-dead `config.sequential` branch — but this touches
more surface (parser registration, the short-flag map from issue 8, and the settings default in
`settings/settings.py`) than the catch-and-report approach, so it is not the recommended default
unless product intent is confirmed to be "no sequential mode, ever."

**Verification**: `model-checker --sequential examples.py` (or `-q`) exits non-zero with a
single clean `Error: ...` line and no Python traceback (assert via `run_cli_command(['-q',
'examples.py'], check=False)`: `result.returncode != 0` and no `"Traceback"` substring in
`result.stderr`).

---

## Issue 13 — Dead `-j`/`--jupyter` pre-check block

**File**: `code/src/model_checker/__main__.py:253-270`

```python
jupyter_flags = ["-j", "--jupyter"]
needs_jupyter = any(flag in sys.argv for flag in jupyter_flags)

if needs_jupyter:
    missing_deps = []
    for pkg in ["ipywidgets", "matplotlib", "networkx"]:
        try:
            __import__(pkg)
        except ImportError:
            missing_deps.append(pkg)

    if missing_deps:
        print(f"Error: The following required dependencies are missing: {', '.join(missing_deps)}")
        print("To use Jupyter notebook features, install them with:")
        print("  pip install model-checker[jupyter]")
        return
```

Confirmed unreachable: neither `-j` nor `--jupyter` appears anywhere in
`ParseFileFlags._create_parser()` (`__main__.py:35-187`, full read — no such
`add_argument` call exists). Since this block runs *before* `ParseFileFlags().parse()` is even
constructed (it's the first thing in `main()`, at `__main__.py:253`, ahead of the `len(sys.argv)
< 2` check at line 272 and the `parser = ParseFileFlags()` call at line 276), if a user actually
typed `-j` or `--jupyter`, this block *would* run and print its dependency message — but then
control falls through to `parser.parse()` at line 277, and argparse itself will immediately
reject the unrecognized `-j`/`--jupyter` token with its own `unrecognized arguments` error and
`SystemExit(2)`, which happens after the dependency message already printed. So the block is not
strictly dead code (it does execute), but its *purpose* (gate on Jupyter deps before running) is
defeated because argparse always rejects the invocation immediately afterward — the user gets a
dependency-check message immediately followed by an "unrecognized arguments: -j" argparse error,
which is confusing and never reaches actual Jupyter functionality either way. This matches the
task's characterization ("unreachable" in the sense that its intended purpose can never be
fulfilled).

**Task's options**: "Delete it, or register the flag if the dependency-hint behavior is
wanted." No `--jupyter`/`-j` argparse action exists anywhere, and no other code path in
`__main__.py` or `builder/` branches on a `jupyter` flag — there is no evidence of intended
Jupyter-mode CLI behavior beyond this orphaned check (Jupyter support in this codebase appears
to live entirely in the `model_checker.jupyter` package for use *inside* notebooks, e.g.
`jupyter/adapters.py`, not as a CLI mode). **Recommendation: delete the block** (lines
253-270, plus the two lines that no longer have a referent), the simpler and clearly
scope-respecting option — registering a new flag would be a net-new feature, out of place in a
"polish defect" cleanup task with an explicit "no behavior change beyond these six items"
constraint.

**Verification**: (a) `grep -n "jupyter_flags\|needs_jupyter" code/src/model_checker/__main__.py`
returns nothing after the fix; (b) existing CLI invocations without `-j`/`--jupyter` behave
identically (this code path was a no-op for every real invocation already, so no behavioral
test is needed beyond confirming the full suite still passes); (c) optionally, a unit test
confirming `model-checker -j` and `model-checker --jupyter` both fail with argparse's
`unrecognized arguments` error (unchanged before/after — this documents that removing the dead
block does not change observable behavior for any input).

---

## Issue 15 — `__pycache__` warning leaks to users

**File**: `code/src/model_checker/builder/project.py`

Confirmed the mechanism precisely:
- `project.py:76`: `COPY_IGNORE_PATTERNS = ['__pycache__', '.ipynb_checkpoints']` — used only
  by `shutil.copytree(..., ignore=shutil.ignore_patterns(*COPY_IGNORE_PATTERNS))` at line
  ~285, which prevents `__pycache__` from being copied **into** subdirectories that are
  themselves already being copied (e.g. it stops a stray `theory/__pycache__/` nested inside a
  copied subpackage from being duplicated into the new project).
- This does **not** cover the top-level manifest-filtering loop at lines 267-273:
  ```python
  allowed_items = set(REQUIRED_COPY_ITEMS) | set(semantic_present) | set(OPTIONAL_COPY_ITEMS)

  for item in sorted(available):
      if item not in allowed_items:
          self.log(f"Skipped non-manifest item: {item}", "WARNING")
          continue
      ...
  ```
  `available = set(os.listdir(self.source_dir))` (line 243) lists every entry in the theory's
  source directory, including a `__pycache__/` directory left over from Python having imported
  that theory's modules at some point (confirmed reproducible from an installed wheel per the
  review). Since `__pycache__` is never in `REQUIRED_COPY_ITEMS`, `semantic_present`, or
  `OPTIONAL_COPY_ITEMS`, it falls into the `if item not in allowed_items:` branch and gets
  logged at `WARNING` level.
- `log()` (`project.py:131-143`) prints WARNING-level messages immediately to stdout
  (`elif level == "WARNING": print(f"Warning: {message}")`), which is exactly the leak the
  review reproduced: `Warning: Skipped non-manifest item: __pycache__` on every project
  generation.
- Two other places in the same file already special-case `__pycache__` deliberately
  (`project.py:374-375` skip-hidden-dirs-and-pycache during directory walk;
  `project.py:678-679` filter pycache out of `subdir_items`), confirming the codebase already
  treats `__pycache__` as "never worth mentioning" everywhere except this one manifest-check
  branch, which the review calls out as the inconsistency.

**Fix**: exclude `__pycache__` (and, for symmetry with `COPY_IGNORE_PATTERNS`,
`.ipynb_checkpoints` and `*.pyc`, since the task says "Suppress `__pycache__`/`*.pyc` silently")
from ever reaching the `if item not in allowed_items:` WARNING branch. Two ways to do this
without touching the manifest constants themselves (safer, since `REQUIRED_COPY_ITEMS` /
`OPTIONAL_COPY_ITEMS` are meaningful contract lists elsewhere, e.g. referenced in
`docs/THEORY_ARCHITECTURE.md` per an existing comment at `project.py:225-226`):
  - Reuse the existing `COPY_IGNORE_PATTERNS` list (already defined at line 76 for exactly this
    kind of "never worth copying or mentioning" purpose) as a pre-filter: change the loop to
    skip (silently `continue`, no `log()` call) any `item` that matches `COPY_IGNORE_PATTERNS`
    or looks like a `.pyc` file, before the `allowed_items` check runs. This is the more
    consistent fix since it reuses an existing, already-named constant instead of introducing a
    new one.
  - Alternatively, filter `available` itself right after line 243:
    `available = {i for i in os.listdir(self.source_dir) if i not in COPY_IGNORE_PATTERNS and
    not i.endswith('.pyc')}` — arguably cleaner since every downstream use of `available` (the
    `semantic_present` check, `missing_required` check, and the copy loop) then automatically
    never sees `__pycache__`/`.pyc` at all, rather than special-casing it only at the warning
    site.

Either approach satisfies "Suppress `__pycache__`/`*.pyc` silently — they are never manifest
items and their presence is not a condition worth reporting" without weakening the warning for
any *other* genuinely-unexpected non-manifest item (e.g. a stray `.DS_Store` or an editor swap
file would still warn, which is correct — the task only asks to silence pycache/pyc, not to
remove the warning mechanism itself).

**Verification**: (a) `BuildProject(theory).generate(...)` against a source theory directory
that has a `__pycache__/` present (trivially reproducible: `python -c "import
model_checker.theory_lib.bimodal"` populates `__pycache__` under the source tree, or construct
one in a tmp fixture) produces zero `"Skipped non-manifest item: __pycache__"` log entries in
`self.log_messages` and prints nothing matching that string to stdout; (b) a genuinely unknown
non-manifest item (e.g. write a throwaway `stray_file.tmp` into a copy of the source dir in a
test fixture, or use `tmp_path` to build a synthetic source tree) still produces the WARNING —
i.e. the fix is scoped to pycache/pyc, not a blanket suppression.

---

## Cross-Cutting Notes

- **No file currently imports or unit-tests `ParseFileFlags`** (`grep -rln "ParseFileFlags"
  code --include=*.py` matches only `__main__.py` itself). Issues 8, 9, 11, 13 all touch this
  class or its immediate call sites, so this task is a natural, low-risk place to add the first
  direct unit-test coverage the review's own issue 6 calls out as entirely missing — without
  taking on issue 6's full scope (that remains a separate, larger "CLI end-to-end suite" task
  per the task description's CONSTRAINTS section).
- **Where to put new tests**: `code/tests/unit/` exists but currently only contains a
  `syntactic/` subpackage (confirmed via `find code/tests -maxdepth 2 -type d`); a new
  `test_main_cli.py` (or similar) at that level, or a package-local
  `code/src/model_checker/tests/` if a sibling package's convention favors that (e.g.
  `builder/tests/` exists per the review's issue 4/5/6 file references) are both defensible —
  check `builder/tests/test_package_loading.py` and `builder/tests/test_issue_73_fix.py`
  (named in review issues 4 and 5) as precedent before choosing.
- **Existing integration coverage to re-run, not just add to**: `run_cli_command` (helper in
  `code/tests/utils/helpers.py:14-38`, spawns `python -m model_checker` as a real subprocess
  with `PYTHONPATH` set) and `code/tests/integration/test_error_handling.py` (esp.
  `test_invalid_theory_name` at line 28, `test_invalid_cli_flags` at line 58, and the
  currently-empty `test_conflicting_flags` stub at line 69 — review issue 6 calls this stub
  out explicitly; filling it in is optional here but would be a cheap, in-scope opportunity
  since `--sequential` now has a "conflicting" flavor of failure worth asserting, if the
  implementer wants to close part of issue 6 opportunistically without expanding into full
  scope).
- **Ordering suggestion for implementation**: issues 13 and 15 are pure deletions/filters with
  no interaction with the others — do them first as zero-risk warmups. Issue 8 and issue 9 both
  touch `__main__.py:_create_parser()`/`parse()` but are otherwise independent of each other.
  Issue 11 and issue 12 both touch the output/save path (`output/config.py` and
  `builder/module.py` respectively) but are also independent of each other and of 8/9/13/15.
  No two issues touch the same line ranges, so all six are safely implementable and testable in
  any order or in parallel phases.
- **Full-suite regression baseline**: the review recorded 2193/2193 passing
  (`PYTHONPATH=src pytest tests/` → 283/283; in-package suite → 1910/1910). Re-run both after
  the fixes; none of the six changes touch code paths outside `__main__.py`,
  `output/config.py`, `builder/module.py`, and `builder/project.py`, so a full-suite green
  result plus the new targeted assertions above should be sufficient verification.

## Summary Table

| # | Defect | File(s) | Root cause | Recommended fix | Verification |
|---|--------|---------|-------------|------------------|---------------|
| 8 | `-p` no-ops | `__main__.py:202-216`, `settings/settings.py:202-233` | `_short_to_long` missing `'p'` entry; downstream override gate keys off this dict, not off argparse's own parsed value | Add `'p': 'print_constraints'`; add a test asserting every registered short option has a mapping entry (or derive the dict from the parser) | Unit test: `-p` and `--print_constraints` yield identical settings |
| 9 | `--load_theory` help stale, unvalidated | `__main__.py:72-78` | Hardcoded `help=` string, no `choices=`; registry (`registry.py:154-156,207-210`) already the source of truth elsewhere (`builder/project.py:111-119`, `theory_lib/__init__.py:482`) | Build `help=` and `choices=` from `registry.get_registered()` at parser-construction time | `--help` lists 4 theories; invalid theory name now fails at argparse with `SystemExit` |
| 11 | `--save jupyter` silently discarded; stale help wording | `__main__.py:115-123`, `output/config.py:53-79` | `jupyter` is a valid `choices=` entry but `create_output_config`'s if/elif has no jupyter branch | Remove `'jupyter'` from `choices=`; fix "No args = all formats" wording | `--save jupyter` now fails at argparse; help text accurate |
| 12 | `--sequential`/`-q` raises `NotImplementedError` uncaught | `__main__.py:124-129`, `builder/module.py:158-178` | Deliberate, already-explained raise, but uncaught at `main()`'s call site — traceback, not a clean error | Catch `NotImplementedError` around `BuildModule(...)` construction and print+exit cleanly, following the existing `__main__.py` error-message convention | `--sequential` exits non-zero with a one-line `Error: ...`, no traceback |
| 13 | Dead `-j`/`--jupyter` pre-check | `__main__.py:253-270` | Flags checked via raw `sys.argv` scan but never registered on the parser; argparse rejects them regardless | Delete the block | `grep` for `jupyter_flags`/`needs_jupyter` returns nothing; unrecognized-argument behavior unchanged |
| 15 | `__pycache__` warning leaks | `builder/project.py:267-273` | Manifest-filter loop doesn't reuse the existing `COPY_IGNORE_PATTERNS` (line 76) that other pycache-aware code paths in the same file already use | Skip `__pycache__`/`.pyc`/`.ipynb_checkpoints` silently before the `allowed_items` warning check | No pycache warning in `log_messages`/stdout; a genuinely-unknown stray file still warns |
