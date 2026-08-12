# Research: Real End-to-End Verification for the CLI

Task 148. Session `sess_1786505927_3bc048`.

## 1. Confirmed gap inventory (verified against current source)

All claims in the task description were checked against the current tree and are accurate as of
this research pass, with one important update: **part of gap (a) has already been closed by task
149**, landed after the review that raised this task.

### 1.1 Console-script coverage — partially closed already

`code/tests/packaging/test_entry_point.py` (added at commit `89f887a9`, "task 149 phase 5:
console-script entry-point assertion") already builds a wheel, installs it into a fresh venv via
the session-scoped `installed_venv` fixture, and asserts:
- `test_console_script_installed_and_executable` — the `model-checker` script exists and is
  executable in the venv's `bin/`.
- `test_console_script_runs` — `model-checker --version` exits 0 with non-empty stdout, invoked
  as `[str(script_path), "--version"]` (the actual console script, not `python -m`).
- `test_entry_point_module_importable` — `from model_checker.__main__ import run` resolves in the
  installed venv.

Its own docstring states the intended split: "minimal declare-install-run liveness check... broader
console-script behavior coverage belongs to `code/tests/e2e/`." So the *existence check* is done;
the *behavioral flag matrix* and *generate-then-execute* work described in (b)-(d) below is not,
and is exactly what this task's `<literature-briefing>`-free scope should build. The
`installed_venv` fixture is currently private to `test_entry_point.py` (a module-level fixture,
not in `tests/packaging/conftest.py`), so it is not shared with other files as written.

`tests/packaging/conftest.py` supplies `packaging_toolchain` and `built_artifacts` (session-scoped,
build a wheel/sdist into a pytest temp dir, `PIP_USER=0`/`--no-user`, CI-gated skip/fail via
`_provisioning_failure` — never a silent pass, matching this repo's fail-fast philosophy). Building
new console-script tests on top of this existing wheel-build-and-venv-install infrastructure avoids
introducing a second, divergent way to invoke the real entry point.

**Cost implication**: this is a `pytest.mark.packaging, pytest.mark.slow` session-scoped fixture —
builds a wheel and does a full `pip install` into a fresh venv once per test session. Adding a large
flag matrix and 4-theory generate-then-execute sweep as console-script subprocess invocations
against this fixture is cheap per-test (each is just a subprocess call against the same installed
venv) but the fixture setup itself is the expensive part, already paid once. The alternative —
running everything through `python -m model_checker` (as `tests/utils/helpers.py::run_cli_command`
does today) — is fast but does not exercise the actual `[project.scripts]` entry point, which is
precisely the gap the review flagged. The plan should decide, per requirement, whether that
requirement needs the *real* console script (a, and arguably d, since "primary user journey"
implies what a real user runs) or can accept `python -m` (b, c can reasonably use `python -m` for
the bulk of the ~15-flag matrix, since flag *parsing* behavior does not depend on which entry point
invokes `ParseFileFlags`/`argparse` — only the entry-point-resolution question in (a) does).

### 1.2 `ParseFileFlags` — confirmed untested

`code/src/model_checker/__main__.py:19-237`. Key structure for test design:
- `_create_parser()` builds one `argparse.ArgumentParser` with groups: theory selection
  (`-l`/`--load_theory`, choices from `registry.get_registered()`), model constraints
  (`-c`/`--contingent`, `-n`/`--non_null`, `-e`/`--non_empty`, `-d`/`--disjoint`,
  `-m`/`--maximize`), output control (`-s`/`--save` `nargs='*'` choices
  `['markdown','json']`, `-q`/`--sequential`, `-a`/`--align_vertically`), solver
  (`--z3`/`--cvc5`, mutually exclusive, no short forms), debugging (`-p`/`--print_constraints`,
  `-z`/`--print_z3`, `-i`/`--print_impossible`), utility (`-v`/`--version` action=`version`,
  `-u`/`--upgrade`).
- `parse()` builds `self._short_to_long` (14 entries, hardcoded dict at :208-223) and stamps
  `flags._short_to_long` and `flags._parsed_args = sys.argv[1:]` onto the returned Namespace —
  **this exact mechanism is what the `-p` regression class depends on downstream**: see 1.3.
- `registry.get_registered()` currently returns `['bimodal', 'logos', 'exclusion', 'imposition']`
  (verified live) — 4 registered theories, in registration order. Import is intentionally lazy
  inside `_create_parser()` (comment explains circular-import avoidance), so a test constructing
  `ParseFileFlags()` directly (not via subprocess) needs `model_checker.theory_lib` already
  imported/registry populated — true for any test importing `model_checker` normally.

Existing coverage: `code/tests/integration/test_error_handling.py:15-73`,
`TestCLIErrorHandling` — 5 cases, all error-path only (`test_invalid_file_path`,
`test_invalid_theory_name`, `test_malformed_module_syntax`, `test_missing_required_attributes`,
parametrized `test_invalid_cli_flags`), plus `test_conflicting_flags` at :69-73 which is a literal
`pass` body with a comment ("Test mutually exclusive flags if any exist... For example, batch and
interactive modes if they conflict") — dead code, no real mutex assertion, despite `--z3`/`--cvc5`
being an actual `add_mutually_exclusive_group()` that could be tested here. `ParseFileFlags` itself
(the class, its short/long map, `.parse()` return values) is never imported by any test file
(confirmed via grep — zero non-comment `import.*ParseFileFlags` or `from model_checker.__main__
import` hits outside `__main__.py` itself).

### 1.3 The `-p` short/long equivalence regression path — confirmed, this is the load-bearing detail

`code/src/model_checker/settings/settings.py:202-274`
(`SettingsManager._extract_user_provided_flags` / `_apply_overrides`):
- For a real (non-mock) `argparse.Namespace`, "was this flag user-provided" is determined by
  **re-scanning the raw `sys.argv` tokens** stored on `_parsed_args`, not by inspecting the
  Namespace's boolean attributes directly. `--flag` tokens strip the `--` and (optionally)
  `=value`; short tokens are recognized **only when `len(arg) == 2`** (i.e. exactly `-x`), then
  mapped through `_short_to_long`.
- A **documented, deliberate** gap sits right next to this: clustered short flags (`-cn` for
  `-c` and `-n` together) parse fine in argparse but are silently **not** detected as
  user-provided here, since `len('-cn') != 2` — the code comment at :214-220 calls this
  "deliberately out-of-scope," not a bug to fix in this task, but it IS a case the new tests
  should assert stays *documented and non-silent* (e.g. a test that clustered flags do NOT
  override the setting, matching the comment, rather than assuming they do).
- `_apply_overrides` then walks `vars(module_flags)`, skips `_`-prefixed keys and `file_path`,
  and for real argparse objects only overrides `merged_settings[key]` when `key in
  user_provided_flags`. This is the exact mechanism a short-flag/long-flag mapping bug (the `-p`
  defect referenced in the task) would break: if `_short_to_long` mis-maps a letter, or if a
  flag's short form isn't recognized as "provided," the setting silently keeps its default
  instead of being overridden — a silent no-op, not a crash, which is why it shipped undetected.
- `standard_args` at :253-255 (`load_theory, upgrade, version, save, interactive, output_mode,
  sequential_files, z3, cvc5, subtheory`) are flags that intentionally do NOT correspond to a
  settings-dict key and must not trigger the "unknown flag" warning at :273-274. `interactive` is
  in this list, confirming it is a recognized-but-inert placeholder in the settings layer, not
  something `ParseFileFlags`/argparse ever produces (see 1.6).

**Recommended regression-guard test shape** (per task requirement "b"): for every entry in
`ParseFileFlags()._short_to_long` (built by parsing `-x` alone, and separately `--long-name`
alone, through a full `parse()`/`SettingsManager` round trip), assert the resulting merged
settings dict is identical for the short and long spellings. This directly targets the mapping
table and the `_parsed_args`-based detection logic, which is exactly what a stale/incorrect
`_short_to_long` entry would break.

### 1.4 Flag matrix — confirmed zero CLI-level coverage of behavior

Grep across `code/tests/` and `code/src/model_checker/**/tests/` for subprocess-level assertions
tied to each flag turned up nothing beyond the error-path tests in 1.2 and the malformed
`test_full_pipeline.py`/`test_batch_output_real.py` cases described in the task. Notable
call-sites to design tests against:
- `--maximize`/`-m` dispatches to `module.comparison.run_comparison()` at `__main__.py:301-303`.
  `BuildModule.comparison` implements `ModelComparison.run_comparison()` in
  `code/src/model_checker/builder/comparison.py:140+`, which iterates `example_range` against all
  `semantic_theories` via a `ProcessPoolExecutor` (see :108-135, `_find_max_N_static`/timeout
  handling) — a real subprocess-level `-m` test needs a **small, fast** example (`N` kept tiny) to
  avoid inflating suite runtime, since this path forks worker processes.
- `--z3`/`--cvc5` dispatch: `set_cli_backend`/`validate_backend` live in
  `code/src/model_checker/solver/registry.py:59` and `:121`. The `cvc5`-missing path at
  `__main__.py:271-279` catches `ImportError` from `validate_backend("cvc5")`, prints two lines
  (`Error: {e}` and the `pip install cvc5` hint), and returns cleanly (exit 0, not a crash) — this
  exact "graceful missing-optional-dependency" behavior is what part (c) asks to cover, and it is
  the one solver path guaranteed to be exercisable in this environment (cvc5 not installed here).
- `--upgrade`/`-u` at `__main__.py:281-287` shells out via `subprocess.run([sys.executable, '-m',
  'pip', 'install', '--upgrade', package_name], check=True)`. Task explicitly says not to execute
  this — verified the call is trivially mockable (`unittest.mock.patch('subprocess.run')`) to
  assert the constructed argv list and that `check=True` is passed, without ever hitting the
  network or mutating the environment.
- `--save`/`-s`: `nargs='*'` with `choices=['markdown','json']`, default `None` (flag entirely
  absent means "don't save" — distinct from `-s` with zero args meaning "save both"). A real test
  needs to assert actual output files land on disk (task explicitly calls this out — "assert files
  are actually produced"), which means running in a `tmp_path`/`cwd`-controlled subprocess and
  checking for the output directory/files `BuildModule`'s output layer creates, not just
  returncode.

### 1.5 Generate-then-execute — confirmed absent, registry-driven design is straightforward

- `BuildProject.generate(name, destination_dir=None)` at
  `code/src/model_checker/builder/project.py:171` is the non-interactive generation API already
  used correctly by `tests/e2e/test_project_creation.py::test_project_directory_creation` (直接
  calls `BuildProject(theory=...).generate(name=..., destination_dir=str(tmp_path))`, verified
  project dir named `project_{name}`). `ask_generate()` at :146 is the *interactive* path (prompts
  via `input()`), which is what `test_issue_73_fix.py:82-99
  test_handle_example_script_simulation` short-circuits with `patch('builtins.input',
  return_value='n')` — confirming the task's claim that the one place this journey is superficially
  touched deliberately skips the execution branch.
- `registry.get_registered()` (see 1.2) gives the exact 4-theory list to drive a
  `@pytest.mark.parametrize("theory_name", registry.get_registered())`-style test — no hardcoded
  theory list needed, matching the task's explicit ask to "drive this off the registry."
- The generated project's `examples.py` is what must be run through the console script (or at
  minimum `python -m model_checker`) after generation — this is the one piece with no existing
  reusable helper; `tests/utils/helpers.py::create_temp_project` explicitly *hand-writes* a
  synthetic project (task's own words: "hand-writes a fake project and never calls
  BuildProject") rather than using `BuildProject.generate()`, so it cannot be reused for this
  requirement without being replaced or bypassed.
- Review's manual baseline to match/regress against: 4/4 theories exit 0, output line counts
  logos/exclusion/imposition/bimodal = 1099/188/95/770 (per task description, from
  `specs/reviews/review-20260811.md` issues 4-6) — useful as a sanity range check (e.g. "output is
  non-trivial, > N lines") rather than an exact-line-count assertion, since output length is
  liable to drift with unrelated formatting changes; an exact match would make this test overly
  brittle for a task not otherwise touching that formatting.

### 1.6 Misleading/dead existing files — confirmed, with exact fix targets

- `builder/tests/test_package_loading.py::TestSubprocessExecution::test_pythonpath_setup_in_subprocess`
  (line ~244-289 per grep) `@patch('subprocess.run')`s and then asserts against `mock_run.call_args`
  — it invokes `subprocess.run(["model-checker", examples_path], env=env, check=True,
  timeout=30)` under the patch, so **no production code path executes at all**; the assertions are
  entirely about the test's own call arguments. Task says fix-or-delete; given `test_entry_point.py`
  already owns the "does invoking model-checker with PYTHONPATH-adjacent env work" question at the
  real-subprocess level (once this task adds generate-then-execute coverage), deleting this test is
  the lower-risk option — there is no unique behavior left uniquely covered by it once (d) lands.
  If kept, it would need to become a real subprocess call against a generated project.
- `code/tests/e2e/test_batch_output_real.py::TestBatchOutputReal::test_bimodal_batch_output` — file
  name says "batch output," docstring says "Test bimodal CLI invocation succeeds with correct
  flags," but the visible body (through the point read) only asserts `returncode == 0` from a
  correct `-l bimodal` subprocess call; nothing about *batch* output specifically (no
  `--save`/multiple-example/output-count assertions found). Confirms task's claim.
- `code/tests/e2e/test_project_creation.py` — confirmed it largely wraps
  `tests/utils/helpers.py::create_temp_project` (the hand-written-project helper), with one
  exception (`test_project_directory_creation`) that does call the real `BuildProject.generate()`
  API. So this file is a mix — worth noting in planning that at least one real-API test already
  exists here as a pattern to extend, not purely dead weight.
- `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py::test_iteration_workflow`
  (confirmed at the file, function starting ~line 89) passes `-i` with `input="2\n\n"` expecting an
  "iteration" prompt/flag; `-i` is actually `--print_impossible` (boolean store_true, no interactive
  iteration count prompt exists in `ParseFileFlags`) — the stdin is unused by anything `-i` triggers,
  and the test's premise (that `-i` requests N iterations) does not match the registered flag table
  in 1.2. This needs correcting to either use the real iteration mechanism (if one exists elsewhere
  in the codebase — not investigated here, out of this task's stated scope of *CLI* verification
  unless iteration is itself CLI-flag-driven) or be rewritten to test `--print_impossible` correctly.
- `builder/tests/integration/test_cli_interactive_integration.py` — confirmed: constructs a mock
  flags object with `'interactive': True/False` and asserts on `BuildModule` internals
  (`interactive_manager.mode`, etc.). `interactive` is listed in `settings.py:253`'s
  `standard_args` (a recognized-but-inert key so `_apply_overrides` doesn't warn), and is **not**
  a flag `ParseFileFlags`/argparse can ever set — the real analogous flag is `-q`/`--sequential`
  (`action='store_true'`, "Prompt to save each model individually"). This file tests an internal
  `BuildModule` capability using a flag name the CLI cannot produce; task's instruction is to
  reconcile it with the real flag surface (rewrite using `sequential`, driven via actual
  `ParseFileFlags`-parsed argv) or retire it. Given `general_settings["sequential"]` presumably
  exists as the real key (not directly confirmed in this pass — worth a quick check in planning
  before deciding rewrite vs. retire), the safer default recommendation is: rewrite using the real
  `-q`/`--sequential` flag end-to-end through `ParseFileFlags`, since the underlying
  `BuildModule`/`interactive_manager` behavior it's probing may still be worth covering, just
  through the correct entry point.

## 2. Existing reusable infrastructure

| Component | Location | Status |
|---|---|---|
| `run_cli_command`, `assert_cli_success`, `assert_cli_failure` | `code/tests/utils/helpers.py:14,137,162` | Defined, unused by any test (confirmed: no `import.*run_cli_command` hits outside the file's own definition and the 5 `test_error_handling.py` cases, which is the *only* current consumer — so "unused" in the task description is nearly, not fully, accurate; error-handling tests do use `run_cli_command`, just not `assert_cli_success`/`assert_cli_failure`/`cli_runner`). Runs via `python -m model_checker`, not the real console script. |
| `cli_runner` fixture | `code/tests/conftest.py:166-189` | Defined, zero requesting tests found (confirmed via grep for `cli_runner` usage — only the definition and its own docstring match). Also `python -m model_checker`. |
| `installed_venv` fixture (session-scoped, builds wheel + venv + pip install) | `code/tests/packaging/test_entry_point.py:35-71` | New (task 149 phase 5). Only fixture that invokes the *actual* `model-checker` console script. Module-local, not yet in `tests/packaging/conftest.py` — would need relocating/importing to share with new e2e-style tests, or new tests added directly to `tests/packaging/`. |
| `built_artifacts`, `packaging_toolchain` | `code/tests/packaging/conftest.py:70,113` | Session-scoped wheel/sdist builder with CI-gated skip/fail (`_provisioning_failure`), stale-build-cache clearing (fixed under task 149 per its own commit history — see `55ea4e8f`/`ba2257a6`/`eaa0f4f8` in recent log). |
| `create_temp_project` | `code/tests/utils/helpers.py:302` | Hand-writes a fake project; does not call `BuildProject`. Do not reuse for generate-then-execute (task explicitly flags this). |
| `BuildProject.generate()` | `code/src/model_checker/builder/project.py:171` | Correct non-interactive API; already used once correctly in `tests/e2e/test_project_creation.py`. |
| `registry.get_registered()` | `code/src/model_checker/registry.py:154` | Returns `['bimodal', 'logos', 'exclusion', 'imposition']` live; use to parametrize generate-then-execute rather than hardcoding. |

## 3. Test markers / suite-integration considerations

- `pyproject.toml` registers markers `countermodel`, `theorem`, `performance`, `differential`,
  `slow` ("run in the default suite"), `packaging` ("slower... requires a build toolchain"). No
  marker is excluded by default (`addopts = "--durations=0 -v --import-mode=importlib"` has no
  `-m` deselect), so anything added under `tests/packaging/` or marked `slow` still runs in the
  full-suite baseline (2193/2193) unless a future `-m "not slow"` filter is applied locally.
- `testpaths = ["tests", "src/model_checker"]` — both `code/tests/` and in-package
  `src/model_checker/**/tests/` are collected; new tests can live in either tree depending on
  whether they're package-wide CLI concerns (`code/tests/e2e/` or `code/tests/packaging/`) or
  builder-specific (`code/src/model_checker/builder/tests/e2e/` or `.../integration/`), matching
  the existing split the task description itself uses when citing file paths.
- `code/docs/core/TESTING_GUIDE.md` section 2.1/2.2 documents the standard test-directory/naming
  conventions this repo expects (`tests/unit/`, `tests/integration/`, file names `test_*.py`,
  classes `Test*`) — any new/rewritten files should follow this, and section 8.6
  ("Solver Timing Budgets and Machine Variance") plus 8.8 ("Oracle Suite: Gating vs. Exhaustive
  Split") are relevant precedent for how this repo already handles "some tests are expensive,
  keep them but budget them sensibly" — worth reading in full during planning for phrasing
  runtime-budget constraints on the new console-script/generate-then-execute tests (a full venv
  build + per-theory execution sweep is not free).

## 4. Sequencing / dependency note

Task 148 depends on task 146 ("CLI defects," now COMPLETED per delegation context and the recent
commit `55ea4e8f task 146: complete implementation`). The current CLI behavior on disk already
reflects that completed fix work, so building tests against current `__main__.py`/`settings.py`
behavior (as inspected in this report) is safe and not encoding pre-fix bugs — no further
verification of task 146's landed state was needed beyond confirming its commit exists in the log.

## 5. Recommendations for planning

1. Treat (a) as **augment, don't rebuild**: extend `test_entry_point.py`'s pattern (or relocate
   `installed_venv` into `tests/packaging/conftest.py` so other files can reuse it) rather than
   inventing a second venv-based harness.
2. For (b), write the short/long equivalence sweep as a single parametrized test iterating
   `ParseFileFlags()._short_to_long.items()`, asserting `SettingsManager`-merged settings equality
   for `-x` vs `--long-name` — this is the direct regression guard for the class of defect that
   caused the `-p` bug, and doubles as the fix for `test_conflicting_flags`'s empty `pass` stub if
   the mutex `--z3`/`--cvc5` case is folded in alongside it (`argparse` raises `SystemExit(2)` for
   simultaneous `--z3 --cvc5`, easily asserted via subprocess non-zero exit + stderr content).
3. For (c), the bulk of the ~15-flag matrix can run via `python -m model_checker` (fast, no venv
   build) since flag-parsing/settings-override behavior is identical regardless of entry point;
   reserve the real installed-console-script subprocess for the smaller set of checks that are
   specifically about the entry point itself (`--version`, `--help`, and ideally at least one full
   generate-then-execute pass) to keep runtime reasonable.
4. For (d), parametrize over `registry.get_registered()`, use small `N` where the semantics allow
   it (check each theory's default `N` isn't already tiny) to bound runtime, assert exit 0 + no
   `Traceback` in stderr + output line count in a loose sanity range (not exact-matching the
   review's 1099/188/95/770 figures) rather than pinning exact output.
5. For the four misleading/dead files (1.6), plan explicit per-file dispositions: delete
   `test_pythonpath_setup_in_subprocess`; rewrite `test_batch_output_real.py` to actually assert
   batch-specific behavior (multiple examples/`--save` output) or rename it down to what it tests;
   fix `test_iteration_workflow`'s flag misunderstanding; and reconcile or retire
   `test_cli_interactive_integration.py` against the real `-q`/`--sequential` flag.
6. Confirm during planning (not yet checked here) whether `general_settings["sequential"]` is the
   actual settings-dict key populated by `-q`, to decide the safest rewrite target for
   `test_cli_interactive_integration.py`.

## Files referenced (absolute paths)

- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/__main__.py`
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/settings/settings.py`
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/registry.py`
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/solver/registry.py`
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/builder/project.py`
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/builder/comparison.py`
- `/home/benjamin/Projects/ModelChecker/code/tests/packaging/test_entry_point.py`
- `/home/benjamin/Projects/ModelChecker/code/tests/packaging/conftest.py`
- `/home/benjamin/Projects/ModelChecker/code/tests/utils/helpers.py`
- `/home/benjamin/Projects/ModelChecker/code/tests/conftest.py`
- `/home/benjamin/Projects/ModelChecker/code/tests/integration/test_error_handling.py`
- `/home/benjamin/Projects/ModelChecker/code/tests/e2e/test_project_creation.py`
- `/home/benjamin/Projects/ModelChecker/code/tests/e2e/test_batch_output_real.py`
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/builder/tests/test_package_loading.py`
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/builder/tests/test_issue_73_fix.py`
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/builder/tests/e2e/test_full_pipeline.py`
- `/home/benjamin/Projects/ModelChecker/code/src/model_checker/builder/tests/integration/test_cli_interactive_integration.py`
- `/home/benjamin/Projects/ModelChecker/code/pyproject.toml`
- `/home/benjamin/Projects/ModelChecker/code/docs/core/TESTING_GUIDE.md`
