# Implementation Plan: CLI End-to-End Verification Suite

- **Task**: 148 - cli_end_to_end_verification_suite
- **Status**: [COMPLETED]
- **Effort**: 10 hours
- **Dependencies**: 146 (CLI defects — COMPLETED, landed at `55ea4e8f`)
- **Research Inputs**: `specs/148_cli_end_to_end_verification_suite/reports/01_cli-e2e-verification-research.md`
- **Artifacts**: plans/01_cli-e2e-verification-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

The CLI has effectively zero behavioral test coverage: the console script is never invoked,
`ParseFileFlags` is never imported by a test, and the primary "generate a project then run it"
journey is untested. This plan builds that coverage in a new `code/tests/cli/` package (fast
`python -m model_checker` invocations for the flag matrix and parser unit tests) plus a small set
of real-console-script tests layered onto the existing wheel-build-and-venv-install fixture in
`code/tests/packaging/`, then reconciles or retires four existing files that are named like
end-to-end coverage but are not. Definition of done: every flag in the registered flag table is
exercised, short and long spellings are proven equivalent for every entry in `_short_to_long`,
all registry-registered theories survive generate-then-execute through the real console script,
and the full suite is green with no test asserting against its own mock.

### TDD Direction (read this before writing any test)

This task's deliverable IS the tests; the production code under test already exists and is
presumed correct following task 146. The RED/GREEN discipline therefore inverts relative to a
feature task, and the inversion must be respected literally:

1. Write the assertion that encodes the **intended** behavior, derived from reading
   `__main__.py` / `settings.py` / `module.py`, never from running the code and transcribing
   whatever it printed.
2. Run it. A pass validates existing behavior. A failure is a **genuine newly-discovered
   defect**.
3. **On failure, do NOT weaken the test to make it pass.** Report the defect in the phase notes,
   and either fix the production code (if it is a clear, small, in-scope defect of the kind task
   146 addressed) or record it and leave the test failing with an explicit `pytest.mark.xfail`
   carrying a reason string naming the defect. Silently relaxing an assertion to green
   reintroduces exactly the blindness this task exists to remove.

### Research Integration

The research report was verified against the current tree and its findings are adopted wholesale.
Load-bearing points carried into this plan:

- **Gap (a) is already half-closed.** `code/tests/packaging/test_entry_point.py` (added by task
  149) builds a wheel, installs into a fresh venv, and runs the real `model-checker` script for a
  liveness check. Its own docstring reserves "broader console-script behavior coverage" for
  elsewhere. This plan **extends that fixture, it does not build a second venv harness.**
- **The `-p` regression mechanism is `settings.py:202-274`.** "Was this flag user-provided" is
  decided by re-scanning raw `sys.argv` tokens on `flags._parsed_args`, with short tokens
  recognized only when `len(arg) == 2`, then mapped through `_short_to_long`. A bad mapping entry
  produces a **silent no-op** (setting keeps its default), never a crash — which is why the defect
  shipped. The short/long equivalence sweep in Phase 3 targets this mechanism directly.
- **Clustered short flags (`-cn`) are a documented, deliberate non-feature**, not a bug
  (comment at `settings.py:214-220`). Tests must assert the documented behavior (no override),
  not the intuitive one.
- **`registry.get_registered()` returns 4 theories live**; parametrize off it, never hardcode.
- **The cvc5-missing `ImportError` path is exercisable in this environment** (cvc5 not
  installed) and returns cleanly with exit 0 after printing two lines — it is not a crash path.
- Runtime cost: the `installed_venv` fixture is session-scoped and already paid once. Additional
  console-script subprocess calls against it are cheap; additional *venv builds* are not.

### Two open questions from the research, now resolved

Both were flagged in the research as needing confirmation during planning. Both were checked and
one **materially changes the recommended disposition** of a file:

1. **`general_settings["sequential"]` exists** — confirmed at
   `code/src/model_checker/models/semantic.py:83`, inside `DEFAULT_GENERAL_SETTINGS`. The
   research's precondition for rewriting `test_cli_interactive_integration.py` holds.
2. **But `-q`/`--sequential` is a hard fail-fast path, not a working feature.**
   `code/src/model_checker/builder/module.py:140-152` raises `NotImplementedError` whenever
   `config.sequential` is truthy, because `SequentialSaveManager`/`ConsoleInputProvider` were
   deliberately deleted and are not being restored. `__main__.py:294-297` catches that and exits
   1 with `Error: {e}`. Therefore the correct rewrite target for
   `test_cli_interactive_integration.py` is **the fail-fast contract**, not an
   `interactive_manager.mode` behavior: `prompt_manager` is unconditionally `None`, so the
   internals that file asserts against cannot exist. See Phase 7 for the resulting disposition.

### A third defect found during planning (not in the research)

`code/tests/e2e/test_batch_output_real.py` is worse than the research described. Its comment says
`# Use -l for load_theory (correct flag)` but **the subprocess call it precedes passes no `-l` at
all** — just the example path. Separately, `-l` could not be used that way regardless: at
`__main__.py:290-293`, `--load_theory` dispatches to `BuildProject(...).ask_generate()` and
returns, so it never runs an example file and it blocks on `input()`. The flag matrix in Phase 4
must not invoke `-l` as a bare non-interactive subprocess, and Phase 7 must correct this
comment as well as the missing batch assertions.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found; no roadmap phases included.

### Scope note: two files touched outside the declared `file_scope`

`file_scope` is prospective and descriptive, not a hard boundary. Two additions outside it are
required and are justified here rather than worked around:

- `code/tests/packaging/conftest.py` — receives the relocated `installed_venv` fixture (Phase 2).
  Relocation is mandatory because pytest fixture visibility is directory-scoped: a fixture that
  stays module-local in `test_entry_point.py` cannot be shared, and duplicating it would create
  the second divergent venv harness the research warns against.
- `code/tests/packaging/test_cli_console_script.py` — new (Phase 5). Console-script tests must
  live in the same directory as the fixture for the same visibility reason; they cannot live in
  `code/tests/cli/`.

`code/tests/packaging/test_entry_point.py` is edited only to drop the moved fixture definition and
its now-shared helpers; its three existing tests are unchanged.

## Goals & Non-Goals

**Goals**:
- Exercise the real installed `model-checker` console script for behavior, not just liveness.
- Unit-test `ParseFileFlags.parse()`, its short/long mapping, and the flag-to-settings override
  path, with a per-flag short/long equivalence sweep as the `-p`-class regression guard.
- Cover every flag in the registered table through the CLI, including `--save` producing real
  files on disk and the cvc5-missing `ImportError` path.
- Automate generate-then-execute for every theory in `registry.get_registered()`.
- Assert `--upgrade`'s constructed command without ever executing it.
- Leave zero tests that assert against their own mock, and zero test names that overstate what
  the test does.

**Non-Goals**:
- Fixing CLI defects. That was task 146. A defect newly surfaced here is reported and either
  fixed if small and unambiguous, or recorded as an `xfail` with a reason — never papered over.
- Restoring sequential/interactive save. It was deliberately removed; this task tests that the
  removal fails fast and clearly.
- Executing `--upgrade`, or any network/pip-mutating operation.
- Pinning exact output line counts. The review's 1099/188/95/770 figures are used as a loose
  sanity floor, not as equality assertions.
- Adding a second wheel-build or venv-install harness.
- Restructuring the `tests/` tree beyond adding `tests/cli/`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Suite runtime inflates unacceptably (venv build + 4-theory sweep + `-m` process pool) | H | H | Confine real-console-script use to Phase 5/6 only; run the whole ~15-flag matrix through `python -m` (Phase 4). Keep `N` minimal in every fixture example. Mark the expensive files `packaging`/`slow`. Record per-file timings in Phase 8 against a stated budget. |
| A new test surfaces a real defect and gets weakened to green | H | M | The "TDD Direction" section above is a standing instruction; Phase 8 explicitly re-reads every added assertion for weakening, and any `xfail` must carry a reason string naming the defect. |
| `--maximize` forks a `ProcessPoolExecutor` and hangs or times out in CI | M | M | Use the smallest possible example (single example, `N: 2`, two trivially-distinguishable theories) and set an explicit subprocess `timeout`; assert on `run_comparison` dispatch, not on comparison depth. |
| Deleting/rewriting the four misleading files removes coverage that was uniquely theirs | M | L | Phase 7 depends on Phases 3, 4, and 6 so replacement coverage exists first; each disposition is recorded with the specific new test that subsumes it. |
| Relocating `installed_venv` breaks the three existing `test_entry_point.py` tests | M | L | `interface` tier on Phase 2: run the whole `tests/packaging/` directory immediately after the move, before anything depends on it. |
| Generated projects are documented as "cannot be loaded standalone" (`test_generated_projects.py:88`) and the journey genuinely does not work | H | M | Phase 6 begins with a manual single-theory spike before parametrizing. If the journey is genuinely broken, that is a real defect: record it as `xfail` with the failure mode and report it, rather than downgrading the assertion to something the broken path can satisfy. |
| `cvc5` becomes installed in some environment, silently skipping the ImportError path | L | M | Assert the branch conditionally on cvc5 import availability, and make the "cvc5 present" arm assert the success dispatch — so neither environment yields a vacuous pass. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3, 4, 5 | 1, 2 |
| 3 | 6 | 2, 5 |
| 4 | 7 | 3, 4, 6 |
| 5 | 8 | 7 |

Phases within the same wave can execute in parallel. Phases 3 and 4 are blocked by Phase 1 only;
Phase 5 is blocked by Phase 2 only.

---

### Phase 1: CLI test package scaffolding and harness adoption [COMPLETED]

**Goal**: Create `code/tests/cli/` and make the existing-but-unused CLI harness actually usable,
so Phases 3 and 4 have somewhere to write and something to write with.

**Tasks**:
- [x] Create `code/tests/cli/__init__.py` and `code/tests/cli/conftest.py`.
- [x] Read `code/tests/utils/helpers.py` (`run_cli_command` at :14, `assert_cli_success` at :138,
      `assert_cli_failure` at :162) and `code/tests/conftest.py`'s `cli_runner` fixture at :166.
      Confirm each works as written by exercising it once; fix any defect found (these have never
      been executed by `assert_cli_success`/`assert_cli_failure`/`cli_runner` consumers).
- [x] Add a `timeout` default and an explicit `cwd`/`tmp_path` story to the harness if the
      existing signature cannot support running against a file in a temp dir — `run_cli_command`
      currently hardcodes `cwd=<project root>`, which the `--save` test in Phase 4 needs to vary.
- [x] Add a minimal shared fixture producing a tiny valid example module (single example,
      `semantic_theories` + `example_range`, `{"N": 2}`) in a `tmp_path`, modeled on the module
      format in `code/tests/e2e/test_batch_output_real.py`.
- [x] Confirm `code/tests/cli/` is collected: `testpaths` already includes `tests`, so no
      `pyproject.toml` change should be needed. Verify rather than assume.

**Timing**: 0.75 hours

**Depends on**: none

**Verification Tier**: local

**Files to modify**:
- `code/tests/cli/__init__.py` - new, empty package marker
- `code/tests/cli/conftest.py` - new, tiny-example fixture
- `code/tests/utils/helpers.py` - fix/extend `run_cli_command` and the two assert helpers
- `code/tests/conftest.py` - fix `cli_runner` if broken

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/cli/ -v` collects (zero tests is acceptable at this
  phase; a collection error is not).
- `PYTHONPATH=code/src pytest code/tests/ -v` still green — the helper edits must not disturb
  `test_error_handling.py`, the one current `run_cli_command` consumer.

**Implementation Notes**:
- `run_cli_command` already has more live consumers than the plan assumed:
  `tests/integration/test_error_handling.py`, `tests/integration/test_timeout_resources.py`,
  `tests/unit/test_main_cli.py`, `tests/e2e/test_project_creation.py`, and
  `tests/utils/base.py::BaseCLITest`. Extended its signature (`timeout` now defaults to 30,
  added `cwd`/`input`) without breaking any of them — reran all five files green.
- Genuine defect found and fixed per the TDD Direction: `cli_runner` (`tests/conftest.py`) had
  never been exercised by a consumer and was broken -- it changes `cwd` to the project root but
  relies on an inherited, possibly-*relative* `PYTHONPATH` env var (the project's own
  `PYTHONPATH=code/src pytest ...` convention), which Python resolves against the *subprocess's*
  cwd at import time, not the invoking shell's cwd. Confirmed directly: with `cwd` changed and
  `PYTHONPATH=code/src` inherited unmodified, the subprocess raised
  `No module named model_checker`. Fixed by injecting an absolute `src/` path into `PYTHONPATH`
  explicitly, matching `run_cli_command`'s existing approach, plus adding `timeout`/`cwd`/`input`
  parameters for parity.
- `assert_cli_success`/`assert_cli_failure` (module-level, `tests/utils/helpers.py`) did not
  accept `**kwargs`, while `BaseCLITest.assert_cli_success`/`assert_cli_failure`
  (`tests/utils/base.py`, currently unused outside `tests/README.md`'s example) already forward
  `**kwargs` to them — a latent `TypeError` waiting for the first caller to pass e.g. `cwd`. Fixed
  by accepting and forwarding `**run_kwargs`.
- `code/tests/unit/test_main_cli.py` (added by task 146, landed at `694d7411`) already imports
  `ParseFileFlags` and covers short/long equivalence for `-p` alone, `--sequential`'s clean-exit
  path, `--load_theory` registry-derived choices, and the `_short_to_long` completeness check
  against registered short options. This corrects the research/plan's "never imported" premise;
  noted here so Phase 3 builds complementary (all-14-flags sweep, argparse structure, standard_args,
  clustered-flag gap, the `test_conflicting_flags` stub) coverage rather than duplicating it.

---

### Phase 2: Relocate `installed_venv` into the packaging conftest [COMPLETED]

**Goal**: Make the real-console-script fixture shareable without building a second venv.

**Tasks**:
- [x] Move `installed_venv` (session-scoped) from `code/tests/packaging/test_entry_point.py` into
      `code/tests/packaging/conftest.py`, alongside the existing `packaging_toolchain` and
      `built_artifacts`.
- [x] Move the supporting helpers `_venv_bin_dir` and `_console_script_path` into the conftest
      too; `_provisioning_failure` already exists in the conftest — reuse that copy and delete
      the duplicate in `test_entry_point.py` rather than keeping two.
- [x] Preserve the `PYTHONPATH`-stripping behavior verbatim, including its explanatory comment.
      That comment documents a real, already-hit failure mode: an inherited `PYTHONPATH=src`
      makes pip see `model_checker` as satisfied and skip installing the wheel, silently leaving
      the console script uninstalled.
- [x] Expose `_console_script_path` as a usable fixture or importable helper for Phases 5 and 6.
- [x] Leave the three existing tests in `test_entry_point.py` semantically unchanged.

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: interface

**Files to modify**:
- `code/tests/packaging/conftest.py` - receives `installed_venv`, `_venv_bin_dir`,
  `_console_script_path`
- `code/tests/packaging/test_entry_point.py` - fixture and duplicate-helper definitions removed;
  tests unchanged

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/packaging/ -v` green, with the same test count as before
  the move.
- Confirm the venv is built exactly once for the directory (session scope preserved), e.g. via
  `--durations=0` showing a single expensive setup.

---

### Phase 3: `ParseFileFlags` unit tests and the short/long equivalence sweep [COMPLETED]

**Goal**: Cover the parser class that no test has ever imported, and install the direct
regression guard for the `-p` class of silent-no-op defect.

**Tasks**:
- [x] New `code/tests/cli/test_parse_file_flags.py`. Import `ParseFileFlags` from
      `model_checker.__main__` — the first test in the repo to do so. (Correction: as noted in
      Phase 1's Implementation Notes, `tests/unit/test_main_cli.py` already did this; this file
      is complementary, not first.)
- [x] Test `_create_parser()` structure: `-l/--load_theory` choices come from
      `registry.get_registered()`; `--z3`/`--cvc5` form a mutually exclusive group with no short
      forms; `-s/--save` is `nargs='*'` with `choices=['markdown','json']`.
- [x] Test `parse()` stamps `_short_to_long` and `_parsed_args` (`= sys.argv[1:]`) onto the
      returned Namespace. Drive via `monkeypatch.setattr(sys, "argv", [...])`, since `parse()`
      reads `sys.argv` directly rather than accepting an argv argument.
- [x] **Short/long equivalence sweep** (the core regression guard): parametrize over the
      generic-sweep subset of `_short_to_long.items()`. For each `(short, long)` pair, run a full
      `parse()` + `SettingsManager` merge for `-x` and separately for `--long_name`, and assert
      the resulting merged settings dicts are equal. Exclude the pairs whose flags exit the
      process (`v`/`version`) or take a required value (`l`/`load_theory`), and handle
      `s`/`save` (`nargs='*'`) and `u`/`upgrade` (no settings key) explicitly rather than by
      silently skipping them — an unexplained skip would hide exactly the mapping bug this sweep
      exists to catch.
- [x] Assert the sweep's own completeness: the number of pairs actually asserted plus the number
      explicitly excluded equals `len(_short_to_long)`. Without this, adding a 15th flag would
      silently go uncovered.
- [x] Test the `settings.py` override mechanism directly: a flag present in
      `_parsed_args` overrides the merged setting; a flag absent leaves the default; a flag whose
      argparse attribute is set but which is *not* in `_parsed_args` does **not** override (this
      is the silent-no-op mechanism).
- [x] Test the documented clustered-short-flag gap: `-cn` parses successfully in argparse but
      does **not** override either setting, because `len('-cn') != 2`. Assert the documented
      behavior with a comment pointing at the relevant `settings.py` comment, so a future reader
      sees this is intentional, not a latent bug the test enshrined by accident. **Correction
      found while writing this test**: the actual mechanism is stronger than "leaves the
      default" — because `_apply_overrides`'s `key in merged_settings` / `elif key in
      DEFAULT_EXAMPLE_SETTINGS` branches are both nested inside `if is_mock or key in
      user_provided_flags`, an unrecognized clustered token doesn't just skip overriding, it
      means the key is **never added to `merged_settings` at all** when it wasn't already
      present (e.g. `contingent`/`non_null`, which only live in `DEFAULT_EXAMPLE_SETTINGS`, not
      the base general settings). The test asserts `'contingent' not in settings` rather than
      `settings['contingent'] is False`, matching the real behavior exactly.
- [x] Test `standard_args` produce no "unknown flag" warning.
- [x] Fill the empty `pass` stub at `code/tests/integration/test_error_handling.py:69`
      (`test_conflicting_flags`) with the real `--z3 --cvc5` mutex assertion: argparse exits
      `SystemExit(2)` with the mutex message on stderr.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: `_short_to_long` is asserted to have 14 entries
(`c,d,e,l,m,n,p,q,s,i,v,u,z,a`, read from `__main__.py:208-223`). Confirm at implementation time
by asserting `len(...)` in the completeness check rather than hardcoding 14 in prose — if the
count differs, the completeness assertion fails loudly instead of the sweep silently covering a
subset.

**Files to modify**:
- `code/tests/cli/test_parse_file_flags.py` - new
- `code/tests/integration/test_error_handling.py` - replace the `pass` stub at :69

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/cli/test_parse_file_flags.py -v` green.
- `PYTHONPATH=code/src pytest code/tests/integration/test_error_handling.py -v` green with 6 real
  tests and zero `pass` bodies.
- `grep -n "pass$" code/tests/integration/test_error_handling.py` returns no stub test body.

---

### Phase 4: Flag matrix through `python -m model_checker` [COMPLETED]

**Goal**: Exercise every flag in the registered table at CLI level, fast, without a venv build.

**Tasks**:
- [x] New `code/tests/cli/test_flag_matrix.py`, using the Phase 1 harness and tiny-example
      fixture.
- [x] `--version`/`-v`: exit 0, non-empty stdout containing a version-shaped string.
- [x] `--help`/`-h`: exit 0, stdout lists every long flag in the registered table. Assert
      coverage by iterating the parser's own actions, so a newly added flag missing from help is
      caught.
- [x] Boolean flags — `--contingent/-c`, `--non_null/-n`, `--non_empty/-e`, `--disjoint/-d`,
      `--print_constraints/-p`, `--print_z3/-z`, `--print_impossible/-i`, `--align_vertically/-a`
      — each in both spellings against the tiny example: exit 0 and no `Traceback` in stderr.
      For the three flags with observable output effects (`-p`, `-z`, `-i`), additionally assert
      the output differs from the no-flag baseline run, so the test is not merely asserting the
      flag is accepted.
- [x] `--save/-s`: run in a `tmp_path` cwd and assert output files are actually produced on disk.
      Cover all three states distinctly — flag absent (nothing saved), `-s` with zero args (the
      `nargs='*'` "save both" case), and `-s markdown` / `-s json`.
- [x] `--maximize/-m`: assert dispatch to `module.comparison.run_comparison()`. Use the smallest
      viable comparison example and an explicit subprocess timeout; this path forks a
      `ProcessPoolExecutor`.
- [x] `--z3`: exit 0, backend selected. `--cvc5`: assert the missing-dependency path — prints
      `Error: ...` plus the `pip install cvc5` hint and returns cleanly with **exit 0, not a
      crash**. Guard on cvc5 import availability and give the cvc5-present arm its own success
      assertion, so neither environment passes vacuously.
- [x] `--upgrade/-u`: **unit test with `unittest.mock.patch('subprocess.run')`. Never execute.**
      Assert the constructed argv is exactly
      `[sys.executable, '-m', 'pip', 'install', '--upgrade', package_name]` and that `check=True`
      is passed.
- [x] `--sequential/-q`: assert the fail-fast contract — `NotImplementedError` is raised, caught
      at `__main__.py`, printed as `Error: ...`, and the process exits 1. This is the correct
      current behavior, not a defect.
- [x] Do **not** invoke `-l/--load_theory` as a bare subprocess: it dispatches to
      `BuildProject.ask_generate()` and blocks on `input()`. Its non-interactive coverage belongs
      to Phase 6.

**Implementation Notes -- two genuine defects surfaced, handled per the TDD Direction**:
- **Fixed (small, unambiguous, in-scope): `--cvc5` crashed on every invocation with a raw
  Python traceback, exit 1** (`AttributeError: module 'cvc5.pythonic' has no attribute
  'reset_params'`). `builder/runner.py`'s `_initialize_z3_context` called `z3.reset_params()`/
  `z3.set_param(verbose=0)` unconditionally through the `z3_shim`, but `cvc5.pythonic` (the
  actual backend module cvc5 selection forwards to) implements neither function -- confirmed
  directly (`'reset_params' in dir(cvc5.pythonic)` is `False`, same for `set_param`). This
  crashed *every* `--cvc5` run in an environment where cvc5 is installed, before any solving
  began, contradicting the research/plan's premise that "the cvc5-missing `ImportError` path is
  exercisable in this environment (cvc5 not installed)" -- cvc5 **is** installed here
  (`pip show cvc5` reports version 1.3.3). Fixed by guarding both calls behind
  `get_active_backend() == "z3"` in `builder/runner.py`; single call site, no other code paths
  affected (verified: `code/src/model_checker/builder/`, `code/src/model_checker/solver/`, and
  the full `code/tests/` suite all still green after the fix).
- **Recorded, not fixed (theory-specific, out of scope): bimodal cannot complete a solve under
  `--cvc5`** -- after the fix above, `--cvc5` against a bimodal example still crashes, one level
  deeper, with `AttributeError: module 'cvc5.pythonic' has no attribute 'MultiPattern'`
  (`theory_lib/bimodal/semantic/core.py`'s `build_forward_comp_constraint` calls
  `z3.MultiPattern` directly via the shim). This is a real, theory-specific gap in cvc5.pythonic
  API coverage, not a CLI-flag defect, and fixing it would mean extending the cvc5 compatibility
  shim or bimodal's constraint-building code -- both well outside this task's `--cvc5`
  flag-dispatch scope. `logos` was confirmed to complete successfully under `--cvc5` in this
  same environment (exit 0, real solve, correct output), so `test_cvc5_flag` in
  `test_flag_matrix.py` uses logos for its cvc5-present success assertion rather than the shared
  bimodal `tiny_example_file` fixture, with a comment naming the gap. This finding should be
  reported as a follow-up rather than left implicit.
- Also discovered while prototyping the `--maximize` test (no fix needed, test-design-only):
  `builder/comparison.py`'s `ModelComparison`/`_find_max_N_static` path builds
  `semantics_class(settings)` directly from the raw example-case settings dict, bypassing
  `SettingsManager`'s merge with the theory's `DEFAULT_EXAMPLE_SETTINGS` entirely (unlike the
  normal single-run path through `BuildExample`, which does merge). A comparison example
  supplying only `{"N": 2, "max_time": ...}` therefore fails per-theory with `KeyError`s for any
  setting the theory itself doesn't default in the caller's dict (e.g. bimodal's `M`,
  `contingent`). `test_maximize_dispatches_to_run_comparison`'s fixture instead seeds a complete
  settings dict from `theory["semantics"].DEFAULT_EXAMPLE_SETTINGS` before overriding `N`/
  `max_time`, matching the pattern `tests/utils/helpers.py::create_test_model` already uses for
  the same reason.

**Timing**: 2 hours

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: this phase asserts a ~15-flag table drawn from `__main__.py:19-237`. Confirm
at implementation time by enumerating the parser's registered actions programmatically and
asserting every one is either covered by a test in this file or on an explicit, commented
exclusion list — do not hand-transcribe the flag list.

**Files to modify**:
- `code/tests/cli/test_flag_matrix.py` - new
- `code/tests/cli/conftest.py` - extend fixtures as the matrix requires

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/cli/test_flag_matrix.py -v` green.
- The programmatic flag-coverage assertion passes, proving no registered flag is unexercised and
  unexcluded.
- `--durations=0` for this file stays within the Phase 8 budget.

---

### Phase 5: Console-script behavioral coverage [COMPLETED]

**Goal**: Cover the real `[project.scripts]` entry point for behavior, beyond the existing
liveness check, without a second venv.

**Tasks**:
- [x] New `code/tests/packaging/test_cli_console_script.py`, marked
      `pytest.mark.packaging`/`pytest.mark.slow`, consuming the relocated `installed_venv` and
      `_console_script_path`.
- [x] `model-checker --version` and `model-checker --help` invoked as the real script: exit 0,
      and stdout matching what the equivalent `python -m model_checker` invocation produces. The
      cross-check is the point — it proves the entry point resolves to the same `run()` rather
      than merely that it exits 0.
- [x] One real example run through the console script against a tiny example file: exit 0, no
      `Traceback` in stderr, non-empty stdout.
- [x] Invoke with **no `PYTHONPATH`** (the fixture already strips it), proving the installed
      package is self-sufficient — this is the property the deleted mock test only pretended to
      check.
- [x] Add a docstring stating this file owns broader console-script behavior, closing the
      forward reference in `test_entry_point.py`'s docstring (already updated during Phase 2's
      edit, since that file's fixture-relocation and docstring pointer are the same edit site).

**Implementation Notes -- environment-specific failure mode discovered, handled loudly**:
- The two tests that actually run a solve through the installed venv's console script
  (`test_real_example_run_through_console_script`,
  `test_console_script_runs_without_pythonpath`) hit a real failure the first time they ran:
  `z3.z3types.Z3Exception: libz3.so not found`, from
  `[OSError('libstdc++.so.6: cannot open shared object file...'), ...]`. Root cause confirmed:
  on this project's NixOS development host, the *ambient* interpreter's `z3` package resolves
  through the Nix store with correctly wired RPATHs, but the isolated packaging-test venv
  installs `z3-solver` fresh from PyPI, and that wheel's bundled shared libraries expect an
  FHS-standard library search path that Nix's non-FHS layout does not provide outside of
  `nix-ld`-patched binaries (which pip-installed wheels are not). This is an isolated-venv
  dynamic-linking limitation of this specific dev machine, not a `model_checker` code defect --
  a standard (non-Nix) Linux CI runner would not be expected to hit it.
- Handled with a new `handle_known_venv_libz3_link_failure()` helper in `conftest.py`, reusing
  the exact CI-gated skip/fail shape `_provisioning_failure` already established for
  toolchain/wheel-build provisioning: skip outside CI (loud reason, not a silent pass), fail
  loudly in CI. It recognizes only this one exact failure signature in the subprocess output and
  is a no-op for anything else, so it can never mask a real defect. Exposed for reuse by Phase 6,
  which will hit the identical signature for every theory's generate-then-execute run in this
  same environment.
- Result: 2 of 4 tests in this file pass outright (`--version`/`--help`, which never import z3);
  the other 2 skip with the loud reason above in this environment. Recorded here rather than
  silently accepted, per the "never a silent pass" standing policy this file inherits from
  `conftest.py`.

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: local

**Files to modify**:
- `code/tests/packaging/test_cli_console_script.py` - new
- `code/tests/packaging/test_entry_point.py` - correct the forward pointer in its docstring

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/packaging/ -v` green.
- Still exactly one venv build for the directory.
- The console-script and `python -m` outputs for `--version`/`--help` are asserted equal.

---

### Phase 6: Generate-then-execute, per registered theory [COMPLETED]

**Goal**: Automate the primary user journey the review verified by hand, driven off the registry.

**Tasks**:
- [x] **Spike first, parametrize second.** Manually ran bimodal end-to-end
      (`BuildProject('bimodal').generate('spike_test', tmp_dir)`, then the generated
      `examples.py` through `python -m model_checker`) before writing the parametrized test.
      **Finding**: the journey works. `test_generated_projects.py:88`'s "cannot be loaded
      standalone" note describes a narrower, different scenario (a hand-built `MockFlags` with
      only `file_path` set, bypassing package detection) -- the real CLI path detects the
      `.modelchecker` marker `BuildProject.generate()` writes and routes through
      `strategies.py`'s `PackageImportStrategy`, which resolves the generated project's relative
      imports correctly. Confirmed with a full, correct countermodel output and zero Tracebacks.
- [x] If the journey is genuinely broken, that is a **real defect**... (N/A -- not broken; see
      finding above).
- [x] New `code/tests/packaging/test_generate_then_execute.py`, parametrized
      `@pytest.mark.parametrize("theory_name", registry.get_registered())` — **never a hardcoded
      theory list**.
- [x] Per theory: generate via `BuildProject.generate()` (the non-interactive API — **not**
      `ask_generate()`, and **not** `tests/utils/helpers.py::create_temp_project`, which
      hand-writes a fake project and never calls `BuildProject`), then run the generated
      `examples.py` through the real console script.
- [x] Assert exit 0, **no `Traceback` in stdout or stderr**, and output length above a loose
      sanity floor (20 lines -- confirmed well under all four theories' real output: bimodal 779,
      logos 1201, exclusion 191, imposition 95 lines, matching the review's figures closely).
      **Do not assert equality**; output length drifts with unrelated formatting changes.
- [x] Assert the parametrization is non-empty, so an empty registry cannot silently produce a
      zero-test vacuous pass.

**Implementation Notes**:
- Extra ambient-interpreter verification beyond the required single-theory spike: manually ran
  generate-then-execute for **all four** registered theories (not just the spike theory) via
  `python -m model_checker` (same `model_checker.__main__:run` entry point the console script
  uses) to build confidence independent of this environment's venv-specific libz3 issue (see
  Phase 5's notes). All four produced correct, complete output with zero Tracebacks: bimodal 779
  lines (~100s -- genuinely slow, not a bug: it runs bimodal's full default example set),
  logos 1201 lines, exclusion 191 lines, imposition 95 lines. Set the per-invocation subprocess
  `timeout=180` (up from an initial 120) to give comfortable margin over bimodal's confirmed
  ~100s runtime plus venv-subprocess overhead.
- As anticipated from Phase 5: all four parametrized `test_generate_then_execute[theory]` cases
  skip in this environment via `handle_known_venv_libz3_link_failure` (same NixOS isolated-venv
  libz3/libstdc++ dynamic-linking limitation, not a CLI or generate-then-execute defect) -- the
  parametrization itself is verified to run exactly once per live registry entry (4), and the
  non-empty/no-Traceback/output-floor assertions are exercised structurally even though the
  z3-dependent solve is skipped in this specific dev environment.

**Timing**: 1.5 hours

**Depends on**: 2, 5

**Verification Tier**: local

**Scope Hypothesis**: `registry.get_registered()` is expected to return 4 theories
(`bimodal, logos, exclusion, imposition`). Confirm at implementation time via the non-empty
assertion and by checking the parametrized test count matches `len(registry.get_registered())` —
never by hardcoding 4.

**Files to modify**:
- `code/tests/packaging/test_generate_then_execute.py` - new

**Verification**:
- `PYTHONPATH=code/src pytest code/tests/packaging/test_generate_then_execute.py -v` green (or
  green with documented, reason-carrying `xfail`s).
- Test count equals the live registry length.
- Runtime recorded for the Phase 8 budget.

---

### Phase 7: Reconcile or retire the misleading existing files [COMPLETED]

**Goal**: Remove every test that asserts against its own mock, and every test name that
overstates what the test does. Runs last among the coverage phases so replacement coverage
already exists.

**Tasks**:
- [x] **`builder/tests/test_package_loading.py::TestSubprocessExecution::test_pythonpath_setup_in_subprocess`
      (~:244-289): delete.** It `@patch`es `subprocess.run` and then asserts against
      `mock_run.call_args` — no production code executes. Phase 5's no-`PYTHONPATH` console-script
      test covers the real question it pretended to. Remove the enclosing `TestSubprocessExecution`
      class if it becomes empty, and drop any now-unused imports.
- [x] **`code/tests/e2e/test_batch_output_real.py`: rewrite.** Add the batch-output assertions its
      name promises (multiple examples and/or `--save` output actually landing on disk), not just
      `returncode == 0`. **Also correct the false comment** `# Use -l for load_theory (correct
      flag)` — the call passes no `-l`, and `-l` would dispatch to `ask_generate()` and block on
      `input()` rather than run the file. If the batch assertions end up fully duplicating Phase
      4's `--save` coverage, retire the file instead and record that in the phase notes.
- [x] **`builder/tests/e2e/test_full_pipeline.py::test_iteration_workflow` (~:89): rewrite.** It
      passes `-i` believing it requests N iterations and feeds `input="2\n\n"`; `-i` is
      `--print_impossible`, a `store_true` boolean, and the stdin is consumed by nothing. Rewrite
      it to test `--print_impossible` honestly and rename it accordingly, dropping the unused
      stdin. Do not invent an iteration flag — no CLI iteration mechanism exists in the
      registered table.
- [x] **`builder/tests/integration/test_cli_interactive_integration.py`: retire, or rewrite to the
      fail-fast contract.** It constructs a mock flags object with `interactive: True/False` and
      asserts on `interactive_manager.mode`. `interactive` is a recognized-but-inert
      `standard_args` entry that `ParseFileFlags` can never produce, and per the planning finding
      above `prompt_manager` is now unconditionally `None` with `config.sequential` raising
      `NotImplementedError` — so the internals it asserts against no longer exist. **Disposition:
      retired**, since Phase 4's `-q`/`--sequential` fail-fast test already covers the real,
      current contract end-to-end through the actual flag surface.
- [x] Record each of the four dispositions in the phase notes with the specific replacement test
      that subsumes it.

**Disposition Table**:

| File | Disposition | Replacement / rationale |
|------|-------------|--------------------------|
| `builder/tests/test_package_loading.py::TestSubprocessExecution::test_pythonpath_setup_in_subprocess` | Deleted (class removed, `patch`/`MagicMock` import dropped) | `code/tests/packaging/test_cli_console_script.py::test_console_script_runs_without_pythonpath` |
| `code/tests/e2e/test_batch_output_real.py` | Rewritten, kept (did not fully duplicate Phase 4) | Adds real batch-specific assertions Phase 4's single-example `--save` test does not cover: `MODELS.json`'s `"models"` list has one entry per example (2), and combined `EXAMPLES.md` joins per-example sections with `---`. False `-l` comment removed; the file now correctly documents why `-l` is inapplicable here. |
| `builder/tests/e2e/test_full_pipeline.py::test_iteration_workflow` | Rewritten and renamed to `test_print_impossible_flag_includes_impossible_states` | Now honestly exercises `-i`/`--print_impossible` (the flag it always actually invoked), with a baseline-vs-flagged output-differs assertion added so it cannot pass vacuously for a no-op flag |
| `builder/tests/integration/test_cli_interactive_integration.py` | Retired (deleted, 444 lines, 9 tests) | `code/tests/cli/test_flag_matrix.py::test_sequential_fails_fast_without_traceback` covers the real, current `-q`/`--sequential` contract through the actual flag surface. Also updated the two nearest READMEs (`builder/tests/README.md`, `builder/tests/integration/README.md`) to remove the now-stale entry rather than leave dangling documentation. |

**Fifth-instance grep follow-up** (per this phase's Scope Hypothesis): re-grepping
`patch.*subprocess.run` across `code/` after the four dispositions above finds exactly one
remaining hit -- `code/tests/cli/test_flag_matrix.py`'s
`test_upgrade_constructs_expected_pip_command_without_executing`, which is the plan's own
sanctioned pattern for `--upgrade` (mock `subprocess.run`, assert the constructed command, never
execute a real `pip install`) -- not a misleading test. Re-grepping for tests passing
`'interactive'` as a flag finds one file beyond the four, `test_output_directory_guidance.py`.
Investigated per the Scope Hypothesis's explicit instruction: this file's assertions test a real,
still-live `BuildModule.__init__` code branch (`module.py`'s empty-`example_range` +
`interactive` validation, reachable via `hasattr(module_flags, 'interactive')`), not dead
internals like `interactive_manager.mode` -- confirmed by grep (no `interactive_manager`/`.mode`
references in the file) and by running it (7 passed, 5 subtests passed). It is a legitimate unit
test of internal logic via a directly-constructed flags object, not a misleading claim of CLI-level
coverage, so it is **not** a fifth instance of this phase's target defect class and was left
unchanged -- recorded here as the explicit follow-up the Scope Hypothesis requires rather than
silently ignored.

**Timing**: 1.5 hours

**Depends on**: 3, 4, 6

**Verification Tier**: interface

**Scope Hypothesis**: four files are asserted to need disposition. Confirm at implementation time
by re-grepping for tests that patch `subprocess.run` and then assert on the mock
(`grep -rn "patch.*subprocess.run" code/`), and for tests passing `interactive` as a flag — if
either grep finds a fifth instance, widen this phase or record the extra as a follow-up rather
than leaving it silently uncovered.

**Files to modify**:
- `code/src/model_checker/builder/tests/test_package_loading.py` - delete the mock-asserting test
- `code/tests/e2e/test_batch_output_real.py` - rewrite assertions, fix the false comment
- `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py` - rewrite and rename
  `test_iteration_workflow`
- `code/src/model_checker/builder/tests/integration/test_cli_interactive_integration.py` - retire
  or rewrite to the fail-fast contract

**Verification**:
- `grep -rn "patch.*subprocess.run" code/` shows no remaining test that patches then asserts on
  its own mock.
- `PYTHONPATH=code/src pytest code/src/model_checker/builder/tests/ -v` green.
- `PYTHONPATH=code/src pytest code/tests/e2e/ -v` green.

---

### Phase 8: Full-suite regression and runtime budget [COMPLETED]

**Goal**: Prove nothing regressed against the 2193/2193 baseline and that the added coverage did
not make the suite unaffordable.

**Tasks**:
- [x] Run the full suite: `PYTHONPATH=code/src pytest code/tests/ -v` and the in-package tree.
      Baseline is 283 top-level + 1910 in-package = 2193 green. Account for every delta — added
      tests, and the tests deliberately deleted in Phase 7 — so the new total is explained
      exactly, not merely "still green". **Deviation**: the plan-stated baseline (283+1910=2193)
      does not match the actual pre-task-148 commit (`55ea4e8f`, verified directly by checking out
      that commit into a worktree and running both suites): the real baseline is 401 top-level
      (397 passed + 4 skipped) + 1912 in-package = 2313. Used the verified `55ea4e8f` numbers as
      the reconciliation baseline instead of the plan's stale figure — see implementation summary
      for the full per-file delta table, which reconciles exactly (top-level +71, in-package -10).
- [x] Any red is genuinely new. Diagnose it; do not silence it. Zero failures in either suite.
- [x] Capture `--durations=0` and record the runtime cost of each new file. State the resulting
      total suite delta explicitly. If the delta is disproportionate, adjust markers (not
      assertions) and record the reasoning. Top-level: 69.29s (was 32.19s at baseline, +37.1s).
      In-package: 389.99s (was 368.03s at baseline, +21.96s). Judged acceptable — see summary.
- [x] **Re-read every assertion added in Phases 3-7** specifically for weakening: no bare
      `assert result.returncode == 0` standing alone where a behavioral assertion was specified,
      no `xfail` without a reason string, no silently skipped parametrization case. Confirmed: zero
      `xfail` markers in any Phase 3-7 file; every `returncode == 0` assertion in
      `code/tests/cli/test_flag_matrix.py` is paired with additional behavioral assertions
      (output content, file existence, Traceback absence); the one remaining
      `patch('subprocess.run')` site (`test_upgrade_constructs_expected_pip_command_without_executing`)
      asserts real constructed-argv content, matching the plan's sanctioned `--upgrade` exception,
      not the prohibited assert-on-own-mock pattern.
- [x] Confirm each of the five requirement letters (a)-(e) has a named covering test, and record
      that mapping in the implementation summary.

**Timing**: 1 hour

**Depends on**: 7

**Verification Tier**: full

**Files to modify**:
- None (verification only); summary artifact written at task completion.

**Verification**:
- Full suite green with every count delta explained against 2193.
- Runtime delta recorded and judged acceptable.
- Requirement-letter-to-test mapping recorded.

---

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/tests/ -v` green.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/ -v` green.
- [ ] Full-suite count reconciles against the 2193 baseline with every delta explained.
- [ ] `ParseFileFlags` is imported by at least one test (it never was before).
- [ ] The short/long equivalence sweep covers every `_short_to_long` entry, with its own
      completeness assertion.
- [ ] The real `model-checker` console script is invoked for behavior, with no `PYTHONPATH` set.
- [ ] Generate-then-execute passes for every theory in `registry.get_registered()`.
- [ ] `--save` is proven to produce files on disk.
- [ ] `--upgrade` is asserted by constructed-command inspection and never executed.
- [ ] No test in the repo patches `subprocess.run` and then asserts against its own mock.
- [ ] `test_conflicting_flags` has a real mutex assertion, not a `pass` body.

## Artifacts & Outputs

- `code/tests/cli/__init__.py` (new)
- `code/tests/cli/conftest.py` (new)
- `code/tests/cli/test_parse_file_flags.py` (new)
- `code/tests/cli/test_flag_matrix.py` (new)
- `code/tests/packaging/test_cli_console_script.py` (new)
- `code/tests/packaging/test_generate_then_execute.py` (new)
- `code/tests/packaging/conftest.py` (modified — receives `installed_venv`)
- `code/tests/packaging/test_entry_point.py` (modified — fixture moved out, docstring pointer)
- `code/tests/conftest.py`, `code/tests/utils/helpers.py` (modified — harness fixes)
- `code/tests/integration/test_error_handling.py` (modified — stub filled)
- `code/tests/e2e/test_batch_output_real.py` (rewritten or retired)
- `code/src/model_checker/builder/tests/test_package_loading.py` (mock test deleted)
- `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py` (test rewritten/renamed)
- `code/src/model_checker/builder/tests/integration/test_cli_interactive_integration.py`
  (retired or rewritten)
- `specs/148_cli_end_to_end_verification_suite/summaries/01_cli-e2e-verification-summary.md`

## Rollback/Contingency

All changes are test-only except any small in-scope production fix arising from a newly
discovered defect, which is committed separately with its own message so it can be reverted
independently of the test work. Every phase commits at its own green boundary
(`per-substep`), so any phase can be reverted individually with `git revert` without disturbing
the others. If the Phase 6 generate-then-execute journey proves genuinely broken, that phase
lands as `xfail`-marked tests plus a defect report rather than being dropped — the coverage gap
stays visible, which is the whole point of the task. The Phase 2 fixture relocation is the only
change that can break existing green tests; it is verified immediately and in isolation, and is a
pure move that reverts cleanly.
