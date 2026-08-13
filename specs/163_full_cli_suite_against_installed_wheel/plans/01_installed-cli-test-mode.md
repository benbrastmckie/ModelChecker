# Implementation Plan: Run full CLI suite against installed wheel

- **Task**: 163 - Run full CLI suite against installed wheel
- **Status**: [IMPLEMENTING]
- **Effort**: 8 hours
- **Dependencies**: None blocking. Adjacent (must not be touched):
  `harden_release_ci_testpypi_gate` owns `.github/workflows/release.yml`.
- **Research Inputs**: specs/163_full_cli_suite_against_installed_wheel/reports/01_installed-cli-verification.md
- **Artifacts**: plans/01_installed-cli-test-mode.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md;
  code/docs/core/TESTING_GUIDE.md (mandatory TDD);
  .claude/rules/pr-prohibition.md; .claude/rules/no-task-references-in-deliverables.md
- **Type**: python
- **Lean Intent**: false

## Overview

Parametrise the single CLI invocation chokepoint, `run_cli_command`
(`code/tests/utils/helpers.py`), over `MODELCHECKER_CLI_TEST_MODE = source | installed |
installed-module`, so the entire existing `code/tests/cli/` suite — including its parser-derived
completeness gate — executes unchanged against a pip-installed console script. Default remains
`source`, leaving the developer loop untouched. The change is worthless unless the source tree is
provably absent from the verification environment's import path, so a mandatory anti-vacuous-pass
guard, plus active removal of the three in-process source-tree injections this repository
currently performs, is treated as load-bearing rather than optional. Definition of done: the full
`tests/cli/` suite passes inside a real distro container against a pip-installed wheel in both
non-source modes, with the guard asserting `model_checker.__file__` resolves under
`site-packages`.

### Research Integration

Findings carried in from `reports/01_installed-cli-verification.md`:

- **F1** — `run_cli_command` is the sole invocation seam; all CLI tests reach it via the `run_cli`
  fixture (`code/tests/cli/conftest.py`). Phase 2 is therefore a configuration change, not a
  rewrite.
- **F2** — `test_every_registered_flag_is_covered_or_excluded` already derives coverage from
  `ParseFileFlags().parser._actions`; the coverage guarantee transfers to any environment the
  suite runs in for free.
- **F3/F4** — local green is produced by a `LD_LIBRARY_PATH` repair no user applies, on a glibc
  2.42 host (the most permissive possible target). Local green is not evidence about a user's
  machine. Verification must run in a real distro container.
- **F5** — a Nix FHS sandbox was evaluated and rejected on seven grounds; it is not an acceptable
  substitute (D2).
- **F8** — a vacuous pass is the primary hazard and is silent by construction (D6). Phase 3 exists
  solely to make it impossible.
- **F9** — `nix flake check` is red on master at the released commit, on the nixpkgs-z3 /
  PyPI-z3-solver seam. Phase 1 diagnoses it before any environment is trusted as an oracle.
- **R4** — CI wiring is a recorded handoff for the task that owns `release.yml`; explicitly out of
  scope here (D5).

**Correction to the research report's difficulty estimate**: R2 describes the change as "roughly
15 lines in one file". Direct inspection during planning found that popping `PYTHONPATH` from the
subprocess environment is necessary but *not sufficient*. Three separate in-process source-tree
injections currently exist and would each independently cause a vacuous pass in the pytest
process itself:

1. `code/pyproject.toml` — `[tool.pytest.ini_options] pythonpath = "src"`, applied by pytest
   before any conftest loads.
2. `code/tests/conftest.py` — an unconditional `sys.path.insert(0, <repo>/code/src)`.
3. Whatever rootdir/cwd entry pytest itself contributes under the configured
   `--import-mode=importlib`.

`test_flag_matrix.py` imports `model_checker.__main__` in-process, so these are not hypothetical.
Phase 3 is a direct consequence of this finding and is not optional.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` was not supplied as a `roadmap_path` for this dispatch and contains no item
naming installed-wheel CLI verification. The nearest adjacent entries concern package identity
and the wheel's contents (the differential oracle being excluded from the wheel) — this task
strengthens the evidence base behind those claims but does not advance or complete any listed
item. No ROADMAP.md edits are in scope.

## Goals & Non-Goals

**Goals**:
- Parametrise `run_cli_command` over `MODELCHECKER_CLI_TEST_MODE` with `source` as default.
- Make a vacuous pass structurally impossible: guard test plus active removal of source-tree
  injections when a non-source mode is active.
- Achieve console-script vs `python -m` parity across the whole CLI suite via `installed-module`.
- Provide `code/scripts/verify-installed-cli.sh` for the local podman debug loop.
- Diagnose the red `nix flake check` before treating any environment as an oracle.
- Attempt retirement of the sole `_EXCLUDED_FLAGS` entry, `load_theory`.

**Non-Goals**:
- Any edit to `.github/workflows/release.yml` (owned elsewhere; recommendation R4 is a handoff).
- Fixing the TestPyPI trusted-publisher registration.
- Adding a `--yes` / non-interactive CLI path (owned elsewhere; only the *test-side* exclusion is
  in scope here).
- Executable documentation — executing extracted doc commands against an installed package
  (deferred, R7).
- Fixing whatever Phase 1 diagnoses; Phase 1 is diagnosis-only.
- Any `git push`, tag, PR, or upload operation.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Vacuous pass: source tree shadows the wheel, suite passes without touching it | H | H | Phase 3 is dedicated to this: guard test asserting `site-packages` in `model_checker.__file__`, plus active `sys.path` purge. Phase 5 will not be marked complete on a run where the guard skipped. |
| podman is not installed on this host (confirmed: neither `podman` nor `docker` on PATH) | H | H | Phase 5 carries an explicit fallback ladder and terminates as `[BLOCKED]` with a named one-line user action rather than substituting a Nix FHS sandbox (D2/F5) or claiming unverified success. |
| Plan requires editing `code/conftest.py` and `code/tests/conftest.py`, outside the declared `file_scope` | M | H | Flagged explicitly below; `file_scope` is prospective and advisory, but it should be widened at implementation time to `["code/tests/", "code/scripts/", "code/conftest.py"]` to keep overlap detection honest. |
| Changing shared conftest sys.path behavior breaks unrelated suites | H | M | Gate every change on `mode != 'source'`; source mode must be byte-for-byte behaviourally identical. Phase 3 verification runs the full default suite, not just `tests/cli/`. |
| `from tests.utils.helpers import ...` fails inside the container when `code/src` leaves sys.path | M | M | Phase 3 confirms the `tests` package still imports with an explicit sys.path dump; if rootdir insertion is insufficient, set `PYTHONPATH=/w/code` (the test *package* root, never `code/src`) in the runner. |
| `nix flake check` failure is a genuine z3 version sensitivity, not a flake | M | M | Phase 1 diagnoses before Phase 5 relies on any environment as an oracle; a genuine sensitivity is recorded and spawned as a separate task rather than fixed here (out of `file_scope`). |
| `load_theory` retirement appears to work locally but hangs in a container without a tty | M | L | Phase 6 keeps the existing 30s subprocess timeout; if the attempt is not clean, the exclusion and its comment are left intact verbatim (R6). |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 6 | -- |
| 2 | 3, 4 | 2 |
| 3 | 5 | 1, 3, 4 |
| 4 | 7 | 5, 6 |

Phases within the same wave can execute in parallel.

**Sequencing note**: the task directive says to diagnose `nix flake check` "DO FIRST,
SEPARATELY". Phase 1 has no code dependency on Phase 2, so both sit in Wave 1; when phases are
run sequentially, execute Phase 1 first. The hard requirement is Phase 5's dependency on Phase 1
— no environment is trusted as an oracle until the diagnosis lands.

---

### Phase 1: Diagnose the red `nix flake check` [COMPLETED]

**Verdict**: divergent draw (transient contention-based flake), not a deterministic
nixpkgs-z3-vs-PyPI-z3-solver version sensitivity — though a genuine version gap does exist and is
worth tracking separately.

**Evidence gathered this session**:
- Resolved versions: nixpkgs-native `z3-solver` (via `nix develop`) = **4.16.0**;
  real PyPI `z3-solver` wheel (installed into a scratch venv, with the same
  `LD_LIBRARY_PATH` repair `code/tests/packaging/conftest.py` applies) = **5.0.0** — a major
  version jump, confirmed by direct install rather than assumed.
- `test_iteration_via_iterate_api` run in isolation, repeatedly: **8/8 passed** under
  `nix develop` (z3 4.16.0), and **4/4 passed** (3 completed within one batch, a 4th was
  observed passing before the batch's time budget closed) under the real PyPI wheel (z3
  5.0.0). No isolated failure under either version.
- The `checks.default` derivation's exact `checkPhase` command
  (`pytest src/model_checker tests -m "not packaging and not performance and not unstable" -n 6
  -q`, `PYTHONPATH=$PWD/src`, isolated `$HOME`) was run once, live, under `nix develop`,
  reproducing every condition of `nix flake check` except the sandboxed build isolation itself:
  **2013 passed, 254 skipped, 0 failed in 226.76s** — the CI failure (`1 failed, 2012 passed`)
  did not reproduce. Item count (2013) matches CI's total (2012 passed + 1 failed = 2013),
  confirming this was the same selection, not a narrower one.

**Reasoning**: a test that fails deterministically under a genuine version sensitivity would be
expected to reproduce on repeat attempts under the same version and toolchain. It did not, either
in isolation or under a live rerun of the exact `-n 6` contended command the check derivation
runs. This is consistent with the CPU/Z3-state contention flake class already documented
elsewhere in this codebase (`test_build_example_bimodal_theory_countermodel`'s comment on
`max_time` headroom "observed to take just over 10s under full-builder-suite load"). A single
full-suite run is not exhaustive proof of "never fails under Nix" — a true statistical
reproduction would need ~10 full contended runs at ~4 minutes each (out of proportion with this
phase's 1-hour budget) — but combined with 12 clean isolated runs across both z3 versions, it is
sufficient to prefer "divergent draw" over "genuine version sensitivity" as the verdict.

**Recommendation**: no fix is warranted here (diagnosis-only, and any real fix targets
`code/src/model_checker/builder/tests/`, outside this task's `file_scope`). The 4.16.0-vs-5.0.0
z3 version gap between the Nix build and the PyPI wheel is real and worth a separate, low-priority
spawned task to track — not because this specific test proved sensitive to it, but because a major
version jump this large is worth knowing about independent of this flake.

**Files modified**: none (diagnosis only, as planned).

**Goal**: Determine whether
`test_example.py::TestBuildExampleIntegration::test_iteration_via_iterate_api` ("Should find
initial model for A") fails under `nix flake check` because of a divergent solver draw or a
genuine nixpkgs-z3 vs PyPI-`z3-solver` version sensitivity. Diagnosis only — no fix.

**Tasks**:
- [ ] Reproduce: run `nix flake check` at the released commit; capture the exact failure output.
- [ ] Record both z3 versions: the one `flake.nix` supplies (nixpkgs-native, with
      `pythonRemoveDeps = [ "z3-solver" ]`) and the PyPI `z3-solver` version resolved by a normal
      install.
- [ ] Run the same test repeatedly (>= 10 iterations) under the Nix build and under the source
      tree. A test that fails intermittently in both is a draw; one that fails deterministically
      only under Nix is a version sensitivity.
- [ ] If deterministic under Nix: capture the differing solver behavior (seed, model count, or
      `check()` result) far enough to name the mechanism.
- [ ] Record the verdict, the evidence, and a recommendation in the implementation summary. If a
      fix is warranted it targets `code/src/model_checker/builder/tests/`, outside this task's
      `file_scope` — recommend a spawned task, do not fix here.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: The failure is asserted to be a single test in a single file. Confirm by
reading the full `nix flake check` output — if more than one test fails, or the failure does not
reproduce at all, record that and adjust rather than forcing the reported shape.

**Files to modify**:
- None (diagnosis only). Findings land in the task summary.

**Verification**:
- A written verdict of "divergent draw" or "version sensitivity", each backed by the iteration
  counts and version numbers that support it.
- No source file modified by this phase.

---

### Phase 2: Parametrise `run_cli_command` over an invocation mode [COMPLETED]

**Goal**: Introduce `MODELCHECKER_CLI_TEST_MODE` with three modes and route the single
invocation chokepoint through it, defaulting to `source` so the existing developer loop is
unaffected.

**Tasks**:
- [ ] TDD first: add `code/tests/cli/test_cli_mode.py` asserting (a) default mode is `source`,
      (b) each of the three modes yields the expected command vector and environment, (c) an
      unknown value raises immediately with the offending value in the message, (d) `installed`
      raises a clear `RuntimeError` when `model-checker` is not on `PATH`. Confirm RED.
- [ ] Add `code/tests/utils/cli_mode.py` exposing a single `get_cli_test_mode()` that reads and
      validates the env var, so no other module re-derives the vocabulary.
- [ ] Rewrite the environment/command construction in `run_cli_command`
      (`code/tests/utils/helpers.py`) per R2: `source` keeps today's `PYTHONPATH` injection and
      `python -m` invocation; `installed` pops `PYTHONPATH` and invokes
      `shutil.which('model-checker')`; `installed-module` pops `PYTHONPATH` and invokes
      `python -m model_checker`.
- [ ] Keep the public signature (`args, capture_output, check, timeout, cwd, input`) unchanged —
      `assert_cli_success` / `assert_cli_failure` / `BaseCLITest` forward through it.
- [ ] Document the three modes in `run_cli_command`'s docstring, including why `installed` must
      not inject `PYTHONPATH` (any reliance on the source tree must fail there; that is the
      point).

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: interface

**Scope Hypothesis**: The research report estimates "roughly 15 lines in one file, plus
`import shutil`". Confirm at implementation time by grepping for every constructor of a CLI
subprocess invocation (`-m model_checker`, `model-checker`) across `code/tests/`; if any test
builds an invocation without going through `run_cli_command`, the chokepoint claim (F1) is false
for that call site and it must be routed through the helper or explicitly excepted with a reason.

**Files to modify**:
- `code/tests/utils/cli_mode.py` - new; single source of the mode vocabulary and its validation
- `code/tests/utils/helpers.py` - `run_cli_command` env/command construction
- `code/tests/cli/test_cli_mode.py` - new; unit tests for mode dispatch

**Verification**:
- New mode tests pass (GREEN after RED).
- `PYTHONPATH=code/src pytest code/tests/cli/ -v` fully green in default mode.
- `pytest code/tests/packaging/ -m packaging` still green (baseline from research: 106 passed,
  4 skipped).
- `git diff` shows no behavioural change on the `source` path.

---

### Phase 3: Close the source-tree shadowing holes and add the vacuous-pass guard [COMPLETED]

**Scope Hypothesis result**: exactly **two** in-process source-tree injection sites confirmed by
a live `sys.path` dump inside `code/tests/cli/` under a forced non-source mode, both resolving to
the literal same path (`code/src`, appearing twice) -- `pyproject.toml`'s `pythonpath = "src"`
and `tests/conftest.py`'s own insert. The third hypothesized site ("whatever rootdir/cwd entry
pytest itself contributes under `--import-mode=importlib`") did **not** manifest as a `sys.path`
entry at all -- pytest's importlib import mode resolves the `tests` package via direct
`sys.modules` population during collection, not via a `sys.path` search, so `from
tests.utils.helpers import ...` remains resolvable after the purge with no third injection to
handle and no `PYTHONPATH=code` fallback needed (de-risking the corresponding row in the plan's
Risks table).

**`code/conftest.py` import-ordering finding**: `from tests.utils.cli_mode import
get_cli_test_mode` at this rootdir conftest's module-load time genuinely raises
`ModuleNotFoundError` (confirmed empirically with a debug marker, then removed) -- the rootdir
conftest loads before pytest's importlib package-chain machinery has bound `tests` for this
invocation. The `try/except ModuleNotFoundError` fallback in `code/conftest.py` (reading the env
var directly, same default) is therefore load-bearing, not defensive dead code, and is commented
as the one deliberate exception to "no other module re-derives the vocabulary."

**Guard-fails-loud demonstration** (required before the purge landed): confirmed once,
deliberately -- `MODELCHECKER_CLI_TEST_MODE=installed PYTHONPATH=code/src pytest
code/tests/cli/test_installed_mode_guard.py` **FAILED** (not skipped, not errored) with
`model_checker` resolving to `code/src/model_checker/__init__.py`.

**Post-purge verification, real installed wheel**: built `model_checker-1.3.3-py3-none-any.whl`
locally (`PIP_USER=0 python -m build`, worked around this host's ambient `pip.conf`
`install.user=true`), installed it into a scratch venv with the same `LD_LIBRARY_PATH` repair
`tests/packaging/conftest.py` documents, and ran the full `tests/cli/` suite against it directly
(not yet inside a container -- that remains Phase 5's job):
- `installed` mode: guard **PASSED** (not skipped), `model_checker.__file__` resolved to
  `.../wheeltest/lib/python3.13/site-packages/model_checker/__init__.py`; full `tests/cli/`
  suite **85 passed**.
- `installed-module` mode: same wheel, **85 passed**.
- Collected-test count matched the host source-mode baseline exactly: **85 == 85**.
- `test_every_registered_flag_is_covered_or_excluded` executed (not just collected) in both
  installed-mode runs, as part of the 85.

**Source mode regression check**: `PYTHONPATH=code/src pytest code/tests/cli/
code/tests/unit/test_main_cli.py -v` -> 94 passed, 1 skipped (the guard, correctly, in source
mode). Full-suite regression check (`pytest src/model_checker tests -m "not packaging and not
performance and not unstable" -n 6 -q`, matching the `nix flake check` selection): **1 failed,
2276 passed, 1 skipped** -- the one failure
(`test_solver_comparison.py::test_example_with_solver[cvc5-CL_CM_5]`) passed cleanly when rerun
in isolation immediately after, and touches solver comparison logic entirely unrelated to
`sys.path`/import location; recorded as a pre-existing `-n 6` contention flake (the same
documented class as Phase 1's finding and the codebase's own `max_time`-under-load comments), not
a regression introduced by this phase's changes.

**Files modified**: `code/tests/cli/test_installed_mode_guard.py` (new), `code/tests/conftest.py`
(gated insert), `code/conftest.py` (purge, with the fallback vocabulary reader).

**Goal**: Make it structurally impossible for `import model_checker` to resolve to the working
tree while a non-source mode is active, and assert loudly if it ever does. This is the phase the
whole change depends on for meaning (F8/D6).

**Tasks**:
- [ ] TDD first: add `code/tests/cli/test_installed_mode_guard.py` — skips with a loud reason in
      `source` mode; otherwise asserts `'site-packages' in model_checker.__file__` with a message
      naming the resolved path, and additionally asserts no `sys.path` entry resolves to
      `code/src`. Confirm it fails today when a non-source mode is forced.
- [ ] Gate `code/tests/conftest.py`'s unconditional `sys.path.insert(0, <repo>/code/src)` on
      `get_cli_test_mode() == 'source'`.
- [ ] In `code/conftest.py` (the rootdir conftest, loaded before any test module imports), purge
      every `sys.path` entry resolving to `code/src` when mode is not `source`. This is the only
      available defence against `[tool.pytest.ini_options] pythonpath = "src"`, which pytest
      applies during config before conftests load and which a caller can otherwise only defeat
      with `-o pythonpath=`.
- [ ] Confirm empirically that `from tests.utils.helpers import ...` and
      `from model_checker.__main__ import ParseFileFlags` both still resolve after the purge, in
      both non-source modes; dump `sys.path` and `model_checker.__file__` once as evidence.
- [ ] Confirm source mode is byte-for-byte behaviourally unchanged.

**Timing**: 1.5 hours

**Depends on**: 2

**Verification Tier**: full

**Scope Hypothesis**: Exactly three in-process source-tree injection sites are asserted
(`pyproject.toml` `pythonpath`, `code/tests/conftest.py`'s insert, and pytest's own rootdir/cwd
entry). Confirm by dumping the full `sys.path` from inside a non-source-mode pytest run *before*
the purge and accounting for every entry that resolves under `code/`; a fourth injection site
found there must be handled, not ignored.

**Files to modify**:
- `code/tests/cli/test_installed_mode_guard.py` - new; the mandatory guard
- `code/tests/conftest.py` - gate the src insert on source mode
- `code/conftest.py` - purge `code/src` from `sys.path` in non-source modes

**Scope note**: `code/conftest.py` and `code/tests/conftest.py` fall outside the task's declared
`file_scope` (`code/tests/cli/`, `code/tests/utils/helpers.py`, `code/scripts/`). They are
unavoidable — the injections live there. Widen `file_scope` to `["code/tests/",
"code/scripts/", "code/conftest.py"]` when starting this phase.

**Verification**:
- Guard test fails (not skips, not errors) when a non-source mode is set while the source tree is
  still importable — demonstrated once, deliberately, before the purge lands.
- Guard test passes in a genuine installed environment (deferred confirmation to Phase 5).
- Full default-mode suite green: `PYTHONPATH=code/src pytest code/tests/ -v` plus
  `code/src/model_checker` per `code/docs/core/TESTING_GUIDE.md`, no new failures or skips.

---

### Phase 4: Local container runner script [COMPLETED]

**Verification performed**: `bash -n` clean; `shellcheck` (via `nix run nixpkgs#shellcheck`)
clean with zero findings; executable bit set (`chmod +x`). Both failure paths exercised directly
on this host (which genuinely lacks podman, so the "podman absent" path needed no simulation):
absent-podman run exits 1 with the exact `virtualisation.podman.enable = true;` + rebuild
instruction; a temporarily-moved `code/dist/` with a stubbed-out fake `podman` on `PATH` exits 2
with the `python -m build` command to run. Neither failure path performs any partial work.

**Goal**: Provide `code/scripts/verify-installed-cli.sh` so the container behaviour is
reproducible locally in seconds instead of via CI cycles (R5).

**Tasks**:
- [ ] Write `code/scripts/verify-installed-cli.sh` wrapping the podman invocation from R5: mount
      the repo read-only, create a venv inside `python:3.11-slim`, `pip install` the built wheel
      plus pytest, then run `tests/cli/` under `installed` and `installed-module`.
- [ ] Fail fast and legibly when podman is absent: name the required host change
      (`virtualisation.podman.enable = true;` plus a rebuild) and exit non-zero. Never silently
      fall back to a Nix FHS sandbox or to the host (D2/F5).
- [ ] Fail fast when `code/dist/*.whl` is missing or stale, with the build command to run.
- [ ] Accept an optional image argument so `python:3.10-slim` / `python:3.12-slim` /
      `ubuntu:20.04` can be exercised without editing the script.
- [ ] `set -euo pipefail`, `shellcheck`-clean, executable bit set, brief usage header.
- [ ] Add a one-paragraph entry to `code/scripts/README.md`.

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: local

**Files to modify**:
- `code/scripts/verify-installed-cli.sh` - new
- `code/scripts/README.md` - script inventory entry

**Verification**:
- `bash -n` and `shellcheck` clean.
- Running it with podman absent produces the named user action and a non-zero exit — no partial
  work, no misleading success.
- Running it with a missing wheel produces the build command and a non-zero exit.

---

### Phase 5: Execute container verification against a real installed wheel [NOT STARTED]

**Goal**: Actually run the full `tests/cli/` suite against a pip-installed wheel inside a real
distro container, in both `installed` and `installed-module` modes, with the guard active. This
phase produces the evidence the whole task exists for.

**Tasks**:
- [ ] Build a fresh wheel into `code/dist/` (do not reuse the stale `1.3.0` artifacts present
      there).
- [ ] Attempt, in order: (a) `podman` if on PATH; (b) `docker` if on PATH; (c) a rootless podman
      obtained ad hoc via `nix run nixpkgs#podman` — expected to fail without the host's setuid
      `newuidmap` wrapper, so treat a failure as informative, not as a reason to improvise.
- [ ] If none succeeds: mark this phase `[BLOCKED]`, record the exact one-line NixOS change
      (`virtualisation.podman.enable = true;`) plus rebuild as the user action, and explicitly do
      NOT claim verification. A Nix FHS sandbox is not an acceptable substitute (F5).
- [ ] On success: run `MODELCHECKER_CLI_TEST_MODE=installed pytest tests/cli/ -v` and
      `MODELCHECKER_CLI_TEST_MODE=installed-module pytest tests/cli/ -v` inside the container.
- [ ] Confirm the guard **ran and passed** — a skipped guard means the run proves nothing. Quote
      the guard's resolved `model_checker.__file__` in the summary.
- [ ] Confirm `test_every_registered_flag_is_covered_or_excluded` executed in the container, not
      just collected.
- [ ] Record any failures that reproduce only in the container — those are the real product of
      this task and must be reported even if they cannot be fixed within `file_scope`.

**Timing**: 1.5 hours

**Depends on**: 1, 3, 4

**Verification Tier**: full

**Scope Hypothesis**: The container run is assumed to reach every test in `tests/cli/`. Confirm by
comparing the container run's collected-test count against the host's source-mode count for the
same directory; a smaller count means collection silently dropped tests (e.g. an import error
swallowed as a skip) and the run is not evidence.

**Files to modify**:
- None expected. Any fix required to make the container run green is a new finding — record it,
  and only make the change if it lands inside `code/tests/` or `code/scripts/`.

**Verification**:
- Both modes green inside the container, with the guard passing (not skipping) in each.
- Collected-test counts match the host source-mode baseline.
- Evidence quoted in the summary: image name, Python version, wheel filename, resolved
  `model_checker.__file__`, and the two pass lines.

---

### Phase 6: Attempt to retire the `load_theory` exclusion [COMPLETED]

**Result**: retired cleanly. `ask_generate()` prompts three times, not the plan's assumed one
(`(y/n)` to generate, project name, then `_handle_example_script`'s `(y/n)` to test the
generated example) -- discovered by direct dispatch before writing the test. Piping
`input="y\ngen_project\nn\n"` through `run_cli_command` produces a clean, error-free,
`returncode == 0` generation, confirmed 6/6 clean runs during investigation and 5/5 repeat runs
of the finished test (`pytest -k load_theory`, run 5x per the plan's requirement) -- all fast
(~0.2s each) and none hung. A closed-stdin run (`input=""`) fails immediately with a nonzero
return code (EOFError on the very first uncaught `input()` call) rather than hanging, confirmed
separately. `_EXCLUDED_FLAGS` is now empty; `test_every_registered_flag_is_covered_or_excluded`
passes with `load_theory` moved into `_COVERED_FLAGS`. Full-file wall time: 38.04s (was ~37s
before this phase) -- same order, no regression.

**Files modified**: `code/tests/cli/test_flag_matrix.py` (dispatch test added,
`_EXCLUDED_FLAGS`/`_COVERED_FLAGS` updated).

**Goal**: Close the completeness gate over the full registered flag set by piping `input="y\n"`
through `run_cli_command`'s existing `input` parameter — or, failing that, leave the exclusion and
its comment intact (R6/F7).

**Tasks**:
- [ ] Add a dispatch test for `-l`/`--load_theory` in `code/tests/cli/test_flag_matrix.py` using
      `input="y\n"` and the existing 30s timeout, run in a `tmp_path` cwd so generated project
      output is contained.
- [ ] If it passes cleanly and repeatably (run it >= 5 times, and once with a closed stdin to
      confirm it does not hang): move `load_theory` from `_EXCLUDED_FLAGS` to `_COVERED_FLAGS`,
      leaving `_EXCLUDED_FLAGS` empty, and update the surrounding comment to record that the set
      is now empty and why.
- [ ] If it does not: revert the attempt, leave `_EXCLUDED_FLAGS` and its comment **verbatim**,
      and record the observed failure mode. The real fix (a non-interactive `--yes` path) is owned
      elsewhere and must not be duplicated here.
- [ ] Either way, confirm `test_every_registered_flag_is_covered_or_excluded` still passes.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: `_EXCLUDED_FLAGS` is asserted to hold exactly one entry (`load_theory`).
Confirm by reading the live set before editing; if it has grown, only `load_theory` is in scope
here.

**Files to modify**:
- `code/tests/cli/test_flag_matrix.py` - dispatch test and, conditionally, the exclusion set

**Verification**:
- `pytest code/tests/cli/test_flag_matrix.py -v` green, including the completeness gate.
- No test hangs: full-file wall time stays within the same order as before.
- If retired: `_EXCLUDED_FLAGS` is empty and the comment says so.

---

### Phase 7: Document the mode and record the CI handoff [NOT STARTED]

**Goal**: Make `MODELCHECKER_CLI_TEST_MODE` discoverable to a developer who did not read this
plan, and leave the R4 CI wiring where its owning task will find it.

**Tasks**:
- [ ] Document the three modes, the default, and the guard in `code/tests/README.md` (and
      `code/tests/cli/`'s module docstring, whose current text — "All CLI invocations in this
      directory go through `python -m model_checker` (never the installed console script)" —
      becomes wrong once Phase 2 lands and must be corrected).
- [ ] Note the podman prerequisite alongside the runner script entry.
- [ ] Confirm the R4 `verify-install` YAML remains recorded in the research report for the task
      that owns `release.yml`; do not copy it into any workflow file.
- [ ] Write the implementation summary, including Phase 1's verdict and Phase 5's evidence (or its
      blocked state and the required user action).
- [ ] Confirm no deliverable outside `specs/**` cites a task number
      (`.claude/rules/no-task-references-in-deliverables.md`); reference filenames and headings
      instead.

**Timing**: 0.5 hours

**Depends on**: 5, 6

**Verification Tier**: prose

**Files to modify**:
- `code/tests/README.md` - mode documentation
- `code/tests/cli/conftest.py` - correct the now-stale module docstring
- `specs/163_full_cli_suite_against_installed_wheel/summaries/01_installed-cli-test-mode-summary.md` - new

**Verification**:
- Every changed hunk lies inside a docstring, comment, or markdown prose region — except the
  conftest docstring correction, which is confirmed by re-running `pytest code/tests/cli/ -v`.
- `bash .claude/scripts/check-task-references.sh` (or equivalent grep) reports no task-number
  citation in `code/**`.

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/tests/cli/ -v` green in default (`source`) mode — no
      behavioural change from today.
- [ ] `pytest code/tests/packaging/ -m packaging` green (research baseline: 106 passed, 4
      skipped).
- [ ] Full suite per `code/docs/core/TESTING_GUIDE.md` green: `PYTHONPATH=code/src pytest
      code/tests/ code/src/model_checker -v` with no new failures or skips.
- [ ] `MODELCHECKER_CLI_TEST_MODE=installed pytest tests/cli/ -v` green inside a
      `python:3.*-slim` container against a pip-installed wheel.
- [ ] `MODELCHECKER_CLI_TEST_MODE=installed-module pytest tests/cli/ -v` green in the same
      container.
- [ ] The anti-vacuous-pass guard **runs and passes** (never merely skips) in both non-source
      runs, with the resolved `model_checker.__file__` quoted as evidence.
- [ ] `test_every_registered_flag_is_covered_or_excluded` executes, not merely collects, in the
      container.
- [ ] Container collected-test count matches the host source-mode baseline for `tests/cli/`.
- [ ] `shellcheck code/scripts/verify-installed-cli.sh` clean; the script exits non-zero with a
      named user action when podman is absent.
- [ ] `.github/workflows/release.yml` is untouched (`git diff --stat` confirms).

## Artifacts & Outputs

- `code/tests/utils/cli_mode.py` - mode vocabulary and validation (new)
- `code/tests/utils/helpers.py` - mode-aware `run_cli_command`
- `code/tests/cli/test_cli_mode.py` - mode dispatch unit tests (new)
- `code/tests/cli/test_installed_mode_guard.py` - mandatory anti-vacuous-pass guard (new)
- `code/tests/conftest.py`, `code/conftest.py` - source-tree injection gated on source mode
- `code/tests/cli/test_flag_matrix.py` - `load_theory` dispatch test; exclusion retired if clean
- `code/scripts/verify-installed-cli.sh` - local podman runner (new)
- `code/scripts/README.md`, `code/tests/README.md`, `code/tests/cli/conftest.py` - documentation
- `specs/163_full_cli_suite_against_installed_wheel/summaries/01_installed-cli-test-mode-summary.md`

## Rollback/Contingency

Every phase is additive or mode-gated, and `source` is the default, so reverting is
low-risk. Take `bash .claude/scripts/git-snapshot.sh 163` before any destructive operation.

- **Phase 2/3 regress the default suite**: revert `code/tests/utils/helpers.py`,
  `code/tests/conftest.py`, and `code/conftest.py` to restore today's unconditional source-tree
  behaviour; the new test files are inert in source mode and can stay.
- **Phase 5 blocked on podman**: leave Phases 2-4 and 6 landed — they are independently
  valuable — mark the task `[PARTIAL]` with the one-line NixOS change as the named user action,
  and do not claim installed-wheel verification anywhere.
- **Phase 6 attempt hangs or flakes**: revert only that hunk; `_EXCLUDED_FLAGS` and its comment
  return verbatim.
- **Never** discard uncommitted work to reach a green build; fix forward per
  `.claude/rules/error-handling.md`.
