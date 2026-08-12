# Implementation Plan: Fix CI failures (wheel dep and timing-gated tests)

- **Task**: 155 - fix_ci_failures_wheel_dep_and_timing_gated_tests
- **Status**: [NOT STARTED]
- **Effort**: 2.75 hours
- **Dependencies**: None
- **Research Inputs**: specs/155_fix_ci_failures_wheel_dep_and_timing_gated_tests/reports/01_ci-failures-wheel-and-timing.md
- **Artifacts**: plans/01_ci-fixes-wheel-and-timing.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false
- **Revision**: r1 -- Phase 6 amended to add a local `python -m build --no-isolation` +
  `check-wheel-contents` observation of the Class 1 fix. Phases 1-5 unchanged.

## Overview

The first live workflow run on 2026-08-12 surfaced three independent classes of CI failure, none
of which is a semantic defect (2000-2002 tests passed on every job). This plan applies a
different, class-appropriate remedy to each: add the missing `wheel` build dependency to the two
install lines that lack it (release-blocking), mark the two genuine wall-clock *speed* assertions
`@pytest.mark.performance` and deselect them in both CI gates simultaneously, raise the
*application-level* time budgets for the two correctness tests that merely ran out of time doing
real work, and raise the pre-existing differential-tests timeout. Definition of done: every edit
site in the research report's table is changed, local runs confirm no syntax/marker/collection
regressions, and the implementer reports the fixes as ready while naming the exact workflow runs
the user must observe -- without claiming CI-green, pushing, opening a PR, or tagging.

### Research Integration

The research report verified every claim in the task description against the current tree and
produced an exact edit-site table (10 rows across 9 files), which this plan consumes directly.
Findings that shaped the phase structure:

- `release.yml` has TWO `pip install` sites in TWO different jobs. Only the `build` job (line 99,
  `pip install build twine`) is implicated. The `test-and-release` job (line 51,
  `pip install build wheel setuptools`) ALREADY has `wheel` and must not be touched.
- `test_complex_model_performance` is a speed assertion dressed as a hang guard (`elapsed < 20.0`
  / `elapsed < 30.0` assertion bodies), so it is routed to class 2(a) alongside
  `test_performance_improvement` rather than getting a raised `@pytest.mark.timeout`.
- The two class-2(b) failures are driven by an application-level `max_time` and an outer
  `subprocess.run(timeout=...)` -- NOT by `@pytest.mark.timeout` markers (neither file has one).
  "Raise the pytest-timeout budget" therefore maps to a different literal knob in each case.
- `flake.nix:147` and `.github/workflows/tests.yml:66` carry identical `-m "not packaging"`
  selectors and must gain `and not performance` together, or the PyPI-toolchain gate and the
  nixpkgs-toolchain gate will diverge on which tests are CI-appropriate.

#### Revision r1: `check-wheel-contents` now available

`check-wheel-contents` was NOT installed when this plan was first written (zero occurrences in
the plan and zero in the research report). It has since been installed and was re-verified
directly at revision time:

| Probe | Result |
|-------|--------|
| `command -v check-wheel-contents` | `/home/benjamin/.nix-profile/bin/check-wheel-contents` |
| `check-wheel-contents --version` | `check-wheel-contents 0.6.3` |
| `import check_wheel_contents` | resolves inside the nix python3.13 env |
| `python -c "import build"` / `import wheel` / `import setuptools` | `1.4.4` / `0.46.1` / `80.10.1` |
| `code/pyproject.toml` `build-system.requires` | `["setuptools>=42", "wheel"]` |

Four facts established at revision time shape how Phase 6 consumes the tool:

1. **It resolves via the user's nix *profile*, not the flake devShell.** `nixpkgs#check-wheel-contents`
   and its three plausible attribute spellings all still fail to evaluate, and `flake.nix`'s
   `devShells.default` is `packages = [ devPython ]` only. `specs/TODO.md:235` independently
   records that the devShell has no `build`, `twine`, or `check-wheel-contents`. Phase 6
   therefore runs this step from the **ambient shell**, never inside `nix develop`.
2. **`build-system.requires` genuinely lists `wheel`.** This is why `--no-isolation` -- which
   deliberately does NOT provision build-system requires -- is the faithful local reproduction of
   the CI failure mode `ERROR Missing dependencies: wheel`, and thus a real observation of the
   Class 1 fix rather than a formality.
3. **The tool exits 1 on the current tree, on a pre-existing finding.** Run against the existing
   `code/dist/model_checker-1.3.0-py3-none-any.whl` it reports `W002: Wheel contains duplicate
   files` for the four identical `theory_lib/{bimodal,exclusion,imposition,logos}/VERSION` files
   (each containing `1.0.0`), and **exits 1**. `--ignore W002` returns `OK` and exits 0. This
   finding predates task 155 and is unrelated to the `wheel` install-list fix.
4. **This corrects a stale historical claim.** The archived rehearsal
   (`specs/archive/125_release_engineering_and_pypi_rehearsal/`) recorded `check-wheel-contents
   dist/*.whl` -> `OK` (clean). That is no longer reproducible on the current tree, consistent
   with `specs/TODO.md:161`'s note that the archived rehearsal's artifact evidence is stale.
   Recording the W002 finding is in scope; fixing it is not.

The plan-level consequence is that `check-wheel-contents` is wired in as a **non-blocking
observation**, with its expected exit-1 stated up front so an implementer does not mistake a
known pre-existing finding for a Phase 6 failure. See Phase 6's "Non-blocking contract".

### Prior Plan Reference

No prior plan. This file is revision r1 of the original plan; the revision is confined to
Phase 6 plus its bookkeeping. Phases 1-5 are byte-unchanged -- their edit sites, budgets, and
commit modes were re-verified against the tree during planning and remain correct.

### Roadmap Alignment

No `roadmap_path` was supplied in the delegation context, so no roadmap consultation was
performed and no roadmap review/update phases are included.

## Goals & Non-Goals

**Goals**:
- Unblock the publish pipeline by making `wheel` importable wherever `python -m build` runs.
- Stop wall-clock *speed* assertions from running on contended CI runners, via a marker plus a
  matching selector change in both gates.
- Keep the two real correctness tests running, with budgets generous enough to survive contention.
- Raise the pre-existing differential-tests budget without dropping the scan's coverage.
- End with an honest readiness report naming exactly which workflow runs the user must check.

**Non-Goals**:
- Changing any production/library code. No semantic defect is implicated anywhere in this task.
- Deselecting `test_iterate_two_produces_distinct_models`, `test_theory_library_execution`, or
  `TestGatingConclusiveScan` -- these do real correctness work and must keep running.
- Touching `release.yml:51` (`test-and-release` job), which already installs `wheel`.
- Touching `.github/workflows/packaging.yml`'s `-m packaging` selector or
  `differential-tests.yml`'s `-m "not slow and not differential"` selector -- disjoint marker sets.
- Asserting CI-green, pushing a branch, opening a PR, or tagging. All four are prohibited for the
  implementing agent by `.claude/rules/pr-prohibition.md`.
- Reverting the `flake.nix` `checks.default` broadening, which remains correct.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The two CI gates drift: only one of `tests.yml` / `flake.nix` gains `and not performance` | H | M | Phase 3 changes both files as a single atomic-batch commit; its verification greps the whole repo for any remaining bare `-m "not packaging"` |
| `@pytest.mark.performance` accidentally deselects more than the two intended tests | M | L | Phase 3 verification runs `--collect-only -m performance` and asserts the collected set is exactly the two named node IDs |
| Raised budgets are still too tight under CI contention | M | M | Prefer generous over tight per the task description: `max_time` 30 -> 60, generated-example `max_time` 10, outer subprocess timeout 15 -> 30, differential `--timeout` 300 -> 900 |
| Outer `subprocess.run` timeout becomes the new bottleneck once the inner `max_time` grows | M | M | Phase 4 raises both knobs together and states the required ordering (outer > inner + startup/import overhead) |
| `release.yml:51` edited by mistake, or the wrong `pip install` line changed | M | L | Phase 1 verification greps both `release.yml` install lines and confirms line 51 is byte-identical to its pre-edit content |
| Local green is mistaken for CI green (the exact failure this task exists to fix) | H | M | Phase 6 is explicitly a reporting phase: it states local evidence is necessary-not-sufficient and names the workflow runs to observe |
| Class 3 (differential-tests) work delays the release-blocking Class 1 fix | M | L | Phase 1 is release-blocking and sits alone in Wave 1's critical position; Phase 5 is independent and explicitly droppable |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 4, 5 | -- |
| 2 | 3 | 2 |
| 3 | 6 | 1, 2, 3, 4, 5 |

Phases within the same wave can execute in parallel. Phase 1 is release-blocking and should be
done first even though the wave permits reordering.

---

### Phase 1: Add `wheel` to the two deficient install lines [NOT STARTED]

**Goal**: Make `wheel` importable in every ambient environment where `python -m build` runs, so
the packaging contract suite and the release `build` job stop dying with
`ERROR Missing dependencies: wheel`.

**Tasks**:
- [ ] `.github/workflows/packaging.yml` line 27: `pip install pytest build` ->
      `pip install pytest build wheel`
- [ ] `.github/workflows/release.yml` line 99 (inside the `build` job, under
      `- name: Build package`): `pip install build twine` -> `pip install build twine wheel`
- [ ] Confirm `.github/workflows/release.yml` line 51 (`test-and-release` job,
      `pip install build wheel setuptools`) is UNCHANGED

**Timing**: 15 minutes

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: atomic-batch

**Scope Hypothesis**: Exactly two `pip install` lines in the repository invoke a `python -m build`
step without `wheel`. Confirm at implementation time with
`grep -rn "python -m build" .github/workflows/` and, for each hit, reading the nearest preceding
`pip install` line; expect exactly three `python -m build` sites (packaging.yml via the contract
suite, release.yml:51, release.yml:~101) of which exactly two install lines need `wheel` added.

**Files to modify**:
- `.github/workflows/packaging.yml` - add `wheel` to the packaging-test dependency install
- `.github/workflows/release.yml` - add `wheel` to the `build` job's install only

**Verification**:
- `python -c "import yaml,sys; [yaml.safe_load(open(f)) for f in ['.github/workflows/packaging.yml','.github/workflows/release.yml']]"` parses both files
- `grep -n "pip install" .github/workflows/release.yml` shows both lines; the `build wheel setuptools` line is byte-identical to its pre-edit content and the other now reads `build twine wheel`
- `grep -n "pip install pytest build wheel" .github/workflows/packaging.yml` matches
- `git diff --stat` shows exactly two files, one changed line each

---

### Phase 2: Mark the two speed-assertion tests `@pytest.mark.performance` [NOT STARTED]

**Goal**: Attach the already-registered but never-applied `performance` marker to the two tests
that assert a wall-clock speed bound a shared 2-core runner cannot fairly measure.

**Tasks**:
- [ ] Confirm the marker is registered at `code/pyproject.toml:90`
      (`"performance: Tests that verify performance characteristics"`) -- registration exists, do
      not re-add it
- [ ] `code/src/model_checker/builder/tests/test_refactoring_target_behavior.py`: add
      `@pytest.mark.performance` immediately above `def test_performance_improvement(self):`
      (line ~311). This is a `unittest.TestCase` method; pytest marks apply to TestCase methods.
      `import pytest` is already present at line 18 -- do not add a duplicate import
- [ ] `code/tests/integration/test_performance.py`: stack `@pytest.mark.performance` alongside the
      existing `@pytest.mark.timeout(30)` above `def test_complex_model_performance(self):`
      (line ~53). Leave the existing timeout marker in place
- [ ] Do NOT add the marker to any other test

**Timing**: 15 minutes

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: Exactly two tests in the tree should carry `@pytest.mark.performance`, and
zero carry it today. Confirm before editing with
`grep -rn "@pytest.mark.performance" code/` (expect zero hits) and after editing with the same
command (expect exactly two hits, in the two named files).

**Files to modify**:
- `code/src/model_checker/builder/tests/test_refactoring_target_behavior.py` - decorate `test_performance_improvement`
- `code/tests/integration/test_performance.py` - decorate `test_complex_model_performance`

**Verification**:
- `grep -rn "@pytest.mark.performance" code/` returns exactly two lines
- `cd code && PYTHONPATH=src python -m pytest --collect-only -q -m performance src/model_checker tests` collects exactly two node IDs: `...test_refactoring_target_behavior.py::TestTargetLoaderBehavior::test_performance_improvement` and `...test_performance.py::TestExecutionPerformance::test_complex_model_performance`
- No `PytestUnknownMarkWarning` appears in that collection output (proves the marker is registered)

---

### Phase 3: Deselect `performance` in BOTH CI gates [NOT STARTED]

**Goal**: Extend the existing marker selector in both gate definitions so the PyPI-toolchain gate
and the nixpkgs-toolchain gate agree on which tests are CI-appropriate.

**Tasks**:
- [ ] `.github/workflows/tests.yml` line 66:
      `pytest tests/ src/model_checker -m "not packaging" -n 6 -q` ->
      `pytest tests/ src/model_checker -m "not packaging and not performance" -n 6 -q`
- [ ] `flake.nix` line 147 (inside `checks.default`'s `checkPhase`):
      `pytest src/model_checker tests -m "not packaging" -n 6 -q` ->
      `pytest src/model_checker tests -m "not packaging and not performance" -n 6 -q`
- [ ] Leave `-n 6` unchanged in both (the documented bimodal CPU-contention flake guard)
- [ ] Do NOT touch `packaging.yml`'s `-m packaging` selector or `differential-tests.yml`'s
      `-m "not slow and not differential"` selector

**Timing**: 30 minutes

**Depends on**: 2

**Verification Tier**: interface

**Commit Mode**: atomic-batch

**Scope Hypothesis**: Exactly two selector sites in the repository carry the bare
`-m "not packaging"` string and both must change together. Confirm at implementation time with
`grep -rn 'not packaging' --include='*.yml' --include='*.nix' .` -- expect exactly two hits before
the edit and zero bare (un-extended) hits after.

**Files to modify**:
- `.github/workflows/tests.yml` - extend the `general-tests` matrix selector
- `flake.nix` - extend the `checks.default` `checkPhase` selector

**Verification**:
- `grep -rn 'not packaging' --include='*.yml' --include='*.nix' .` shows both hits now reading `not packaging and not performance`; no bare `-m "not packaging"` remains
- `nix flake check --no-build` (or at minimum `nix-instantiate --parse flake.nix`) confirms `flake.nix` still parses
- `python -c "import yaml; yaml.safe_load(open('.github/workflows/tests.yml'))"` parses
- Run the exact new selector locally and diff the collected count against the old one: `cd code && PYTHONPATH=src python -m pytest --collect-only -q -m "not packaging and not performance" src/model_checker tests | tail -1` vs the same with `-m "not packaging"`; the difference must be exactly 2

---

### Phase 4: Raise the two application-level budgets for the correctness tests [NOT STARTED]

**Goal**: Give the two tests that ran out of time doing real work enough headroom to finish on a
contended runner, WITHOUT deselecting them. Both knobs here are application-level (`max_time`,
`subprocess.run(timeout=...)`); neither test has a `@pytest.mark.timeout` marker.

**Tasks**:
- [ ] `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` line ~234
      (inside `_build_example`'s `example_case` settings dict): raise `'max_time': 30` to
      `'max_time': 60`. Update the adjacent explanatory comment to record the new value and that
      it was raised because CI contention caused Z3 to hit the cap and return an unsatisfiable
      first model, inverting the `z3_model_status` assertion into a false negative
- [ ] `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py`: in
      `test_theory_library_execution`'s generated temp module, add an explicit `"max_time": 10` to
      the per-example settings dict inside `example_range` -- i.e. `{"N": 2}` becomes
      `{"N": 2, "max_time": 10}`. Note this goes in the example settings dict, NOT the empty
      `general_settings = {}`. Without it, bimodal's 1-second default applies and the theory
      prints `TIMEOUT: Model search exceeded maximum time of {max_time} seconds` instead of the
      expected `World Histories` table
- [ ] `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py` line ~44: raise
      `run_dev_cli`'s `subprocess.run(..., timeout=15)` to `timeout=30`, and update the trailing
      comment (currently "Prevent hanging - reduced timeout for faster tests") to record that the
      outer guard must stay comfortably ahead of the inner `max_time` plus interpreter
      startup/import overhead
- [ ] Do NOT add `@pytest.mark.performance` to either test -- both are correctness tests

**Timing**: 45 minutes

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: Exactly three edit sites across two files (one `max_time` raise, one
`max_time` addition, one `subprocess.run` timeout raise). Confirm at implementation time by
grepping each file for `max_time` and `timeout=` and checking no other occurrence in these two
files governs either failing test; note `run_dev_cli` is shared by other tests in
`test_full_pipeline.py`, so the `timeout=30` raise intentionally affects all of them (a raise is
strictly safer for every caller, but confirm no sibling test asserts on the old 15s bound).

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` - raise `max_time` 30 -> 60 in the shared `_build_example` fixture
- `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py` - add `max_time` to the generated example, raise the outer subprocess timeout 15 -> 30

**Verification**:
- Invariant check: the new outer timeout (30s) strictly exceeds the new inner `max_time` (10s) plus interpreter startup and import overhead -- state the measured overhead from the local run
- `cd code && PYTHONPATH=src python -m pytest src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py -v` passes, including `test_iterate_two_produces_distinct_models`
- `cd code && PYTHONPATH=src python -m pytest src/model_checker/builder/tests/e2e/test_full_pipeline.py -v` passes, including `test_theory_library_execution`; the captured stdout contains `World Histories` and does NOT contain `TIMEOUT: Model search exceeded`
- `grep -rn "@pytest.mark.performance" code/` still returns exactly two lines (the Phase 2 pair) -- neither of these tests gained the marker

---

### Phase 5: Raise the pre-existing differential-tests timeout [NOT STARTED]

**Goal**: Give `TestGatingConclusiveScan::test_known_conclusive_population_self_consistent` a
budget that reflects its observed 620s runtime, without marking it `slow` (which would silently
drop the scan from every regular gating run). Lowest priority; NOT release-blocking and NOT a
regression from the CI-gate work.

**Tasks**:
- [ ] `.github/workflows/differential-tests.yml` line 38 (the FIRST/broad pytest step,
      `-m "not slow and not differential"`): raise `--timeout=300` to `--timeout=900`
- [ ] Add a brief comment at that step recording why: the failing scan is `xdist_serial` (it
      already runs alone, so this is a genuine budget-too-tight issue rather than worker
      contention), does real re-solving work, and is deliberately unmarked so it runs every
      gating pass
- [ ] Leave line 52 (the explicit six-class step) at `--timeout=300` -- its class list does not
      include `TestGatingConclusiveScan` and it is unaffected
- [ ] Do NOT add `@pytest.mark.slow` to `TestGatingConclusiveScan`

**Timing**: 15 minutes

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: Exactly one of the two `--timeout=300` occurrences in
`differential-tests.yml` needs to change. Confirm at implementation time with
`grep -n "timeout=300" .github/workflows/differential-tests.yml` (expect exactly two hits) and by
reading the second step's explicit class list to reconfirm `TestGatingConclusiveScan` is absent
from it.

**Files to modify**:
- `.github/workflows/differential-tests.yml` - raise the broad step's `--timeout` only

**Verification**:
- `python -c "import yaml; yaml.safe_load(open('.github/workflows/differential-tests.yml'))"` parses
- `grep -n "timeout=" .github/workflows/differential-tests.yml` shows `--timeout=900` on the broad step and `--timeout=300` still on the explicit-class step
- `grep -n "mark.slow" oracle/bimodal_logic/tests/test_cross_oracle_differential.py` confirms `TestGatingConclusiveScan` (line ~2324) still carries no `slow` marker

---

### Phase 6: Consolidated local verification and readiness report [NOT STARTED]

**Goal**: Run the full affected surface locally, then report the fixes as READY -- naming exactly
which workflow runs the user must observe -- without claiming CI-green.

**Tasks**:
- [ ] Run the full CI selector locally exactly as the gate will:
      `cd code && PYTHONPATH=src python -m pytest tests/ src/model_checker -m "not packaging and not performance" -n 6 -q`
- [ ] Record the passed count and confirm it is exactly 2 lower than the pre-change baseline
      (2002 -> 2000), accounting for the two deselected performance tests and nothing else
- [ ] Confirm the two deselected tests still PASS when explicitly selected on this quiet host:
      `cd code && PYTHONPATH=src python -m pytest -m performance src/model_checker tests -v`
- [ ] Run `git diff --stat` and confirm the changed-file set is exactly the nine files this plan
      names, with no production/library code among them
- [ ] Clear stale build output so the wheel glob is unambiguous: `rm -rf code/dist` (this is
      gitignored, regenerable build output -- `.gitignore:13` is `**/dist`; the currently-present
      1.3.0 artifacts date from a prior build and their hashes are already recorded under
      `specs/archive/125_release_engineering_and_pypi_rehearsal/`)
- [ ] Build the wheel locally the way Class 1's failure mode actually surfaces:
      `cd code && python -m build --no-isolation`. Run this from the **ambient shell, NOT inside
      `nix develop`** -- the flake devShell has no `build`/`wheel`/`check-wheel-contents`.
      `--no-isolation` is required, not incidental: it deliberately does not provision
      `build-system.requires` (`["setuptools>=42", "wheel"]`), so it reproduces the exact
      `ERROR Missing dependencies: wheel` condition that Phase 1 fixes. A zero exit here is the
      direct local observation that the Class 1 remedy works
- [ ] Lint the wheel that build just produced: `check-wheel-contents code/dist/*.whl`.
      **Expect exit 1** with the pre-existing `W002: Wheel contains duplicate files` naming the
      four identical `theory_lib/{bimodal,exclusion,imposition,logos}/VERSION` files. Per the
      Non-blocking contract below this is NOT a phase failure
- [ ] Re-run as `check-wheel-contents --ignore W002 code/dist/*.whl` to isolate the "is there
      anything NEW?" signal. Expect `OK` and exit 0. If this second run reports anything beyond
      `OK`, that IS a new finding worth surfacing prominently in the readiness report (still as
      information, not as a phase failure)
- [ ] Record both `check-wheel-contents` invocations verbatim -- command, exit code, and full
      output -- in the summary artifact. Do NOT fix the W002 duplicate `VERSION` files under this
      task; see the Non-blocking contract
- [ ] Confirm `git status --porcelain` still shows no `code/dist` entry after building, proving
      the build did not perturb the nine-path change set
- [ ] Write the summary artifact stating: (i) what changed per class, (ii) that local green is
      NECESSARY BUT NOT SUFFICIENT evidence here -- this task exists precisely because local green
      did not predict CI green, (iii) the explicit statement that CI-green is NOT being claimed,
      (iv) the local `python -m build --no-isolation` result and both `check-wheel-contents`
      runs, with the W002 finding reported as pre-existing and explicitly OUT OF SCOPE for this
      task. Note that (iv) STRENGTHENS but does not upgrade (ii): a locally-built, locally-linted
      wheel is still local evidence, and says nothing about whether the CI runner's install step
      now provisions `wheel` correctly
- [ ] Name the workflow runs the user should check after they push:
      `.github/workflows/packaging.yml` (Class 1), `.github/workflows/tests.yml` -- BOTH the
      `general-tests` matrix and the `flake-check` job (Classes 1-interaction and 2a), and
      `.github/workflows/differential-tests.yml` (Class 3)
- [ ] State that `.github/workflows/release.yml` cannot be observed without a tag push, which is
      user-only; its `build`-job fix is evidenced by static inspection (identical
      `pip install ... build` + `python -m build` shape to `packaging.yml`) plus the fact that a
      green `packaging.yml` run exercises the same failure mode
- [ ] MUST NOT: push a branch, open a PR, invoke `/merge`, or tag. MUST NOT claim any CI run
      passed. MUST NOT commit anything under `code/dist/`

#### Non-blocking contract for `check-wheel-contents`

`check-wheel-contents` is a **strengthening of local verification, not a gate**. It is wired in
because Phase 1 adds `wheel` to the install lists precisely so `python -m build --no-isolation`
succeeds; linting the wheel that build then produces is a stronger observation of the Class 1 fix
actually working than merely observing a zero exit code from build. That is the whole of its job
here.

Binding rules:

- A non-zero exit from `check-wheel-contents` **MUST NOT** fail Phase 6, and MUST NOT be
  described as a regression. Its exit 1 on the current tree is *expected* and was measured at
  revision time.
- Task 155's Class 1 remedy is the `wheel` install-list fix, **not** wheel-content cleanliness.
  Pre-existing wheel-content findings are **reported, not fixed**, under this task.
- Specifically: do NOT deduplicate, consolidate, symlink, or otherwise touch the four
  `theory_lib/*/VERSION` files to silence W002. Those files are per-theory version markers whose
  contents legitimately coincide (all `1.0.0`); changing them is production-tree surgery, is
  outside this task's non-goal of "changing any production/library code", and would need its own
  task with its own reasoning about per-theory versioning.
- The only outcome that changes Phase 6's *reporting* (never its pass/fail) is the
  `--ignore W002` run returning something other than `OK` -- that would indicate a finding not
  accounted for at revision time and must be surfaced prominently.

**Timing**: 45 minutes

**Depends on**: 1, 2, 3, 4, 5

**Verification Tier**: full

**Scope Hypothesis**: The complete change set is nine files:
`.github/workflows/packaging.yml`, `.github/workflows/release.yml`,
`.github/workflows/tests.yml`, `.github/workflows/differential-tests.yml`, `flake.nix`,
`code/src/model_checker/builder/tests/test_refactoring_target_behavior.py`,
`code/tests/integration/test_performance.py`,
`code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py`, and
`code/src/model_checker/builder/tests/e2e/test_full_pipeline.py` -- nine paths, no
production/library code. Confirm with `git diff --name-only` and reconcile against this list; any
extra path is a deviation to explain, any missing path is an incomplete phase.

The nine-path invariant is unaffected by this phase's local build. `python -m build` writes only
to `code/dist/`, which `.gitignore:13` (`**/dist`) excludes, so it cannot appear in
`git diff --name-only`. Verified at revision time. If `code/dist` ever DOES show up in
`git status --porcelain`, treat that as a `.gitignore` regression to report -- not as a path to
stage.

**Files to modify**:
- `specs/155_fix_ci_failures_wheel_dep_and_timing_gated_tests/summaries/01_ci-fixes-summary.md` - implementation summary and readiness report

**Verification**:
- The full-selector local run completes with 0 failures
- The passed-count delta versus baseline is exactly -2 and is attributed to the two named tests
- `git diff --name-only` matches the nine-path list above with no production/library code
- `cd code && python -m build --no-isolation` exits 0 and produces both a `.whl` and a `.tar.gz`
  under `code/dist/`, run from the ambient shell (not `nix develop`)
- `check-wheel-contents code/dist/*.whl` has been run and its command, exit code, and full output
  recorded in the summary -- with exit 1 on the known W002 accepted as expected, not a failure
- `check-wheel-contents --ignore W002 code/dist/*.whl` returns `OK` (exit 0), confirming no
  wheel-content finding beyond the one known at revision time
- The summary reports the W002 duplicate-`VERSION` finding as pre-existing and out of scope, and
  the four `theory_lib/*/VERSION` files are unmodified (`git diff --name-only` shows none of them)
- `git status --porcelain` shows no `code/dist` entry, and nothing under `code/dist/` is staged
  or committed
- The summary contains an explicit "CI-green is not claimed" statement and the named workflow list
- `git log` for this task contains no push, no PR, and no tag operation

---

## Testing & Validation

- [ ] Both `.github/workflows/packaging.yml` and `.github/workflows/release.yml` parse as YAML and their `pip install` lines include `wheel` wherever `python -m build` follows
- [ ] `release.yml`'s `test-and-release` job install line (line 51) is unchanged
- [ ] `grep -rn "@pytest.mark.performance" code/` returns exactly two lines
- [ ] `pytest --collect-only -m performance` collects exactly the two named node IDs, with no unknown-marker warning
- [ ] Both `.github/workflows/tests.yml` and `flake.nix` carry the identical extended selector `-m "not packaging and not performance"`; no bare `-m "not packaging"` remains anywhere
- [ ] `flake.nix` still parses (`nix flake check --no-build` or `nix-instantiate --parse`)
- [ ] `test_iterate_two_produces_distinct_models` passes with `max_time: 60`
- [ ] `test_theory_library_execution` passes; its stdout contains `World Histories` and not `TIMEOUT: Model search exceeded`
- [ ] The full CI selector run is green locally and the count delta versus baseline is exactly -2
- [ ] `differential-tests.yml`'s broad step reads `--timeout=900` and its explicit-class step still reads `--timeout=300`
- [ ] `cd code && python -m build --no-isolation` exits 0 from the ambient shell, producing a wheel and an sdist
- [ ] `check-wheel-contents code/dist/*.whl` was run and fully recorded; its expected exit 1 on the pre-existing W002 is not treated as a phase failure
- [ ] `check-wheel-contents --ignore W002 code/dist/*.whl` returns `OK`, showing no finding beyond the one known at revision time
- [ ] The four `theory_lib/*/VERSION` files are unmodified -- W002 is reported, not fixed
- [ ] Nothing under `code/dist/` is staged or committed
- [ ] No production or library code appears in `git diff --name-only`

## Artifacts & Outputs

- `specs/155_fix_ci_failures_wheel_dep_and_timing_gated_tests/plans/01_ci-fixes-wheel-and-timing.md` (this file)
- `specs/155_fix_ci_failures_wheel_dep_and_timing_gated_tests/summaries/01_ci-fixes-summary.md` (Phase 6)
- Modified: `.github/workflows/packaging.yml`, `.github/workflows/release.yml`, `.github/workflows/tests.yml`, `.github/workflows/differential-tests.yml`, `flake.nix`
- Modified: `code/src/model_checker/builder/tests/test_refactoring_target_behavior.py`, `code/tests/integration/test_performance.py`, `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py`, `code/src/model_checker/builder/tests/e2e/test_full_pipeline.py`
- Transient, NOT committed: `code/dist/*.whl` and `code/dist/*.tar.gz` rebuilt in Phase 6 as
  local evidence for the Class 1 fix. Gitignored via `.gitignore:13` (`**/dist`); the evidence
  that persists is the recorded command output in the summary, not the binaries.

## Rollback/Contingency

- Every phase is an independent, small, per-file commit (Phases 1 and 3 are two-file atomic
  batches), so any single phase can be reverted with `git revert` of its commit without
  disturbing the others.
- If the Phase 3 selector change proves wrong, reverting it alone restores the prior gate behavior
  while leaving the Phase 2 markers harmlessly in place (an applied-but-unselected marker changes
  nothing).
- If the Phase 4 budget raises prove insufficient under CI, the contingency is a further raise --
  never a deselect, since these are correctness tests.
- Phase 5 is fully independent and NOT release-blocking; it may be dropped or reverted entirely
  without affecting Classes 1 or 2. If 900s still proves insufficient, the documented fallback is
  marking `TestGatingConclusiveScan` `@pytest.mark.slow` (manual-only), matching the existing
  `TestFullScanReport` / `TestBimodalHarnessIntegration` precedent.
- Phase 1 is the release-blocking fix; if any later phase must be abandoned, Phase 1 must still
  land.
- Phase 6's build-and-lint step has no rollback surface: it writes only to gitignored
  `code/dist/` and modifies no tracked file. If `check-wheel-contents` turns out to be
  unavailable at implementation time (e.g. the nix profile changed), drop the two lint bullets
  and record their absence in the summary -- the `python -m build --no-isolation` observation
  alone still verifies the Class 1 fix, which is what the original plan relied on. The lint is
  additive evidence, so losing it degrades the readiness report rather than blocking the phase.
