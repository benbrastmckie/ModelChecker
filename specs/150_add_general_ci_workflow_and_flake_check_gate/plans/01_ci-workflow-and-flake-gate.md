# Implementation Plan: Task #150

- **Task**: 150 - add_general_ci_workflow_and_flake_check_gate
- **Status**: [IMPLEMENTING]
- **Effort**: 4 hours
- **Dependencies**: None (tasks 148 and 149 are COMPLETED)
- **Research Inputs**: `specs/150_add_general_ci_workflow_and_flake_check_gate/reports/01_ci-workflow-and-flake-gate.md`
- **Artifacts**: plans/01_ci-workflow-and-flake-gate.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

Close the "nothing runs the general test suite on an ordinary push/PR" gap by adding one new
GitHub Actions workflow (`.github/workflows/tests.yml`) that runs `code/tests/` and
`code/src/model_checker` at `-n 6` with `-m "not packaging"` on `ubuntu-latest` across Python
3.10/3.11/3.12, plus a companion `nix flake check` job. In the same task, correct `flake.nix`:
its `checks.default` derivation is scoped to the bimodal suite alone on the strength of a
justification (28 pre-existing "everything-else" failures) that a live measured re-run shows is
no longer true, so the scope and the comment both need fixing — and the broadening requires a
`devPython` dependency fix that must land first or it lands red. Finally, close the two now-
answered `specs/ROADMAP.md` Phase 1 items. Definition of done: all edits committed locally, every
phase verified by a command actually run on this host, and no branch pushed and no PR opened.

### Research Integration

The plan is built on `reports/01_ci-workflow-and-flake-gate.md`, which corrects the task
description in two places and supplies five load-bearing measurements:

1. **The 28-failure claim does not reproduce.** `code/tests/` + `code/src/model_checker`, minus
   `bimodal/tests`, minus the `packaging` marker, at `-n 6`: **1700 passed, 254 skipped, 0 failed,
   0 errors in 74.10s**. `flake.nix:100-106`'s justification for the bimodal-only scope is
   therefore false and must be corrected rather than propagated.
2. **The task description's workflow inventory is stale.** `.github/workflows/packaging.yml`
   already exists and runs `code/tests/packaging/` serially on every push/PR. The new workflow
   must not duplicate it, and empirically cannot: running packaging tests under `-n 6` alongside
   the rest reproduced **86 spurious errors** from a wheel/sdist build race across xdist workers.
   Hence `-m "not packaging"` on every invocation that touches `code/tests/`.
3. **`nix flake check` passes cleanly today**: "all checks passed!", 2m32s warm-cache wall-clock.
4. **Broadening `checks.default` will produce genuine `AttributeError`s (not skips)** in
   `code/src/model_checker/jupyter/tests/integration/test_widget_interaction.py` unless
   `ipywidgets` (and `matplotlib`) are added to `flake.nix`'s `devPython`, because
   `unittest.mock.patch` requires the target attribute to pre-exist. Phase 1 lands that fix before
   Phase 2 broadens the check.
5. **The oracle differential-suite cadence needs no new job.** The exhaustive complexity-5 scan
   and `TestBimodalHarnessIntegration` were deliberately designed as manual-only/self-skipping;
   this is a decided non-goal, not an open question.

Additional detail confirmed while planning (not in the report): `code/tests/packaging/conftest.py`
imports only stdlib at module level (`build` is imported lazily inside fixtures), so `-m "not
packaging"` alone is sufficient — collection of that directory does not require a build toolchain.
`--ignore=tests/packaging` remains available as a belt-and-suspenders fallback if collection ever
does break.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` Phase 1 items advanced by this plan:

- **"Add `nix flake check` as a CI gate job"** — closed by Phases 2 and 3 together (the flake's
  check becomes meaningful in scope, and a CI job runs it on every push/PR).
- **"Follow-up task for the 28 documented 'everything-else' failures"** — closed by Phase 5 as
  *resolved, not reproducing*, superseded by the core/theory_lib boundary refactor. The Category
  B/G `"A[]"` literal and all six other categories no longer fail.
- **"Oracle differential-suite cadence decision"** — recorded as a decided non-goal (see Non-Goals);
  this plan does not modify `differential-tests.yml`. Whether to also annotate that ROADMAP item as
  answered is left to Phase 5's discretion and is not a required deliverable.

## Goals & Non-Goals

**Goals**:

- Add `.github/workflows/tests.yml`: push/PR-triggered, `ubuntu-latest` x Python 3.10/3.11/3.12,
  running `code/tests/` and `code/src/model_checker` at `-n 6` with `-m "not packaging"`, plus a
  single-instance `nix flake check` job with Nix store caching.
- State the narrower-than-release matrix rationale, the `-m "not packaging"` rationale, and the
  `-n 6`-never-`-n auto` rationale **in the workflow file's own comments**, so the next editor does
  not silently re-widen them.
- Broaden `flake.nix`'s `checks.default` beyond bimodal-only and replace the now-false justifying
  comment at `flake.nix:100-106` with an accurate one.
- Add the `ipywidgets`/`matplotlib` dependencies that broadening requires, in a phase that lands
  before the broadening.
- Update `.github/workflows/README.md` so the new workflow and its scoping decisions are documented.
- Close the two answered `specs/ROADMAP.md` Phase 1 items.

**Non-Goals**:

- **No branch push, no PR, no `/merge`.** Per `.claude/rules/pr-prohibition.md`, every change is
  authored and committed locally only. No phase may run `git push`, `gh pr create`, or `glab mr create`.
- **No claim of observed CI-green.** The implementation cannot watch these workflows run on GitHub.
  Verification is strictly local (see "Local-only verification contract" below).
- No new nightly/scheduled job for the oracle differential suite — already deliberately designed as
  manual-only.
- No changes to `differential-tests.yml`, `packaging.yml`, or `release.yml`.
- No re-running or re-triaging of the 28 historical failures beyond citing the report's measurement.
- No fixing of task-number references in `flake.nix` comments outside the `100-106` block being
  rewritten (e.g. the `bimodalHarnessSrc` comment's "task-122 baseline" citation) — out of scope.

### Local-only verification contract

Every phase below states a command that runs on this host. None of them observe GitHub Actions.
The implementer MUST NOT write, in a commit message, a summary, or the workflow file, any claim
that the new workflow "passes CI", "is green", or "was verified on GitHub". The verifiable claims
are exactly three, and each phase names which it is relying on:

1. **YAML validity / lint** — `python -c "import yaml,sys; yaml.safe_load(open(...))"`, plus
   `actionlint` if it is available on PATH (`command -v actionlint`); if it is not available, say
   so explicitly rather than silently skipping.
2. **Selector equivalence** — running the *exact* pytest selector strings the workflow contains,
   directly, on this host, and reporting the observed pass/skip/fail counts.
3. **`nix flake check`** — the real thing, ~2.5 min warm, run locally.

Anything beyond those three is unverified and must be labelled as such.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Broadening `checks.default` without the jupyter deps lands a red flake gate | H | H (certain if skipped) | Phase 1 adds `ipywidgets`/`matplotlib` and is a hard prerequisite of Phase 2; Phase 2 cannot start until Phase 1's `nix develop` verification passes |
| `code/tests/` proves hostile to the Nix sandbox (subprocess CLI tests, HOME/network assumptions) inside `checks.default` | M | M | Phase 2 carries a documented fallback: scope the broadened check to `src/model_checker` only (still a large widening from bimodal-only), record the exclusion via `[COMPLETED WITH EXCLUSIONS]` with the failing output as Evidence. Do not force it green by weakening assertions |
| Someone later "simplifies" the workflow by dropping `-m "not packaging"`, reintroducing the 86-error build race | M | M | Phase 3 requires an in-file comment naming the race and pointing at `packaging.yml`'s deliberately-serial design; Phase 4 repeats it in the workflows README |
| `-n auto` creeping in and reviving the documented CPU-contention flake | M | L | `-n 6` written literally, with an in-file comment stating `-n auto` is prohibited here |
| Cold Nix builds on a GitHub runner inflate the flake job far past the local 2m32s | L | H | Generous job timeout (25-30 min) plus a Nix store cache action; explicitly commented as an unverified-until-observed estimate |
| Task-number references leaking into deliverable files outside `specs/**` | L | M | Phase 3/4/5 task lists forbid "task N" citations in `.github/**` and `flake.nix`; cite durable anchors (`code/tests/packaging/`, the `packaging` marker, `packaging.yml`) instead, per `.claude/rules/no-task-references-in-deliverables.md` |
| An agent pushing a branch or opening a PR to "verify CI" | H | L | Stated as a Non-Goal and repeated in Phase 3's task list; `.claude/rules/pr-prohibition.md` governs |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 3 | -- |
| 2 | 2, 4 | 1 (for 2), 3 (for 4) |
| 3 | 5 | 2, 3 |

Phases within the same wave can execute in parallel. Phases 1 and 3 touch disjoint files
(`flake.nix` vs `.github/workflows/tests.yml`) and may be run concurrently; Phase 2 must never
start before Phase 1 is green.

---

### Phase 1: Add jupyter test dependencies to flake devPython [COMPLETED]

**Goal**: Make `ipywidgets` and `matplotlib` available in `flake.nix`'s `devPython` so that
`code/src/model_checker/jupyter/tests/` can run without hard `AttributeError`s, landing this
prerequisite *before* any broadening of `checks.default`.

**Tasks**:
- [x] Add `ipywidgets` and `matplotlib` to the `devPython = python.withPackages (ps: with ps; [...])`
      list in `flake.nix` (currently `nixZ3`, `setuptools`, `pip`, `networkx`, `pytest`,
      `pytest-xdist`, `pytest-timeout`). *(completed)*
- [x] Add a short comment above the two new entries explaining *why* they are required: the jupyter
      integration tests use `unittest.mock.patch('model_checker.jupyter.interactive.widgets', ...)`,
      and `mock.patch` requires the target attribute to already exist — a missing `ipywidgets`
      produces a hard `AttributeError`, not a graceful skip. Do not cite task numbers. *(completed)*
- [x] Confirm both attribute names resolve in this nixpkgs pin (`python312Packages.ipywidgets`,
      `python312Packages.matplotlib`); if either is named differently, use the correct attribute and
      note the deviation. *(completed: both names resolve as-is, no deviation needed)*
- [x] Do NOT touch `checks.default` in this phase. *(completed)*

**Timing**: 0.75 hours

**Depends on**: none

**Verification Tier**: local

**Verification**:
- `nix develop --command python -c "import ipywidgets, matplotlib; print('ok')"` prints `ok`.
- `nix develop --command bash -c 'PYTHONPATH=code/src pytest code/src/model_checker/jupyter/tests -q'`
  completes with zero `AttributeError`s. (Skips are acceptable; a hard error is not.)
- `nix flake check` still reports "all checks passed!" — the bimodal-only check is unchanged by
  this phase, so this is a no-regression confirmation, not the phase's main signal.

**Files to modify**:
- `flake.nix` — extend `devPython`'s package list; add the explanatory comment.

---

### Phase 2: Broaden checks.default and correct its false justification [COMPLETED]

**Goal**: Replace `checks.default`'s bimodal-only `checkPhase` with one covering the full
in-package suite (and `code/tests/`, if the sandbox permits), and rewrite the now-false comment at
`flake.nix:100-106` to state the measured truth.

**Tasks**:
- [x] Rewrite the `checkPhase` to run the broadened selection. Target form, given the derivation's
      `src = ./code` root (so `tests` inside the derivation is the repo's `code/tests`):
      `pytest src/model_checker tests -m "not packaging" -n 6 -q` *(completed)*
- [x] Keep `-n 6`. Do not use `-n auto` — the CPU-contention flake this guards against is documented
      and was corroborated by a measured 1.8x bimodal slowdown under concurrent load. *(completed)*
- [x] Keep the `-m "not packaging"` filter: the packaging suite builds wheels/sdists and is unsafe
      under xdist parallelism (86 spurious build-race errors reproduced), and is already covered
      serially elsewhere. *(completed)*
- [x] Replace the comment block at `flake.nix:100-106` entirely. The new comment must state: (a) the
      check now covers the in-package suite (plus `code/tests/`, if included) rather than bimodal
      alone; (b) the previously-cited "28 documented pre-existing failures" no longer reproduce — a
      measured re-run of that selection produced 1700 passed / 254 skipped / 0 failed / 0 errors at
      `-n 6`; (c) why `packaging`-marked tests are excluded (xdist build race, covered serially by
      the dedicated packaging workflow); (d) why `-n 6` and not `-n auto`. **No task-number
      citations** — reference `code/tests/packaging/`, the `packaging` marker, and
      `.github/workflows/packaging.yml` by name instead. *(completed: the literal string "28
      documented" was paraphrased away per Phase 2's own verification grep)*
- [x] Update the `installPhase`'s `echo "model-checker bimodal suite: green"` message to match the
      new, broader scope. *(completed)*
- [x] Update the `doCheck = false` comment at `flake.nix:47-49`, which currently says the gate is
      "scoped to the known-green bimodal suite", so it does not contradict the new scope. *(completed)*
- [x] If `code/tests/` proves unrunnable inside the Nix sandbox, fall back to
      `pytest src/model_checker -m "not packaging" -n 6 -q`, close the phase as
      `[COMPLETED WITH EXCLUSIONS]`, and record a `#### Reasoned Exclusions` table whose Evidence
      column carries the actual failing output. Do not weaken assertions or add `--ignore` flags
      merely to reach green without recording why. *(not needed — broadened check reached green
      inside the sandbox; see Deviation note below for one additional devPython dependency
      required to get there)*

**Deviation (not a fallback, an additive fix)**: the first `nix flake check` run inside this
sandbox failed with `ModuleNotFoundError: No module named 'typing_extensions'`
(`code/src/model_checker/theory_lib/logos/protocols.py` imports it at module level, but it is not
declared in `code/pyproject.toml`'s dependencies — a pre-existing undeclared-dependency gap in the
package, left unfixed as out of scope for this task). Added `typing-extensions` to `devPython`
alongside `ipywidgets`/`matplotlib` (same class of fix as Phase 1, not a weakening of any
assertion or selector). After that addition, `nix flake check` reported "all checks passed!" with
**2002 passed, 254 skipped, 0 failed, 0 errors in 149.55s** — exactly 1700 (non-bimodal) + 302
(bimodal) = 2002, consistent with the Scope Hypothesis's reference numbers.

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: full

**Scope Hypothesis**: This phase asserts that the broadened `checkPhase` will be green inside the
Nix sandbox, on the strength of a measured 1700-passed/0-failed run performed *outside* the
sandbox in a pip venv. The sandbox differs in three ways that could break it: no network, `HOME`
set to `$TMPDIR`, and a nixpkgs-native `z3` rather than the PyPI `z3-solver` wheel. Confirm at
implementation time by actually running `nix flake check` and reading the reported counts — do not
infer sandbox greenness from the venv measurement. If the counts differ materially from 1700
passed / 254 skipped (plus bimodal's ~302), report the delta rather than rounding it away.

**Verification**:
- `nix flake check` reports "all checks passed!". Budget ~5-10 min for the first run (the broadened
  check runs far more than the previous 302 bimodal tests).
- `nix flake check --show-trace 2>&1 | tail -40` on any failure, to capture the real cause before
  reaching for the fallback.
- `git diff flake.nix` read-through confirming the old "28 documented pre-existing failures"
  sentence is gone from the file: `grep -n "28 documented" flake.nix` returns nothing.
- `grep -niE "task[ -]?[0-9]+" flake.nix` shows no *newly added* task-number citations (pre-existing
  ones outside the rewritten block are out of scope).

**Files to modify**:
- `flake.nix` — `checks.default` `checkPhase` and `installPhase`; the comment block at lines
  100-106; the `doCheck` comment at lines 47-49.

---

### Phase 3: Author the general CI workflow [COMPLETED]

**Goal**: Create `.github/workflows/tests.yml` with a push/PR-triggered general test job and a
`nix flake check` job, and verify locally that its exact selectors are green and its YAML is valid.

**Tasks**:
- [x] Create `.github/workflows/tests.yml` with `on: [push, pull_request]` (unfiltered, matching
      `packaging.yml`'s trigger shape). *(completed)*
- [x] Job A (`general-tests`): `runs-on: ubuntu-latest`, `strategy.matrix.python-version:
      ['3.10', '3.11', '3.12']`, `fail-fast: false`. Steps: checkout, `actions/setup-python@v5`
      with `cache: 'pip'`, install deps (`z3-solver networkx pytest pytest-xdist pytest-timeout
      ipywidgets matplotlib`), then run the suite from `code/` with `-m "not packaging" -n 6`.
      Set a generous `timeout-minutes` (15-20). *(completed: 20; also added `typing-extensions`
      to the install list, see Deviation note below)*
- [x] Job B (`flake-check`): `runs-on: ubuntu-latest`, no matrix (the flake pins its own Python).
      Steps: checkout, a Nix installer action, a Nix store cache action, then `nix flake check`.
      `timeout-minutes: 30`. *(completed: `cachix/install-nix-action@v27` +
      `DeterminateSystems/magic-nix-cache-action@v7`)*
- [x] Write the rationale comments in the file itself:
      - Why `-m "not packaging"`: those tests build wheels/sdists and race under xdist (86 spurious
        errors reproduced); they are already covered serially by `.github/workflows/packaging.yml`
        and by the release pipeline's build job. Do not remove this filter.
      - Why `-n 6` and never `-n auto`: documented CPU-contention flake in the bimodal suite.
      - Why the matrix is `ubuntu-latest` only while the release pipeline uses three OSes: this is a
        fast per-push regression gate, not a cross-platform install check; cross-OS packaging
        breakage is caught at release time and, more cheaply, by the packaging workflow on every push.
      - Why the bimodal suite is deliberately NOT excluded here even though the flake check also
        covers it: the flake exercises the nixpkgs-packaged Z3/Python toolchain while this job
        exercises the PyPI `z3-solver` users actually install — deliberate cross-toolchain coverage,
        not duplication.
      - That the Nix job's timeout is an estimate from a 2m32s warm-cache local run and has not been
        observed on a cold runner.
      *(completed — all five points present in the file's own comments)*
- [x] **No task-number citations anywhere in this file** — cite paths, marker names, and workflow
      filenames. *(completed)*
- [x] **Do not push a branch and do not open a PR.** Commit locally only. *(completed)*

**Deviation (not a fallback, an additive fix)**: the initial selector run against a freshly
provisioned venv matching the workflow's exact `pip install` list reproduced the identical
`ModuleNotFoundError: No module named 'typing_extensions'` discovered in Phase 2. Added
`typing-extensions` to the workflow's `pip install` step (same undeclared-dependency root cause,
same fix class — not a weakened assertion or narrowed selector).

**Timing**: 1.25 hours

**Depends on**: none

**Verification Tier**: full

**Scope Hypothesis**: This phase asserts the selectors it writes are green and asserts approximate
counts (~1700+ passed for the non-bimodal selection, ~302 for bimodal, ~468 for `code/tests/`).
Confirm by running the exact selector strings from the file — copy them out of the YAML rather than
retyping — and report the observed counts. Treat any nonzero failure count as a blocker for closing
this phase, not as a workflow-authoring detail to be resolved later in CI.

**Verification**:
- YAML parses: `python -c "import yaml; yaml.safe_load(open('.github/workflows/tests.yml')); print('ok')"`
  — `ok`. *(passed)*
- Lint if available: `command -v actionlint && actionlint .github/workflows/tests.yml`; if
  `actionlint` is absent, state that explicitly in the phase notes rather than omitting the step.
  **`actionlint` is not present on PATH on this host — stated explicitly, step skipped rather than
  silently omitted**, per the local-only verification contract.
- Selector equivalence, run from `code/` with `PYTHONPATH=src` and
  `LD_LIBRARY_PATH="$(nix eval --raw nixpkgs#stdenv.cc.cc.lib)/lib"` (needed on this NixOS host for
  a pip-installed `z3-solver` to resolve `libstdc++.so.6`), against a venv provisioned with the
  workflow's *exact* `pip install` line:
  - `pytest tests/ -m "not packaging" -n 6 -q` — **354 passed, 0 failed, 0 errors, 16.6s**. (The
    plan's "~468-4 skipped" estimate was for the *unfiltered* `code/tests/` tree, which includes
    the ~108+ packaging-marked tests this selector excludes entirely; 354 is consistent with that
    delta, not a regression — reported per the Scope Hypothesis's "report the delta" instruction.)
  - `pytest src/model_checker -m "not packaging" -n 6 -q` — **1648 passed, 254 skipped, 0 failed, 0
    errors, 102.5s** (bimodal included). 1648 + 354 = 2002, exactly matching Phase 2's `nix flake
    check` total (`src/model_checker tests -m "not packaging" -n 6` inside the sandbox), a strong
    cross-check that both selectors are internally consistent.
- No `-n auto` anywhere in the file: `grep -n "n auto" .github/workflows/tests.yml` returns nothing.
  *(passed, after rewording one comment that originally contained the literal substring)*
- No push occurred: `git log origin/master..HEAD --oneline` shows the new commits are local only
  (a long pre-existing list of unpushed local commits, unrelated to this task), and
  `git reflog | grep -i push` shows no push from this session. *(passed)*

**Files to modify**:
- `.github/workflows/tests.yml` — new file.

---

### Phase 4: Document the new workflow and its scoping decisions [NOT STARTED]

**Goal**: Add `tests.yml` to `.github/workflows/README.md` alongside the three existing workflows,
recording the *why* of each scoping decision so the next editor does not re-derive it.

**Tasks**:
- [ ] Add a `tests.yml` bullet to the `## Workflows` list, describing its trigger, selection, matrix,
      and the `nix flake check` job.
- [ ] Add a short "Scoping rationale" subsection covering: why packaging tests run serially and only
      in their own workflow; why the general gate excludes the `packaging` marker; why the general
      gate uses a narrower matrix than the release pipeline; why `-n 6` and never `-n auto`; and why
      bimodal is covered by both the plain-Python job and the flake check (cross-toolchain, not
      redundant).
- [ ] Mention that `checks.default` in `flake.nix` is no longer bimodal-scoped (consistent with
      Phase 2's outcome), keeping the README and the flake in agreement.
- [ ] No task-number citations.

**Timing**: 0.5 hours

**Depends on**: 3

**Verification Tier**: prose

**Verification**:
- Diff read-through confirming every changed hunk lies inside markdown prose in
  `.github/workflows/README.md` and no other file was touched.
- Every workflow filename mentioned exists: `ls .github/workflows/` cross-checked against the
  README's bullet list (4 workflows: `release.yml`, `packaging.yml`, `differential-tests.yml`,
  `tests.yml`).
- `grep -niE "task[ -]?[0-9]+" .github/workflows/README.md` returns nothing newly added.

**Files to modify**:
- `.github/workflows/README.md` — new `tests.yml` entry and scoping-rationale subsection.

---

### Phase 5: Close the two answered ROADMAP items [NOT STARTED]

**Goal**: Mark the `nix flake check` CI-gate item and the 28-failures follow-up item complete in
`specs/ROADMAP.md`, with accurate annotations.

**Tasks**:
- [ ] Change the `- [ ] **Add `nix flake check` as a CI gate job**` item to `- [x]` with a completion
      annotation `*(Completed: Task 150, 20260812)*` and a one-line note that `tests.yml` now runs
      `nix flake check` on every push/PR and that `checks.default` was broadened beyond the
      bimodal-only scope. (`specs/**` is exempt from the no-task-references rule, so the task-number
      annotation is correct *here* and only here.)
- [ ] Change the `- [ ] **Follow-up task for the 28 documented "everything-else" failures**` item to
      `- [x]` with the same completion annotation, and rewrite its body to state the resolution:
      **resolved, not reproducing.** A measured re-run of the same selection
      (`code/tests/ code/src/model_checker --ignore=.../bimodal/tests -m "not packaging" -n 6`)
      produced 1700 passed / 254 skipped / 0 failed / 0 errors in 74.10s. All eight root-cause
      categories, including the Category B/G malformed `"A[]"` literal in
      `code/tests/utils/helpers.py`, were resolved as a side effect of the core/theory_lib boundary
      refactor and the CLI end-to-end suite's rewrite of `test_batch_output_real.py`. Cite
      `specs/150_add_general_ci_workflow_and_flake_check_gate/reports/01_ci-workflow-and-flake-gate.md`
      as the measurement source.
- [ ] Do NOT close the "Oracle differential-suite cadence decision" item as part of this task's
      required scope; if annotating it, annotate only that the exhaustive/harness-dependent tests
      were already designed as manual-only and no new scheduled job is warranted.
- [ ] Do not renumber, reorder, or reformat unrelated ROADMAP items.

**Timing**: 0.5 hours

**Depends on**: 2, 3

**Verification Tier**: prose

**Verification**:
- `grep -n "nix flake check\` as a CI gate" specs/ROADMAP.md` shows the item now begins `- [x]`.
- `grep -n "28 documented" specs/ROADMAP.md` shows the item now begins `- [x]` and its body states
  the not-reproducing resolution.
- `git diff specs/ROADMAP.md` read-through confirming only those two items (and their bodies)
  changed — no unrelated hunks.
- Both claims being closed are true as of this commit: `.github/workflows/tests.yml` contains a
  `nix flake check` step (`grep -n "flake check" .github/workflows/tests.yml`), and `flake.nix` no
  longer restricts `checks.default` to `theory_lib/bimodal/tests`
  (`grep -n "theory_lib/bimodal/tests" flake.nix` returns nothing inside `checkPhase`).

**Files to modify**:
- `specs/ROADMAP.md` — two Phase 1 checklist items.

---

## Testing & Validation

- [ ] `nix develop --command python -c "import ipywidgets, matplotlib"` succeeds (Phase 1).
- [ ] `nix flake check` reports "all checks passed!" against the broadened `checks.default` (Phase 2).
- [ ] `pytest code/tests/ -m "not packaging" -n 6 -q` — 0 failed (Phase 3).
- [ ] `pytest code/src/model_checker -m "not packaging" -n 6 -q` — 0 failed, bimodal included (Phase 3).
- [ ] `.github/workflows/tests.yml` parses as YAML; `actionlint` clean if available (Phase 3).
- [ ] `grep -n "n auto" .github/workflows/tests.yml` returns nothing.
- [ ] `grep -n "28 documented" flake.nix` returns nothing.
- [ ] No new task-number citations in `.github/**` or `flake.nix`.
- [ ] No `git push`, no `gh pr create`, no `glab mr create` in the session history.

## Artifacts & Outputs

- `.github/workflows/tests.yml` (new)
- `.github/workflows/README.md` (modified)
- `flake.nix` (modified: `devPython`, `checks.default`, two comment blocks)
- `specs/ROADMAP.md` (modified: two Phase 1 items closed)
- `specs/150_add_general_ci_workflow_and_flake_check_gate/summaries/01_ci-workflow-and-flake-gate-summary.md`

## Rollback/Contingency

- Each phase is a separate commit, so any single phase reverts with `git revert <sha>` without
  disturbing the others.
- **Phase 2 is the only phase that can turn a currently-green local gate red.** If the broadened
  `checks.default` cannot be made green inside the sandbox, prefer the documented fallback (scope to
  `src/model_checker`, record a `#### Reasoned Exclusions` table) over reverting; if even that fails,
  revert Phase 2 alone — Phase 1's dependency addition is harmless on its own and Phases 3-5 do not
  depend on Phase 2's specific `checkPhase` content, only on the broadening having been attempted
  and truthfully described in Phase 5's annotation.
- If Phase 3's selectors are not green locally, do not commit the workflow file claiming they are.
  Report the failures and stop — a workflow asserting a false green is worse than no workflow.
- `.github/workflows/tests.yml` is a new file, so full rollback is `git rm` plus reverting the
  README hunk.
