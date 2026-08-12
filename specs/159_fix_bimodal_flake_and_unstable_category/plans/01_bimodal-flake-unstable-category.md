# Implementation Plan: Fix Bimodal Solver-Timing Flakes and Introduce the `unstable` Test Category

- **Task**: 159 - fix_bimodal_flake_and_unstable_category
- **Status**: [IMPLEMENTING]
- **Effort**: 7.5 hours
- **Dependencies**: None (but MUST NOT run concurrently with the CI-hardening task -- both touch `.github/workflows/tests.yml`, `release.yml`, `differential-tests.yml`)
- **Research Inputs**: `specs/159_fix_bimodal_flake_and_unstable_category/reports/01_bimodal-flake-and-unstable-category.md`
- **Artifacts**: plans/01_bimodal-flake-unstable-category.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Two bimodal test defects are red or intermittently red on CI: the `BM_CM_1` example-case timing
flake in `test_bimodal.py`, and the oracle gating scan's conclusive-population shortfall
(95-96 of 103 against `floor=100`). The primary aim is to FIX them; the new `unstable` marker
is a pressure-release valve for whatever genuinely resists repair, gated behind four strict
entry criteria and a written exit criterion, backed by a non-gating watch workflow so nothing
quarantined disappears from view. Definition of done: both defects have a recorded genuine
repair attempt with measurements; `unstable` exists, is registered in both pytest trees, is
deselected from every gating pytest invocation, and is exercised by a scheduled watch workflow;
the policy is documented in `TESTING_GUIDE.md`; and the conditional follow-up task is created
or its absence justified.

### Research Integration

The research report is the empirical basis for every phase and MUST be cited at each marker
site. Findings carried into this plan:

- **Defect (a) has no available encoding fix.** Three avenues are now closed: `z3.FreshInt`
  substitution and `ForAllTime` pattern/trigger hints (both exhaustively investigated and
  rejected by a prior task, recorded in `_fresh_bound_int`'s docstring and at
  `semantic/core.py:432-460`), and finite unrolling of `ForAllTime`/`ExistsTime` over the
  statically-known time domain (newly tried by this task's research: 4 of 7 seeds sped up
  substantially, but 2 of 7 seeds that decided cleanly under baseline failed to decide at all
  within the same 90s probe -- a regression, not an improvement). The real CI failure landed at
  60.94s against the 60s budget; the settings comment's standing verdict is that no budget
  closes the tail. BM_CM_1 therefore meets all four `unstable` entry criteria.
- **Defect (b) has an untried, evidence-backed repair.** The exact failing test re-ran 103/103
  conclusive locally, twice, both unrestricted (24 cores) and CPU-restricted to 2 cores via
  `taskset` -- so local core restriction does NOT reproduce the shortfall. Two real CI runs show
  96/103 and 95/103, both with **0 disagreements**, both well inside the 900s suite timeout
  (real per-formula degradation, not a timeout artifact). GitHub standard runners are 4 vCPU /
  16 GB. The evidence points at CI hardware/contention, so widening
  `GATING_RECHECK_SOLVE_TIMEOUT_MS` (20000 -> 40000 ms) is a genuine budget recalibration of the
  same class already applied to `BM_CM_1`/`BM_CM_4`, not an assertion weakening.
  `MIN_CONCLUSIVE_GATING_FORMULAS` is NOT lowered.
- **`release.yml` has no pytest gate on the bimodal suite** -- see the Decision below.

### Prior Plan Reference

No prior plan. This task supersedes an earlier framing (withdraw bimodal from the release
surface) that was rejected as disproportionate; no plan artifact was produced under that
framing.

### Roadmap Alignment

No `specs/ROADMAP.md` found; no roadmap phases required.

## Decision: `release.yml` marker wiring (resolved here, not left to the implementer)

Deliverable (4) instructs extending `release.yml`'s `test-and-release` matrix with the
`unstable` deselection. Research established that **`test-and-release` runs no pytest suite at
all** -- it builds the wheel, installs it, smoke-tests import/CLI, and verifies the version
matches the tag (`.github/workflows/release.yml`, "Install and test package" step). There is no
`-m` expression there to extend. The only pytest invocation anywhere in `release.yml` is the
`build` job's `python -m pytest tests/packaging/ -v -m packaging`.

**Decision: hybrid (i)+(ii).**

1. **`test-and-release`: documented no-op.** Add a comment at the "Install and test package"
   step recording that this job deliberately runs no pytest suite, that BM_CM_1 therefore
   cannot gate a release from here, and that **any pytest suite added to this job in future
   MUST carry `not unstable` in its `-m` expression**. No behavioural change.
2. **`build`'s packaging invocation: apply the exclusion defensively.** Change
   `-m packaging` to `-m "packaging and not unstable"`. This is a real pytest invocation on the
   release-gating path; the exclusion is a no-op today (no packaging test is or should be
   `unstable`) but makes the release path structurally incapable of gating on a quarantined
   test.

**Reasoning**: the gate that actually failed on the v1.3.0 tag push was the `Tests` workflow
(`tests.yml`), which runs on tag pushes and does include BM_CM_1 -- that is where the real fix
lands (Phase 5). Editing a non-existent expression in `test-and-release` is impossible; silently
skipping the file leaves the next author to rediscover why. Recording the no-op in-file plus
hardening the one real invocation covers both the letter and the intent of deliverable (4).

## Goals & Non-Goals

**Goals**:
- Record, durably and at the code site, the genuine repair attempts made for both defects and
  exactly what each ruled out, so a future reader starts from the frontier.
- Land a genuine, measurement-justified budget repair for the oracle conclusive-population
  shortfall without lowering `MIN_CONCLUSIVE_GATING_FORMULAS`.
- Introduce `unstable` as a marker with strict, in-line-documented entry criteria and a written
  exit criterion per marked test.
- Deselect `unstable` from every gating pytest invocation across all three workflows.
- Ship `unstable-watch.yml` as a first-class, non-gating observation workflow with trend
  visibility, READY-TO-PROMOTE surfacing, and loud alerting on a new (semantic) failure mode.
- Document the policy (entry, exit, cadence, promotion path, escalation rule) in
  `TESTING_GUIDE.md`.
- Create the conditional follow-up task carrying the frontier forward, or record why none is
  needed.

**Non-Goals**:
- Re-tuning `BM_CM_1`'s `max_time` (the settings comment already records that no budget closes
  the tail; a second recalibration would burn a cycle re-learning that).
- Lowering `MIN_CONCLUSIVE_GATING_FORMULAS` (the assertion encodes a real quality property).
- Adopting the finite-unrolling encoding change (empirically inconclusive-to-negative; would
  require a full soundness and regression pass across the whole bimodal suite for an approach
  not demonstrated to help on net).
- Marking `TestGatingConclusiveScan` `unstable` in this task (the budget repair is attempted
  first; the marker is the documented fallback only if a CI-verified widened budget still falls
  short -- and CI verification is a user action, so this decision belongs to the follow-up).
- Withdrawing bimodal from the release surface (explicitly rejected in the task description).
- Any `git push`, `git tag`, `/merge`, `/tag`, or twine upload -- USER-ONLY per
  `.claude/rules/pr-prohibition.md`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Widening `GATING_RECHECK_SOLVE_TIMEOUT_MS` 20s -> 40s pushes `TestGatingConclusiveScan` past `differential-tests.yml`'s `--timeout=900`. Observed CI: ~620s test runtime with 7-8 formulas timing out at 20s; if those still time out at 40s, add ~140-160s -> ~780s, only ~13% under the 900s per-test cap. | High (turns a countable shortfall into an opaque suite timeout) | Medium | Raise `--timeout` to 1500 in the same phase and same commit as the budget widening. Both edits are in the same phase deliberately. |
| Converting `test_examples.items()` to `pytest.param(...)` silently changes generated node IDs, breaking `-k` selections and the documented node ID `test_example_cases[BM_CM_1-example_case7]`. | High | Medium | Phase 4 verification takes a `--collect-only -q` node ID list before and after and requires a byte-identical diff. |
| `unstable` unregistered in the oracle tree: `oracle/conftest.py` (not `code/pyproject.toml`) is the registration site for `oracle/`-rooted invocations -- `code/pyproject.toml` is a sibling of `oracle/`, never an ancestor, so ini-discovery never reaches it. | Medium (unknown-marker warnings; `--strict-markers` would error) | Medium | Phase 3 registers the marker in BOTH sites, mirroring the existing `differential`/`slow` dual-declaration pattern. |
| `pytest -m unstable` selects zero tests in a tree, exiting with code 5 ("no tests collected") and failing the watch job spuriously. | Medium | High (the oracle tree will have no `unstable` test after this task) | Phase 6 treats exit code 5 as "no unstable tests in this tree" and continues; only codes other than 0 and 5 are failures. |
| The oracle budget fix cannot be verified on real CI within this task (agents cannot push). | Medium | Certain | Phase 2 lands the change plus an explicit, clearly-marked USER ACTION block; the verification obligation is carried into the follow-up task in Phase 8. |
| `unstable-watch.yml` accidentally gates something (it would be the repo's first `schedule:` workflow). | High (defeats the whole point) | Low | Triggers limited to `schedule` + `workflow_dispatch` only -- no `push`, `pull_request`, or `tags`; an in-file comment states the non-gating contract; Phase 6 verification greps the file to confirm no other trigger is present. |
| The `unstable` category becomes a dumping ground. | High (long-term) | Medium | Exactly one test is marked in this task; the four entry criteria are recorded in-line at the marker site and in `TESTING_GUIDE.md` 8.9, together with the standing rule that indefinite quarantine is itself a defect to escalate. |
| Concurrent edits with the CI-hardening task on the three shared workflow files. | High (merge conflict / double-applied edits) | Low | Task description already forbids concurrent runs; Phase 5 re-reads each workflow file immediately before editing and reports if the target expression already carries `not unstable`. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |
| 3 | 4, 5, 6, 7 | 3 |
| 4 | 8 | 1, 2, 3, 4, 5, 6, 7 |

Phases within the same wave can execute in parallel.

Phase ordering enforces the task's primary aim: the genuine repair work for both defects
(Phases 1 and 2) completes before the marker infrastructure exists (Phase 3) and before
anything is quarantined (Phase 4).

---

### Phase 1: Record the BM_CM_1 repair frontier [COMPLETED]

- **Goal:** Durably record, at the code site, every encoding avenue attempted for the
  `\Future`/temporal-quantifier divergent draw and exactly what each ruled out -- satisfying
  entry criterion 3 ("a genuine fix was attempted and its failure recorded") BEFORE any marker
  is applied. No behavioural change.

- **Tasks:**
  - [ ] Read the research report's "Defect (a)" section in full (seed sweep table, the prior
        task's two closed avenues, the new unrolling experiment table, the 60.94s real-CI
        measurement).
  - [ ] Read `code/src/model_checker/theory_lib/bimodal/operators.py`'s `_fresh_bound_int`
        docstring and the in-line notes at `semantic/core.py:432-460` to match their existing
        record-keeping style and avoid restating what is already there.
  - [ ] Extend `_fresh_bound_int`'s docstring (or the adjacent in-line block, whichever the
        existing record occupies) with a third closed avenue: **finite unrolling of
        `ForAllTime`/`ExistsTime` over the statically-known time domain `D = (-M, M)`**. Record
        the method (`z3.substitute(body, (time_var, z3.IntVal(t)))` per valid `t`, replacing the
        `z3.ForAll`/`z3.Exists`; world dimension left quantified), the 7-seed measured outcome
        (seeds 2/3/4/6/7 decided, several substantially faster -- seed 6 7.16s -> 0.23s, seed 2
        45.14s -> 5.88s; seeds 1 and 5 went from deciding under baseline to **not deciding at
        all** within the same 90s probe), and the verdict: not adopted, because it regresses two
        of seven draws and `ForAllTime`/`ExistsTime` are used by every temporal operator, so
        adopting it would require a full soundness and regression pass for an approach not
        demonstrated to help on net.
  - [ ] Extend `BM_CM_1_settings`'s comment in
        `code/src/model_checker/theory_lib/bimodal/examples.py` with the two new empirical
        anchors: the real GitHub Actions failure landing at **60.94s** (just past the 60s
        budget, not near the documented 600s divergent extreme), and this task's independent
        7-seed sweep (4.76s / 47.78s / 1.99s / 7.96s / 11.18s / 6.75s / 16.52s, 7/7 decided,
        genuine countermodel found on every decided draw). Re-affirm, do not re-litigate, the
        existing standing verdict that no budget closes the tail; state explicitly that
        `max_time` is NOT to be re-tuned.
  - [ ] Do not change any executable line in either file.

- **Timing:** 45 minutes

- **Depends on:** none

- **Verification Tier:** prose

- **Scope Hypothesis:** This phase asserts that the BM_CM_1 repair record is confined to exactly
  two files (`operators.py`, `examples.py`) and touches zero executable lines. Confirm at
  implementation time with `git diff --stat` (exactly two files) and a read-through of
  `git diff` confirming every changed hunk lies inside a comment or docstring region. If the
  prior task's record turns out to live at a third site (e.g. `semantic/core.py`'s in-line
  block is the better host than `operators.py`'s docstring), widening to that file is permitted
  -- record the reason in the phase's commit message.

- **Files to modify:**
  - `code/src/model_checker/theory_lib/bimodal/operators.py` - add the unrolling avenue to the
    closed-avenues record
  - `code/src/model_checker/theory_lib/bimodal/examples.py` - add the 60.94s CI datum and this
    task's seed sweep to `BM_CM_1_settings`'s comment

- **Verification:**
  - `git diff` read-through confirms every changed hunk is inside a comment or docstring; no
    executable line changed.
  - `python -c "import model_checker.theory_lib.bimodal.examples, model_checker.theory_lib.bimodal.operators"`
    (with `PYTHONPATH=code/src`) succeeds -- guards against an edit crossing a string boundary.
  - The record names all three closed avenues (FreshInt, patterns/triggers, finite unrolling)
    and, for each, states what was measured rather than merely that it "did not work".

---

### Phase 2: Widen the oracle gating re-check budget (genuine repair for defect (b)) [COMPLETED]

- **Goal:** Land the measurement-justified budget recalibration
  (`GATING_RECHECK_SOLVE_TIMEOUT_MS` 20000 -> 40000 ms) with the same in-comment rigor as
  `BM_CM_1`/`BM_CM_4`, raise the suite `--timeout` so the wider per-formula budget cannot turn a
  countable shortfall into an opaque suite timeout, and stage the CI verification as an explicit
  user action. `MIN_CONCLUSIVE_GATING_FORMULAS` is NOT touched.

- **Tasks:**
  - [ ] Read the research report's "Defect (b)" section and the existing derivation comments
        above `GATING_RECHECK_SOLVE_TIMEOUT_MS` and `MIN_CONCLUSIVE_GATING_FORMULAS` in
        `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`.
  - [ ] Change `GATING_RECHECK_SOLVE_TIMEOUT_MS` from `20000` to `40000`.
  - [ ] Extend its comment with a justification block recording: **method** (re-ran the exact
        failing test locally, unmodified, twice); **local results** (103/103 conclusive, 0
        disagreements, 194.64s unrestricted on 24 cores; 103/103 conclusive, 0 disagreements,
        176.06s under `taskset -c 0,1`); **real CI results** (96/103 with 7 timeouts, run
        `31628414697`; 95/103 with 8 timeouts, run `31628228088`; both 0 disagreements, both
        inside the 900s cap so this is per-formula degradation, not a suite-timeout artifact);
        **what was ruled out** (genuine cost growth in the harness -- 2-core local restriction
        did not reproduce the shortfall at all); **the conclusion** (GitHub standard runners are
        4 vCPU / 16 GB against a 24-core / 30 GB derivation host, so the budget did not transfer
        to CI hardware); and **the multiplier rationale** (2x, matching the
        ~2x-of-measured-worst convention used elsewhere in this codebase). State explicitly that
        the floor was deliberately NOT lowered and why.
  - [ ] Add a clearly-marked `USER ACTION REQUIRED` note in the same comment block: this
        multiplier is **not yet verified on real CI**; verification requires pushing the change
        and running `differential-tests.yml` via `workflow_dispatch` 2-3 times, which is a
        user-only operation per `.claude/rules/pr-prohibition.md`. Record what a successful
        verification looks like (>= 100 of 103 conclusive on every dispatched run, 0
        disagreements) and what to do if it still falls short (do NOT lower the floor; the
        documented fallback is marking `TestGatingConclusiveScan` `unstable` under the same four
        entry criteria -- deferred to the follow-up task).
  - [ ] In `.github/workflows/differential-tests.yml`, raise the first pytest invocation's
        `--timeout=900` to `--timeout=1500` and extend the adjacent comment with the arithmetic:
        observed ~620s test runtime with 7-8 formulas timing out at 20s each; at 40s those add
        ~140-160s, landing near ~780s against a 900s cap (~13% headroom) -- too thin, since a
        suite timeout would destroy the countable evidence this test exists to produce.
  - [ ] Do not modify `MIN_CONCLUSIVE_GATING_FORMULAS`, `SELF_SCAN_SOLVE_TIMEOUT_MS`, the
        manifest, or the exhaustive-scan path.

- **Timing:** 1 hour (plus ~4 minutes of local test runtime)

- **Depends on:** none

- **Verification Tier:** local

- **Scope Hypothesis:** This phase asserts the budget change is a single-constant edit at one
  call-site family (`GATING_RECHECK_SOLVE_TIMEOUT_MS` is documented as used ONLY by
  `TestGatingConclusiveScan`'s two solve call sites). Confirm at implementation time with
  `grep -n GATING_RECHECK_SOLVE_TIMEOUT_MS oracle/bimodal_logic/tests/test_cross_oracle_differential.py`
  -- expect the definition plus exactly two call sites, all inside `TestGatingConclusiveScan`.
  If a third consumer exists, stop and report before editing.

- **Files to modify:**
  - `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` - constant + justification
    comment + USER ACTION note
  - `.github/workflows/differential-tests.yml` - `--timeout=900` -> `--timeout=1500` with
    rationale

- **Verification:**
  - `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestGatingConclusiveScan::test_known_conclusive_population_self_consistent -v`
    still PASSES locally with `conclusive=103/103` and `disagreements=0`. (Widening a budget
    cannot reduce the conclusive count; a drop here means something else changed.)
  - `grep -c MIN_CONCLUSIVE_GATING_FORMULAS` shows the constant's value is still `100`
    (unchanged).
  - `python -c "import yaml,sys; yaml.safe_load(open('.github/workflows/differential-tests.yml'))"`
    parses cleanly.
  - The comment block names measurements, method, and what was ruled out -- the standard set by
    `BM_CM_1_settings`.

---

### Phase 3: Register the `unstable` marker in both pytest trees [COMPLETED]

- **Goal:** Make `unstable` a first-class, registered marker in both marker-registration sites,
  with no test marked yet. Infrastructure only.

- **Tasks:**
  - [ ] Add to `[tool.pytest.ini_options] markers` in `code/pyproject.toml`, following the
        `slow` entry's style (including its in-line explanation of how to select/deselect),
        exactly the text specified in the task description:
        `"unstable: Tests with a documented, investigated non-semantic instability (e.g. a heavy-tailed solver draw). Deselected from release-gating runs with \`-m \"not unstable\"\`; run on their own by the unstable-watch workflow so they stay observed rather than forgotten."`
  - [ ] Add the same marker registration to `oracle/conftest.py`'s `pytest_configure` via
        `config.addinivalue_line("markers", ...)`, mirroring the existing
        `differential`/`slow` dual-declaration pattern. `oracle/conftest.py`'s module docstring
        already explains why this second site is required (`code/pyproject.toml` is a sibling of
        `oracle/`, never an ancestor, so ini-discovery never reaches it); extend that docstring
        to include `unstable` in the list of mirrored declarations so the two do not drift.

- **Timing:** 30 minutes

- **Depends on:** 1, 2

- **Verification Tier:** local

- **Scope Hypothesis:** This phase asserts exactly two registration sites exist. Confirm at
  implementation time by running `grep -rn "addinivalue_line\|^markers = \|markers = \[" --include='*.py' --include='*.toml' --include='*.ini' --include='*.cfg' .`
  from the repo root and checking that no third marker-registration site (a `pytest.ini`,
  `setup.cfg`, or another `conftest.py` calling `addinivalue_line("markers", ...)`) governs any
  tree in the file scope. If a third exists, register there too and record the widening.

- **Files to modify:**
  - `code/pyproject.toml` - add `unstable` to the `markers` list
  - `oracle/conftest.py` - register `unstable` in `pytest_configure`; extend the module
    docstring

- **Verification:**
  - `cd code && pytest --markers | grep unstable` shows the registered description.
  - `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py --markers | grep unstable`
    shows it registered for the oracle tree as well.
  - `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/ -m unstable --collect-only -q`
    collects zero tests without an "unknown marker" warning.
  - `python -c "import tomllib; tomllib.load(open('code/pyproject.toml','rb'))"` parses cleanly
    (the marker text contains escaped quotes and backticks).

---

### Phase 4: Mark BM_CM_1 `unstable` with the four entry criteria in-line [NOT STARTED]

- **Goal:** Quarantine exactly one test -- `test_example_cases[BM_CM_1-example_case7]` -- with
  all four strict entry criteria and an explicit written EXIT criterion recorded in-line at the
  marker site, and with node IDs provably unchanged.

- **Tasks:**
  - [ ] Capture the pre-change collection baseline:
        `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py --collect-only -q > /tmp/ids-before.txt`.
  - [ ] Convert the `@pytest.mark.parametrize("example_name, example_case", test_examples.items())`
        argument from a bare `.items()` view into an explicit list of `pytest.param(name, case,
        marks=[pytest.mark.unstable] if name in UNSTABLE_EXAMPLES else [])` -- introducing a
        module-level `UNSTABLE_EXAMPLES = {"BM_CM_1"}` set alongside the existing
        `KNOWN_TIMEOUT_EXAMPLES` set, so the two quarantine mechanisms sit side by side and read
        as one concept. Do not pass an explicit `ids=`; `pytest.param` with the same two values
        reproduces the existing auto-generated IDs.
  - [ ] Write the entry-criteria block as a comment immediately above `UNSTABLE_EXAMPLES`,
        covering all four criteria explicitly and separably:
        (1) **what fails and why** -- a heavy-tailed Z3 solve distribution on the
        `\Future`/all_future quantifier family; median ~7-8s, decided draws measured to 47.78s,
        one documented draw undecided at 600s, and the real CI failure at 60.94s against a 60s
        budget;
        (2) **demonstrably non-semantic** -- the genuine countermodel is found on every decided
        draw (7/7 in this task's sweep, corroborated by the settings comment's own history); the
        failure mode is a budget overrun reported as `model_found == False`, never a changed
        semantic conclusion;
        (3) **genuine fix attempted and its failure recorded** -- cross-reference the three
        closed encoding avenues recorded in Phase 1 (`operators.py`'s `_fresh_bound_int`
        docstring), and state that `max_time` re-tuning is explicitly ruled out by the
        `BM_CM_1_settings` comment's standing verdict;
        (4) **EXIT criterion** -- verbatim and unambiguous: *the marker comes off when EITHER
        20 consecutive `unstable-watch` runs record zero failures (nightly cadence, ~3 weeks),
        OR a genuine encoding fix collapses the tail across a >= 20-seed sweep with no undecided
        draw at `max_time = 60`. A single green CI run never qualifies.*
  - [ ] Cross-reference `code/docs/core/TESTING_GUIDE.md` section 8.9 (written in Phase 7) from
        the comment block.
  - [ ] Do not add BM_CM_1 to `KNOWN_TIMEOUT_EXAMPLES` -- that set removes a test from
        collection entirely; `unstable` deliberately keeps it collected and observable.

- **Timing:** 1 hour

- **Depends on:** 3

- **Verification Tier:** interface

- **Scope Hypothesis:** This phase asserts that (a) `test_examples` is consumed only by the
  `@pytest.mark.parametrize` decorator, so restructuring it into `pytest.param` objects has no
  other consumer, and (b) `-m unstable` selects exactly one test across both trees after this
  phase. Confirm (a) with `grep -rn "test_examples" code/src/model_checker/theory_lib/bimodal/`
  before editing (expect hits only in `test_bimodal.py`, at its definition and the parametrize
  call). Confirm (b) with the collection count in Verification below.

- **Files to modify:**
  - `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` - `UNSTABLE_EXAMPLES`
    set, entry-criteria comment block, `pytest.param`-based parametrize

- **Verification:**
  - Node ID stability (the load-bearing check):
    `PYTHONPATH=code/src pytest .../test_bimodal.py --collect-only -q > /tmp/ids-after.txt && diff /tmp/ids-before.txt /tmp/ids-after.txt`
    must produce **no output**. In particular
    `test_example_cases[BM_CM_1-example_case7]` must still exist verbatim.
  - `PYTHONPATH=code/src pytest .../test_bimodal.py -m unstable --collect-only -q` collects
    **exactly one** test, and it is the BM_CM_1 case.
  - `PYTHONPATH=code/src pytest .../test_bimodal.py -m "not unstable" --collect-only -q` collects
    every other case and excludes BM_CM_1.
  - `PYTHONPATH=code/src pytest .../test_bimodal.py -m "not unstable" -q` passes.
  - The comment block addresses all four entry criteria as separately identifiable items and
    contains a written exit criterion with a concrete threshold.

---

### Phase 5: Wire `unstable` deselection into the gating workflows [NOT STARTED]

- **Goal:** No release-gating pytest invocation can be gated on an `unstable`-marked test.

- **Tasks:**
  - [ ] Re-read each of the three workflow files immediately before editing; if any target
        expression already carries `not unstable`, report it (possible overlap with the
        CI-hardening task) rather than double-applying.
  - [ ] `.github/workflows/tests.yml`: extend the main suite invocation's marker expression from
        `-m "not packaging and not performance"` to
        `-m "not packaging and not performance and not unstable"`. Extend the existing comment
        block above it -- which already names
        `test_example_cases[BM_CM_1-example_case7]` as a documented contention flake -- with a
        sentence stating that this case is now `unstable`-marked and observed by
        `unstable-watch.yml`, pointing at `TESTING_GUIDE.md` 8.9.
  - [ ] `.github/workflows/differential-tests.yml`: extend the first invocation's
        `-m "not slow and not differential"` to
        `-m "not slow and not differential and not unstable"`. Leave the second step's explicit
        `TestCIGate`/`TestFormulaEnumerator`/... node-id list untouched -- it never included
        `TestGatingConclusiveScan` and selects by node ID, not by marker.
  - [ ] `.github/workflows/release.yml`: apply the Decision recorded at the top of this plan --
        (1) add the documented-no-op comment at `test-and-release`'s "Install and test package"
        step stating that this job runs no pytest suite, that BM_CM_1 cannot gate a release from
        here, and that any pytest suite added here in future MUST carry `not unstable`;
        (2) change the `build` job's `python -m pytest tests/packaging/ -v -m packaging` to
        `-m "packaging and not unstable"`, with a one-line comment noting this is a defensive
        no-op today.
  - [ ] Check `flake.nix`'s `checks.default` for a pytest invocation covering the bimodal suite
        (`tests.yml`'s comment states the flake check covers the same tests under the nixpkgs
        toolchain). If it invokes pytest with a marker expression, extend it identically and
        record the file-scope widening with its reason; if it does not, record that finding and
        change nothing.

- **Timing:** 45 minutes

- **Depends on:** 3

- **Verification Tier:** local

- **Scope Hypothesis:** This phase asserts there are exactly four gating pytest invocations to
  consider (`tests.yml` main suite, `differential-tests.yml` first step, `release.yml` build
  job, and possibly `flake.nix`'s check). Confirm at implementation time with
  `grep -rn "pytest" .github/workflows/ flake.nix` and enumerate every hit, classifying each as
  gating-and-needs-the-filter or not-applicable-with-a-reason. Any invocation found beyond this
  list must be classified explicitly, not skipped silently.

- **Files to modify:**
  - `.github/workflows/tests.yml` - marker expression + comment
  - `.github/workflows/differential-tests.yml` - marker expression
  - `.github/workflows/release.yml` - documented no-op comment + defensive `build` filter
  - `flake.nix` - conditionally, only if it carries a pytest marker expression

- **Verification:**
  - Each edited YAML parses:
    `python -c "import yaml,glob; [yaml.safe_load(open(f)) for f in glob.glob('.github/workflows/*.yml')]"`.
  - `grep -n 'not unstable' .github/workflows/*.yml` shows the filter present in `tests.yml`,
    `differential-tests.yml`, and `release.yml`'s build job.
  - Local rehearsal of the exact `tests.yml` expression collects BM_CM_1 out:
    `cd code && PYTHONPATH=src pytest src/model_checker/theory_lib/bimodal -m "not packaging and not performance and not unstable" --collect-only -q | grep -c BM_CM_1-example_case7`
    returns 0.
  - Every pytest invocation enumerated by the Scope Hypothesis grep is accounted for in the
    phase's commit message with a classification.

---

### Phase 6: Add the non-gating `unstable-watch.yml` observation workflow [NOT STARTED]

- **Goal:** A scheduled, non-gating workflow that runs ONLY `-m unstable` across both trees,
  makes the pass/fail trend legible over time, surfaces READY TO PROMOTE when the exit threshold
  is met, and alerts loudly when a quarantined test fails in a NEW (semantic) way rather than
  with its documented timing signature.

- **Tasks:**
  - [ ] Create `.github/workflows/unstable-watch.yml`. Triggers: `schedule` (nightly, e.g.
        `cron: '0 5 * * *'` -- nightly chosen so the 20-run exit threshold is reachable in ~3
        weeks; the job runs a single test, so the cost is negligible) plus `workflow_dispatch`.
        **No `push`, no `pull_request`, no `tags`.** Add a header comment stating the
        non-gating contract explicitly: this workflow must never appear in another workflow's
        `needs:` and must never be added to branch protection; it exists to observe, not to
        gate. Note in the same comment that this is the repository's first `schedule:` workflow.
  - [ ] Run two pytest steps, each with `continue-on-error: true` and `--junitxml` output so a
        failure is recorded rather than aborting the job:
        (a) `cd code && PYTHONPATH=src pytest tests/ src/model_checker -m unstable -v --junitxml=/tmp/watch-code.xml`
        (b) `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/ -m unstable -v --junitxml=/tmp/watch-oracle.xml`
        Treat pytest **exit code 5** ("no tests collected") as "no unstable tests in this tree"
        and continue; only exit codes other than 0 and 5 count as failures. (After this task the
        oracle tree has no `unstable` test, so branch (b) will hit code 5 -- this must not fail
        the job.)
  - [ ] Add a classification step that parses the JUnit XML and, for each failing testcase,
        classifies the failure:
        - **TIMING (documented signature)**: the testcase's recorded `time` is >= 0.8x the
          example's `max_time` AND the failure message is the expected
          `Test failed for example: ...` assertion. A budget overrun surfaces as
          `model_found == False`, so it fails at ~`max_time`.
        - **NEW (possible semantic regression)**: anything else -- a fast failure (well under
          the budget, meaning the solver decided and the assertion still failed), a different
          assertion message, or an error/exception rather than an assertion.
        Emit `::error title=UNSTABLE-WATCH: NEW FAILURE MODE::` for every NEW classification and
        mark the job failed in that case only; a TIMING failure is recorded but leaves the job
        green (the whole point of the category). Keep the classification logic in an inline
        Python step in the workflow, not a new repo script, so the file-scope stays as declared.
  - [ ] Write an append-only per-run record: emit one JSON line per test
        (`{run_id, timestamp, nodeid, outcome, duration_s, classification}`) to
        `unstable-watch-record.jsonl` and upload it with `actions/upload-artifact`. For the
        cross-run trend, do not maintain committed state -- query GitHub's own run history in
        the same step
        (`gh run list --workflow unstable-watch.yml --json conclusion,createdAt,databaseId --limit 25`),
        which is inherently append-only and needs no write access.
  - [ ] READY TO PROMOTE surfacing: if the last 20 runs of this workflow (including the current
        one) all concluded `success`, emit a `::notice title=READY TO PROMOTE::` naming each
        currently-`unstable` test and pointing at `TESTING_GUIDE.md` 8.9's promotion path.
  - [ ] Write a `$GITHUB_STEP_SUMMARY` table: one row per `unstable` test with outcome,
        duration, classification, plus the current consecutive-green streak and the
        20-run promotion threshold.

- **Timing:** 1.5 hours

- **Depends on:** 3

- **Commit Mode:** per-substep

- **Verification Tier:** local

- **Scope Hypothesis:** This phase asserts `unstable-watch.yml` will be the repository's first
  and only `schedule:`-triggered workflow. Confirm at implementation time with
  `grep -rn "schedule:" .github/workflows/` before creating the file; if another scheduled
  workflow exists, read it first and match its cadence and reporting conventions rather than
  inventing new ones.

- **Files to modify:**
  - `.github/workflows/unstable-watch.yml` - new file

- **Verification:**
  - `python -c "import yaml; d=yaml.safe_load(open('.github/workflows/unstable-watch.yml')); print(sorted(d[True] if True in d else d['on']))"`
    shows exactly `schedule` and `workflow_dispatch` and nothing else.
  - `grep -nE '^\s*(push|pull_request|tags):' .github/workflows/unstable-watch.yml` returns
    nothing.
  - `grep -rn "unstable-watch" .github/workflows/ | grep needs` returns nothing (no other
    workflow depends on it).
  - The classification Python is syntax-checked locally (`python -c "compile(open(f).read(), f, 'exec')"`
    against the extracted snippet, or by running it against a hand-written sample JUnit XML with
    one TIMING and one NEW failure and confirming it classifies both correctly).
  - Local rehearsal of the selection: `cd code && PYTHONPATH=src pytest src/model_checker -m unstable --collect-only -q`
    collects exactly the BM_CM_1 case; the oracle-tree equivalent exits 5 and is handled.

---

### Phase 7: Document the `unstable` policy in TESTING_GUIDE.md 8.9 [NOT STARTED]

- **Goal:** A durable, discoverable policy record: entry criteria, exit criteria, review
  cadence, promotion path, and the standing escalation rule.

- **Tasks:**
  - [ ] Read sections 8.6 ("Solver Timing Budgets and Machine Variance") and 8.8 ("Oracle Suite:
        Gating vs. Exhaustive Split") to match their voice, depth, and cross-referencing style.
  - [ ] Add a new `### 8.9 The \`unstable\` Marker` subsection after 8.8, covering:
        - **What the marker means** -- verbatim from the `pyproject.toml` registration text.
        - **Entry criteria** -- all four, stated as a checklist, with the explicit note that
          "it failed once in CI" never qualifies and that the category must not become a dumping
          ground.
        - **Exit criteria and the promotion path** -- the general rule (a written, per-test exit
          criterion is mandatory at the marker site) plus the concrete default (20 consecutive
          green `unstable-watch` runs, or a genuine fix demonstrated across a >= 20-seed sweep),
          and the mechanical promotion steps: remove the mark, remove the test from the
          workflow's exclusion accounting if named there, and record the promotion in the
          settings/marker comment rather than deleting its history.
        - **Review cadence** -- the `unstable` set is reviewed monthly; `unstable-watch.yml`
          runs nightly and surfaces READY TO PROMOTE automatically.
        - **The standing rule** -- an indefinitely-quarantined test is itself a defect to
          escalate, not a steady state. A test still marked `unstable` after two review cycles
          with no promotion and no active repair work must get a task opened against it.
        - **Where the deselection is wired** -- name `tests.yml`, `differential-tests.yml`, and
          `release.yml` (including the documented no-op at `test-and-release`), so a future
          author adding a gating invocation knows to include the filter.
        - **Currently marked** -- `test_example_cases[BM_CM_1-example_case7]`, one line, with a
          pointer to the in-line entry-criteria block rather than a duplicate of it.
  - [ ] Cross-reference 8.6 (the timing-variance mechanism this category exists to route
        around) and 8.8 (the gating-floor discussion).

- **Timing:** 1 hour

- **Depends on:** 3

- **Verification Tier:** prose

- **Files to modify:**
  - `code/docs/core/TESTING_GUIDE.md` - new section 8.9

- **Verification:**
  - `grep -n "^### 8\." code/docs/core/TESTING_GUIDE.md` shows 8.9 present, in order, after 8.8.
  - Every cross-referenced path and section (`unstable-watch.yml`, the three workflows,
    `pyproject.toml`, sections 8.6/8.8) exists; check each with a `test -f` / `grep`.
  - The section addresses all five required topics (entry, exit, cadence, promotion path,
    escalation rule) as separately identifiable items.

---

### Phase 8: Terminal deliverable -- outcome assessment and conditional follow-up [NOT STARTED]

- **Goal:** Assess whether deliverables (1) and (2) fully closed both defects; record that
  outcome; and create the follow-up task carrying the frontier forward if anything remains
  unstable or unverified.

- **Tasks:**
  - [ ] Assess deliverable (1): BM_CM_1. Expected outcome given the research: **not closed** --
        no encoding fix exists, the test is marked `unstable`. Record the assessment explicitly
        rather than assuming it.
  - [ ] Assess deliverable (2): the oracle floor. Expected outcome: **repair landed but
        unverified on real CI** -- the widened budget cannot be dispatched by an agent.
  - [ ] Since at least one deliverable did not fully close, create a follow-up task with
        `task_type: "python"` and a `file_scope` covering the bimodal theory package, its tests,
        and the oracle bimodal tree. Carry forward concretely:
        - Which tests were marked `unstable` and why (BM_CM_1), with each test's written exit
          criterion quoted verbatim.
        - The standing verdict that **no budget closes the BM_CM_1 tail** -- the follow-up must
          not re-tune `max_time` either.
        - The oracle measurements (95/103 and 96/103 on real CI against `floor=100`, 0
          disagreements; 103/103 locally under both 24-core and 2-core conditions) and the
          **do-not-lower-the-floor** instruction.
        - The outstanding CI verification obligation: run `differential-tests.yml` via
          `workflow_dispatch` 2-3 times against the widened `GATING_RECHECK_SOLVE_TIMEOUT_MS =
          40000`, and only if it still falls short consider marking
          `TestGatingConclusiveScan::test_known_conclusive_population_self_consistent`
          `unstable` under the same four entry criteria.
        - Everything already ruled out, so the follow-up starts from the frontier: the prior
          task's `FreshInt` and pattern/trigger avenues, this task's finite-unrolling
          experiment, and the 2-core `taskset` non-reproduction for the oracle defect.
        - The `unstable-watch.yml` promotion path and the 20-run threshold, so the follow-up
          knows what evidence would let the marker come off.
  - [ ] Record the USER ACTION summary prominently in the implementation summary: the user must
        push and dispatch `differential-tests.yml` to verify the oracle budget fix, and may then
        dispatch `unstable-watch.yml` once to confirm the watch workflow runs green.
  - [ ] If, contrary to expectation, both defects fully closed and nothing needed the marker,
        create no follow-up and record that outcome explicitly with its evidence.

- **Timing:** 45 minutes

- **Depends on:** 1, 2, 3, 4, 5, 6, 7

- **Verification Tier:** local

- **Files to modify:**
  - `specs/state.json` - new follow-up task entry (via the sanctioned task-creation path, never
    a wholesale `.artifacts` or `.active_projects` replacement)
  - `specs/TODO.md` - regenerated via `bash .claude/scripts/generate-todo.sh`

- **Verification:**
  - `jq '.active_projects[] | select(.project_name | test("bimodal"))' specs/state.json` shows
    the follow-up task with `task_type: "python"` and the declared `file_scope`.
  - `python -c "import json; json.load(open('specs/state.json'))"` parses.
  - The follow-up description contains each of the six carried-forward items listed above --
    check by reading it back.
  - `bash .claude/scripts/generate-todo.sh` runs clean and `specs/TODO.md` shows the new task.

---

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py -m "not unstable" -q` passes.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py -m unstable --collect-only -q` selects exactly one test.
- [ ] Node ID diff before/after Phase 4 is empty.
- [ ] `PYTHONPATH=code/src pytest oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestGatingConclusiveScan -v` passes locally at `conclusive=103/103`.
- [ ] `cd code && pytest --markers | grep unstable` and the oracle-tree equivalent both show the registration.
- [ ] All four workflow files parse as YAML; `unstable-watch.yml` has only `schedule` and `workflow_dispatch` triggers.
- [ ] Full bimodal unit suite under the exact `tests.yml` expression passes:
      `cd code && PYTHONPATH=src pytest src/model_checker/theory_lib/bimodal -m "not packaging and not performance and not unstable" -q`.
- [ ] `MIN_CONCLUSIVE_GATING_FORMULAS` is still `100`.
- [ ] No `git push`, `git tag`, `/merge`, `/tag`, or twine invocation anywhere in the implementation.

## Artifacts & Outputs

- `specs/159_fix_bimodal_flake_and_unstable_category/plans/01_bimodal-flake-unstable-category.md` (this file)
- `specs/159_fix_bimodal_flake_and_unstable_category/summaries/01_bimodal-flake-unstable-category-summary.md`
- `.github/workflows/unstable-watch.yml` (new)
- `code/docs/core/TESTING_GUIDE.md` section 8.9 (new)
- Edits to: `code/pyproject.toml`, `oracle/conftest.py`,
  `code/src/model_checker/theory_lib/bimodal/{examples.py,operators.py}`,
  `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py`,
  `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`,
  `.github/workflows/{tests.yml,release.yml,differential-tests.yml}`
- A follow-up task in `specs/state.json` (conditional on Phase 8's assessment)

## Rollback/Contingency

Every phase is independently revertible and committed separately, so a bad phase can be reverted
without disturbing the others.

- **Phases 1 and 7** are comment/prose-only: revert with no behavioural consequence.
- **Phase 2** (oracle budget): if the widened budget makes anything worse locally, revert both
  the constant and the `--timeout` change together -- they were deliberately landed in one
  phase and must move together.
- **Phase 4** (the marker): if the node ID diff is non-empty, revert the `pytest.param`
  restructuring and fall back to the codebase's existing precedent for marking parametrized
  cases without touching the source data structure -- `oracle/conftest.py`'s
  `pytest_collection_modifyitems` node-ID-fragment matcher, which exists for exactly this
  problem. Add a `conftest.py`-level matcher in the bimodal tests tree instead.
- **Phases 5 and 6** (workflows): YAML-only; revert restores the prior gating behaviour
  immediately. Note that reverting Phase 5 while keeping Phase 4 re-exposes CI to the BM_CM_1
  flake, so these two must be reverted together or not at all.
- **Phase 8**: a follow-up task created in error is retired with `/task --abandon N`.

If the whole task must be abandoned, `git revert` the phase commits in reverse order; no
migration, data change, or published artifact is involved.
