# Implementation Plan: Certifying Countermodel Architecture

- **Task**: 205 - certifying_countermodel_architecture
- **Status**: [IMPLEMENTING]
- **Effort**: 12 hours (sum of the eight phase timings)
- **Dependencies**: None declared. Consumes (does not re-decide) task 197's certificate-wire hardening, which has landed: the checker now returns `acceptance: entailment` with a bytewise-matching `echo`.
- **Research Inputs**: `specs/205_certifying_countermodel_architecture/reports/01_certifying-countermodel-architecture.md`
- **Artifacts**: plans/01_certifying-countermodel-architecture.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: formal
- **Lean Intent**: false

## Overview

This task owns three things: the output gate on reported countermodels (item 1), the checker's
runtime availability for users with no Lean toolchain (item 2), and the repositioning of the
existing test tiers as UNSAT-direction liveness/regression evidence (item 3). The work is
organized around one measured fact from research: the independent Lean check costs ~50 ms when the
built binary is invoked directly (the ~2.2 s figure in the test suite is `lake`'s build check, not
the checker), so a per-run gate is affordable and the only real obstacle is *availability*, not
cost. Definition of done: every reported countermodel carries an honest, source-grounded label
saying whether it was independently checked; a production-side resolver (not the test tree's
helper) decides availability with a lazy bounded probe and an enforced capability handshake; the
packaging route is decided on a fresh measurement rather than on the current 209 MiB binary; and
the four tier-describing documents plus three test-module surfaces state the direction claim.

### Research Integration

Findings that change the plan's shape versus the task description:

- **F1 — the dispatch's "verdict-producing today" premise is stale.** The binary returns
  `acceptance=entailment` with a matching `echo`, measured live. The whole "is an interim gate over
  a weaker checker worth shipping" branch of item 1 is moot: the gate is built over the
  `entailment` level directly (Phase 3).
- **F2 — two documents overclaim that level** (`ADEQUACY.md` §6.2 and `TRUST_PIPELINE.md`'s trust
  base both call it "a kernel-checked proof for that particular certificate", which is exactly the
  third `Acceptance` value the Lean module deliberately reserves). Reported, not fixed — wire-task
  territory. The gate's own label text is written from the Lean `Acceptance` docstring vocabulary,
  never from §6.2's sentence (Phase 3, Phase 8).
- **F3 — the gate already half exists.** `semantic/model.py:62-95` runs `recheck` unconditionally
  outside any `try`/`except` on every satisfying solve, and nothing catches
  `ModelConstructionError`. What is missing is the *independent* leg, not the gate. This makes item
  1 a labelling-and-availability change, not a new fail-fast path.
- **F5 — ~50 ms, not ~2.2 s**, when the binary is invoked directly. Removes the cost objection.
- **F7 — item 2's cost is set by one upstream flag.** 212,374 of the binary's symbols are
  `l_Lean*`, zero are Mathlib/FormalSystem/BimodalTools runtime code, and every `[[lean_exe]]` in
  BimodalLogic's `lakefile.toml` sets `supportInterpreter = true`. Phase 6 is therefore a decision
  gate: measure with the flag off *before* deciding any packaging route.
- **F8 — `tests/_lean_check.py` cannot be the resolver**: it runs a 60 s `probe()` at module
  import time and lives in the test tree. Phase 1 builds a production resolver; Phase 4 refactors
  the test helper onto it without changing test behaviour.
- **F9 — `BIMODAL_LOGIC_COMMIT` is a dead pin** (declared, exported, consumed nowhere) and the
  local checkout has already drifted from it. Phase 2 enforces a capability handshake instead of
  relying on the pin, and demotes the commit to recorded provenance.
- **F10-F14 — item 3's three already-applied `TRUST_PIPELINE.md` edits all verify correct**; the
  genuinely open work is `A2_GAP.md` §8 limit 3 (stale in exactly the way `TRUST_PIPELINE.md` was
  repaired), `ADEQUACY.md` §7.1's `f^3` sweep arithmetic (contradicts `SEARCH_COVERAGE.md` §3(b)'s
  quadratic decision), `ADEQUACY.md` §7.3's two staleness points, and the direction claim at seven
  surfaces (Phase 7).

### Prior Plan Reference

No prior plan. `plans/` was empty at dispatch; this is round 01.

### Roadmap Alignment

`roadmap_path` was not provided in this dispatch's context, so `specs/ROADMAP.md` is not a plan
input and no roadmap review/update phases are scheduled. Noted for whoever does own it: item 2's
packaging decision (Phase 6) touches the roadmap's wheel/release and CI-gating entries, and Phase
6's recorded measurement is the input a future in-wheel-shipping decision would need.

## Goals & Non-Goals

**Goals**:

- A production-side checker resolver under `semantic/` with lazy, bounded probing, a documented
  resolution order, and an *enforced* capability handshake (item 1's precondition; F8/F9).
- Three honest output states on the countermodel path, worded from the Lean `Acceptance`
  vocabulary: independently checked (`entailment`), Python-re-checked only, and no certificate
  found — plus a fourth behaviour under a strict setting that withholds an unchecked countermodel
  (item 1; R1/R3).
- One new `verify` example setting with a new `SETTINGS.md` section, and an addition beside
  `ADEQUACY.md` §7.4's guards stating that an *unchecked* countermodel is not a validity claim
  either (item 1).
- A measured packaging decision: `supportInterpreter = false` rebuilt and re-measured before any
  route is chosen or rejected (item 2; R4/D2).
- An availability path for users with no Lean toolchain that keeps the wheel `py3-none-any`:
  documented opt-in via an explicit binary path plus optional SHA-256 pinning (item 2, Route B +
  the consumer half of the out-of-band route).
- The tier repositioning: the direction claim stated at every surface where the tiers are
  described, `A2_GAP.md` §8 limit 3 recorded as discharged, `ADEQUACY.md` §7.1/§7.3 corrected, and
  the structural conformance check recorded as a sequenced follow-on (item 3; R6/R7).

**Non-Goals**:

- The wire format, proof-carrying acceptance, and parse-echo verification (wire-hardening task).
  This plan consumes them.
- Fixing `ADEQUACY.md` §6.2's and `TRUST_PIPELINE.md`'s trust-base overclaim (F2/D1) — reported to
  the wire task, not edited here.
- Publishing per-platform release assets or building the per-platform wheel matrix. Phase 6 decides
  whether that is worth a follow-on task; it is not built here, and asset publication requires a
  remote push no agent may perform.
- A Python re-implementation of the decision procedures (declined: it already exists as `recheck`
  and supplies no per-run link to the Lean predicates — F6/Route C).
- Requiring the Lean toolchain of users (declined on measured grounds: 17 GB `~/.elan`, 9.2 GB
  `.lake/packages`, against a 1.14 MiB wheel — Route D).
- The structural conformance check (recorded as a follow-on, explicitly sequenced after items 1-2).
- The A1 compression bound, the divisor-period sweep driver, the harness reorganization and its
  performance work.
- Deleting, narrowing, or weakening any existing test. The retained aggregate assertion stays.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The gate's label repeats §6.2's "kernel-checked proof for that particular certificate" | H | M | Phase 3 writes label text from `BimodalTools/CertificateImport.lean`'s `Acceptance` docstring only; a Phase 3 test asserts the forbidden phrase is absent from rendered output |
| The production gate imports `tests/_lean_check.py` and inherits its 60 s import-time probe | H | M | Phase 1 builds an independent resolver; Phase 4 inverts the dependency (test helper → production module), never the reverse |
| Default-on verification changes output for every existing example and breaks unrelated tests | H | M | `verify` defaults to `auto` = label-only, never failing when the checker is absent; Phase 3 runs the full bimodal suite before closing |
| Phase 6's companion-repo rebuild is unavailable or too slow to schedule | M | M | Bounded build window with a named contingency: record the untrimmed figures, mark the decision deferred, and proceed — Route B (Phases 1-5) stands alone and blocks on nothing |
| The gate is built over an unpinned checker whose acceptance vocabulary is not guaranteed | M | M | Phase 2's capability handshake is enforced (probe must answer `countermodel` *and* carry `acceptance` *and* echo bytewise); the commit pin is demoted to recorded provenance, per D4 |
| `SETTINGS.md` / `ADEQUACY.md` §7.4 edits collide with the wire task's own overlap | M | M | §7.4 gets an addition *beside* its guards, not a modification; `SETTINGS.md` gets a new section (there is no Verification section today); re-read both immediately before editing |
| Item 3's edits duplicate the three already-applied `TRUST_PIPELINE.md` edits | M | M | F10's table states exactly what is already present; Phase 7 opens by re-reading and extends only |
| Sibling task 206 is dispatched into this same working tree with no declared `file_scope` | M | H | Re-read every file immediately before editing; stage only this task's own hunks by explicit path, never a directory or glob; never run `git-snapshot.sh` in its reverting default mode; report any foreign commit or modification rather than dismissing it |
| A cold first invocation of a 209 MiB binary pays page-in cost inside a user's solve | L | M | ~120 MB RSS observed warm; the resolver's probe is bounded and the result cached per process, so the cost is paid at most once |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 6 | -- |
| 2 | 2, 7 | 1 (for 2), 6 (for 7) |
| 3 | 3, 4 | 1, 2 |
| 4 | 5 | 3 |
| 5 | 8 | 3, 4, 5, 7 |

Phases within the same wave can execute in parallel.

### Phase 1: Production checker resolver [COMPLETED]

**Goal**: A production-side module that answers "is an independent checker available, and how do I
invoke it?" without importing anything from the test tree and without a 60-second import-time
probe.

**Tasks**:
- [x] Write `tests/unit/test_checker.py` first (RED): resolution order is honoured; an absent *(completed)*
      checker yields an `unavailable` result with a named reason rather than an exception; the probe
      runs at most once per process and only on first use (assert via a call counter or monkeypatched
      runner, not by timing); a probe timeout yields `unavailable`, not a hang.
- [x] Create `semantic/checker.py` exposing a small, documented surface: a `resolve_checker()` *(completed)*
      returning either an invocable checker handle or an `unavailable` reason, and a
      `check_certificate(payload, timeout)` that invokes it and returns the parsed verdict plus the
      exact bytes sent (reusing `canonical_wire_bytes` from `semantic/certificate.py`).
- [x] Implement the resolution order, each step documented in the module docstring with its *(completed)*
      rationale: (i) explicit binary path from `BIMODAL_CHECKER_BIN`; (ii) a standalone binary in a
      per-user cache location; (iii) the built binary inside a `BIMODAL_LOGIC_PATH` checkout
      (`.lake/build/bin/check_certificate`), invoked **directly** — never through `lake exe`, which
      is where the ~2.2 s build check comes from (F5); (iv) unavailable.
- [x] Make probing lazy and bounded: computed on first call, memoized for the process, with an *(completed)*
      explicit timeout constant in source (mirroring `_lean_check.py`'s explicit
      `PROBE_TIMEOUT_SECONDS` discipline but at a bound appropriate to a ~50 ms binary, not to a
      `lake` build).
- [x] Port the echo comparison as a production-side check: a verdict whose `echo` does not match *(completed)*
      the bytes sent is a protocol failure, distinct from a rejection — keep `_lean_check.py`'s
      environment-absence/protocol-failure split, which exists because conflating them once deleted
      a whole differential tier silently.
- [x] Run the new unit tests to green; run the existing bimodal unit suite to confirm no import-time *(completed)*
      regression.

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/checker.py` - new module: resolution order, lazy bounded probe, direct binary invocation, echo comparison
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py` - new unit tests, written first

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py -v` passes.
- `python -c "import time; t=time.time(); import model_checker.theory_lib.bimodal.semantic.checker; print(time.time()-t)"` completes in well under a second with no checker present (proves the probe is not at import time).
- `grep -rn "tests\." code/src/model_checker/theory_lib/bimodal/semantic/checker.py` returns nothing (no test-tree dependency).

---

### Phase 2: Enforced capability handshake and recorded provenance [NOT STARTED]

**Goal**: The gate knows which checker contract it is gating against. The acceptance vocabulary and
the `echo` field are properties of a particular binary, so their presence is *enforced*, not
assumed — and the commit pin, which is currently consumed by nothing and already drifted, is
demoted to provenance rather than promoted to a gate.

**Tasks**:
- [ ] Extend `tests/unit/test_checker.py` (RED): a probe answering `countermodel` but carrying no
      `acceptance` field is rejected as a capability failure, not accepted as available; a probe
      whose `echo` does not match the sent bytes is a protocol failure; an `acceptance` value
      outside the known vocabulary is a capability failure naming the value seen.
- [ ] Implement the handshake in `semantic/checker.py`: availability requires the probe certificate
      to return `status == "countermodel"`, an `acceptance` value in the known vocabulary
      (`decided`, `entailment`), and an `echo` matching the bytes sent bytewise.
- [ ] Add optional integrity pinning: when a SHA-256 digest is configured (environment variable, or
      a digest file beside a cached binary), a resolved standalone binary whose digest does not
      match is refused with a named reason. Absent configuration, no digest check — this is the hook
      the out-of-band artifact route needs, not a new mandatory requirement.
- [ ] Record provenance rather than enforce it: when the checker resolves inside a
      `BIMODAL_LOGIC_PATH` checkout, capture that checkout's HEAD for inclusion in the output label;
      state in the module docstring why the commit is provenance and the handshake is the
      enforcement (F9/D4, and the observed same-day drift from `d55e2760` to `d1a24b30`).
- [ ] Tests to green; bimodal unit suite green.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/checker.py` - handshake, optional digest pin, provenance capture
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py` - handshake and digest tests

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py -v` passes, including the three new capability-failure cases.
- With a real checkout present, a manual `resolve_checker()` call reports available and records a HEAD commit; with `BIMODAL_CHECKER_BIN` pointed at `/bin/true`, it reports unavailable with a capability-failure reason rather than claiming availability.

---

### Phase 3: The output gate, three states, and the `verify` setting [NOT STARTED]

**Goal**: A reported countermodel says, in words drawn from the Lean module's own vocabulary,
whether it was independently checked — and a strict mode refuses to report one that was not.

**Tasks**:
- [ ] Write the tests first (RED) in a new `tests/integration/test_output_gate.py`: with the
      checker available, a satisfying solve renders the independently-checked label and records
      `acceptance=entailment`; with it unavailable, the same solve renders the
      Python-re-checked-only label; under `verify: 'required'` with the checker unavailable, the
      countermodel is withheld with a clear error rather than reported; under `verify: 'off'` no
      checker invocation occurs at all. Add an assertion that no rendered output contains the phrase
      "kernel-checked proof" (the F2 overclaim guard).
- [ ] Add `verify` to `BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS` in `semantic/core.py` with
      default `'auto'` and the documented three values: `'off'` (Python re-check only, no
      independent leg), `'auto'` (run the independent check when a checker resolves; label
      accordingly; never fail on absence), `'required'` (an unreported-because-unchecked
      countermodel is an error). Validate the value early and fail fast on an unknown one.
- [ ] Wire the check into `BimodalStructure.__init__` immediately after the existing mandatory
      `recheck` guard, using `semantic/checker.py` and `WitnessFamily.to_json(premises,
      conclusions, target_time)` — the same payload shape the A2-triangle test already sends. Store
      the outcome (checked/unchecked, acceptance level, provenance, or the unavailability reason) on
      the structure; do not swallow a protocol failure, which must surface as loudly as the existing
      `recheck` guard does.
- [ ] Render the three states in `print_certificate` and `print_evaluation` (`semantic/model.py`),
      wording the checked state as: Lean constructed a `WitnessFamily.Refutes` term for this
      certificate by applying a compile-time kernel-checked implication to four run-time decisions —
      never as a per-certificate kernel-checked proof. Word the unchecked state as: re-checked by
      this repository's own pure-Python decision procedures only.
- [ ] Under `verify: 'required'` with no checker, raise the withholding error with a suggestion
      naming how to obtain a checker (pointing at the Phase 5 documentation).
- [ ] Update `tests/unit/test_structure.py`'s existing `print_certificate`/`print_evaluation`
      expectations for the new third state; do not weaken the existing no-certificate assertions.
- [ ] Tests to green; then the full bimodal suite.

**Timing**: 2 hours

**Depends on**: 1, 2

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: the countermodel path is rendered at exactly two call sites
(`print_certificate` and `print_evaluation` in `semantic/model.py`, both reached from `print_all`),
and no other module renders a countermodel verdict. Confirm at implementation time with
`grep -rn "print_certificate\|print_evaluation\|not a validity claim" --include=*.py
code/src/model_checker/` and reconcile every hit before editing; if a third renderer exists, it is
in scope for this phase.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/core.py` - `verify` setting in `DEFAULT_EXAMPLE_SETTINGS` plus early validation
- `code/src/model_checker/theory_lib/bimodal/semantic/model.py` - invoke the checker after the existing `recheck` guard; render the three states
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py` - new, written first
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_structure.py` - update print expectations for the third state

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` fully green.
- `cd code && ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py` renders the checked label when a checker is present and the unchecked label when `BIMODAL_LOGIC_PATH` and `BIMODAL_CHECKER_BIN` are both unset.
- `BIMODAL_LOGIC_PATH= BIMODAL_CHECKER_BIN= ` plus a `verify: 'required'` example withholds the countermodel with the named error.
- The overclaim guard test passes: no rendered output contains "kernel-checked proof".

---

### Phase 4: Refactor the test helper onto the production resolver [NOT STARTED]

**Goal**: One invocation-and-echo implementation, on the production side, consumed by the tests —
rather than two that can drift. Test behaviour is preserved exactly, including the import-time
probe the differential modules' `skipif` markers depend on.

**Tasks**:
- [ ] Re-read `tests/_lean_check.py` and each consuming module immediately before editing (sibling
      task 206 shares this tree).
- [ ] Rewrite `tests/_lean_check.py` to delegate invocation, echo comparison, and resolution to
      `semantic/checker.py`, keeping every currently exported name and its exact semantics:
      `SKIP_REASON`, `PROTOCOL_FAILURE`, `run_check_certificate`,
      `run_check_certificate_with_sent`, `assert_echo_matches_sent`, `probe`,
      `resolve_bimodal_logic_path`, `resolve_lake`, `BIMODAL_LOGIC_PATH`, `LAKE`,
      `BIMODAL_LOGIC_COMMIT`, `PROBE_TIMEOUT_SECONDS`.
- [ ] Keep the module-level probe *in the test helper* (the `skipif` markers read `SKIP_REASON` at
      collection time); the production resolver's own probe stays lazy. Document the asymmetry in
      the helper's docstring so it is not "fixed" later by mistake.
- [ ] Preserve the environment-absence versus protocol-failure split verbatim in behaviour; the
      helper's docstring account of why it exists stays.
- [ ] Run every consuming module with a checkout available, and again with `BIMODAL_LOGIC_PATH`
      pointed at a nonexistent directory, confirming clean skips in the second case.

**Timing**: 1 hour

**Depends on**: 1, 2

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: exactly three test modules import `tests/_lean_check.py`
(`tests/integration/test_certificate_lean_agreement.py`,
`tests/integration/test_certificate_a2_triangle.py`, `tests/unit/test_semantics_core.py`; the
other matches for the string are documentation and `tests/_pinned_eval.py`'s prose reference).
Confirm with `grep -rln "_lean_check" code/src/model_checker/theory_lib/bimodal/` and build the
dependent set from the result rather than from this list.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py` - delegate to `semantic/checker.py`; keep the exported surface and the import-time probe

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantics_core.py -v` passes with a checkout present.
- The same command with `BIMODAL_LOGIC_PATH=/nonexistent` produces clean skips and zero errors.
- `git diff` on the helper shows no removed public name.

---

### Phase 5: Gate documentation and the availability path [NOT STARTED]

**Goal**: A user can tell what the label means, how to change the strictness, and how to obtain a
checker without installing a Lean toolchain.

**Tasks**:
- [ ] Re-read `docs/SETTINGS.md` and `docs/ADEQUACY.md` §7.4 immediately before editing (wire-task
      overlap plus sibling-task concurrency).
- [ ] Add a new `## Certificate Verification` section to `docs/SETTINGS.md` documenting `verify`'s
      three values, the default, the three output states in the same words the code renders, and the
      ~50 ms measured cost of the independent leg. This is a new section, not an edit to an existing
      one — there is no verification setting today.
- [ ] Add, *beside* §7.4's existing no-certificate guards and without modifying them, the statement
      that an **unchecked** countermodel is not a validity claim either — the point becomes
      non-obvious once a third state exists, because a reader can mistake "unchecked" for hedging
      about the inference rather than about the certificate.
- [ ] Document the availability path (in `docs/SETTINGS.md`'s new section, cross-referenced from
      `docs/USER_GUIDE.md`): the resolution order, `BIMODAL_CHECKER_BIN` for a standalone binary,
      the cache location, and the optional SHA-256 pin. State plainly that no Lean toolchain is
      required to be in tier 1 — only a checker binary.
- [ ] State what the checked label does and does not establish, in the Lean `Acceptance`
      vocabulary, and note that the per-certificate step rests on Lean's compiler and on the
      importing module's decoding, not on the kernel.

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: prose

**Commit Mode**: per-substep

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/SETTINGS.md` - new `## Certificate Verification` section
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` - addition beside §7.4's guards
- `code/src/model_checker/theory_lib/bimodal/docs/USER_GUIDE.md` - cross-reference to the new section

**Verification**:
- Diff read-through confirms every changed hunk is prose, §7.4's existing guard sentences are
  byte-identical, and `SETTINGS.md`'s pre-existing sections are untouched.
- Every setting value named in the documentation matches `DEFAULT_EXAMPLE_SETTINGS` and the
  validation in `semantic/core.py`.
- Internal links resolve (`grep` each referenced section heading).

---

### Phase 6: Packaging decision gate — measure the trimmed checker [NOT STARTED]

**Goal**: Decide item 2's route on a fresh measurement rather than on a number that a one-line
upstream flag invalidates. This phase is the decision gate for whether in-wheel shipping (Route A)
is worth a follow-on task.

**Tasks**:
- [ ] Record the baseline from research for comparison: 313,863,000 B unstripped, 219,351,032 B
      stripped, 69,143,681 B stripped+`gzip -9`, against a 1,190,654 B `py3-none-any` wheel.
- [ ] In `~/Projects/BimodalLogic` (companion repository, read-mostly: one-line build-flag change),
      set `supportInterpreter = false` for the `check_certificate` `[[lean_exe]]` only, rebuild that
      target, and re-measure unstripped, stripped, and `gzip -9` sizes. Bound the build with an
      explicit timeout and a single waiter on its log (`context/patterns/bounded-build-waiter.md`);
      do not leave the flag flipped in the companion repository afterwards unless that repository's
      owner wants it — restore it and note the finding.
- [ ] Re-run the capability handshake against the trimmed binary to confirm it still answers
      `countermodel` with `acceptance=entailment` and a matching `echo` (a checker that is smaller
      but no longer answers is not a candidate).
- [ ] Decide and record: if the compressed artifact is single-digit MiB, record that in-wheel
      shipping is now plausible and name the follow-on work it needs (per-platform wheel matrix,
      manylinux build, `BIMODAL_LOGIC_COMMIT` becoming an enforced build pin). If it stays in the
      tens of MiB, record that the out-of-band opt-in artifact remains the recommendation and
      in-wheel shipping is declined on the measured number.
- [ ] Contingency, if the rebuild cannot be run: record the untrimmed figures, mark the decision
      explicitly deferred with the measurement named as its precondition, and proceed. Nothing in
      Phases 1-5 depends on this number.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: exactly one `[[lean_exe]]` stanza needs changing (`check_certificate`) and
the flag appears as `supportInterpreter = true` in `~/Projects/BimodalLogic/lakefile.toml`. Confirm
with `grep -n "supportInterpreter\|lean_exe" ~/Projects/BimodalLogic/lakefile.toml` before editing,
and if the flag is set globally rather than per-target, record that instead of widening the change.

**Files to modify**:
- No file in this repository. The measured numbers and the decision are recorded in this task's
  summary and consumed by Phase 7's `TRUST_PIPELINE.md` row extension.

**Verification**:
- Both size triples (baseline and trimmed, or baseline plus a named reason the trimmed one is
  unavailable) are recorded with the exact commands that produced them.
- The trimmed binary's handshake result is recorded.
- `git -C ~/Projects/BimodalLogic status --porcelain` shows the working tree left as found.

---

### Phase 7: Item 3 — extend the ledger, state the direction claim [NOT STARTED]

**Goal**: Extend the three already-applied `TRUST_PIPELINE.md` repairs rather than duplicating
them, close the same staleness one document over, and state at every tier-describing surface that
the Tier 1 differential and the search-coverage grid pins are liveness and regression evidence for
the UNSAT direction — not countermodel trust.

**Tasks**:
- [ ] Re-read `docs/TRUST_PIPELINE.md`'s remaining-work table and its "The standing test for A2"
      section and confirm, in the summary, all three already-applied edits still read correctly
      against what landed: the stale `nb = nf = 2` widening row is absent, the standing-test section
      records the closed blind spot with its measured cost and the aggregate→per-candidate move, and
      both new remaining-work rows for items 1 and 2 are present. Extend only.
- [ ] `docs/A2_GAP.md` §8 limit 3: record the per-candidate obligation as **discharged**, naming
      `tests/_pinned_eval.py`'s `compile_and_bind` as precisely the prescribed solver-free pinned
      evaluator and `_run_exhaustive_triangle`'s first-divergence raise as the per-candidate
      comparison. Keep the aggregate/per-candidate distinction and the retained aggregate assertion;
      this is a status correction, not a deletion.
- [ ] `docs/ADEQUACY.md` §7.1: correct the sweep arithmetic from `f^3` to the quadratic
      `O(back × fwd)` in **both** places (the opening statement and sub-bullet (iii-a)), stating
      that `mid` has no periodicity and never participates, citing `SEARCH_COVERAGE.md` §3(b).
- [ ] `docs/ADEQUACY.md` §7.3: lead with both grid sizes rather than `back = mid = fwd = 1` alone;
      record that the comparison is per-candidate; record that each candidate's leg (iii) is a
      solver-free evaluation of the encoding's own emitted constraint list, with the retained
      aggregate assertion being the only check of the real Z3 *search* verdict.
- [ ] Add the direction claim at each surface where the tiers are described:
      `TRUST_PIPELINE.md`'s "The standing test for A2", `ADEQUACY.md` §7.3, `A2_GAP.md` §8,
      `SEARCH_COVERAGE.md` §1, `tests/README.md`'s `integration/` row for
      `test_certificate_a2_triangle.py`, and the module docstrings of
      `tests/integration/test_certificate_a2_triangle.py` and
      `tests/integration/test_search_period_coverage.py`.
- [ ] Reassess cost on that basis without narrowing anything: record that the 123.29 s
      `nb=nf=2` case is kept deliberately — the UNSAT direction is exactly where results are not
      independently checkable, so liveness evidence there is the only evidence available — and carry
      the existing margin caveat (123.29 s against a 300 s ceiling, assuming CI hardware no more
      than ~2.4× slower than the measuring host) with its already-recorded contingency of a
      deterministic stride, never a weakened assertion.
- [ ] Tighten `TRUST_PIPELINE.md`'s item-1 remaining-work row to "the only *independent* check"
      (the mandatory Python re-check survives in the live path — F3), and extend the item-2 row with
      Phase 6's measured decision.
- [ ] Add a remaining-work row recording the structural conformance check as a follow-on — that the
      emitted Z3 constraint set matches the (C1)-(C4) schema at the configured `(nb, nm, nf)`,
      linear in formula size, extending `tests/_pinned_eval.py`'s `full_constraints` and
      `tests/unit/test_pinned_eval.py`'s `TestOperatorInventoryIsClosed` /
      `TestAssignmentCoverage` — explicitly sequenced after items 1 and 2 because it is
      UNSAT-direction work. Do not build it.

**Timing**: 2 hours

**Depends on**: 6

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: the direction claim belongs at exactly seven surfaces (the four documents,
`tests/README.md`, and two test-module docstrings) enumerated above. Confirm at implementation time
by grepping for the tier vocabulary across `docs/` and `tests/`
(`grep -rn "Tier 1\|Tier 2\|two tiers\|grid pin" code/src/model_checker/theory_lib/bimodal/`) and
add any surface the grep finds that this list missed, recording the reconciliation.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` - §8 limit 3 discharged; direction claim
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` - §7.1 sweep arithmetic; §7.3 staleness and direction claim
- `code/src/model_checker/theory_lib/bimodal/docs/SEARCH_COVERAGE.md` - §1 direction claim
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` - standing-test direction claim; item-1 row wording; item-2 row extension; conformance follow-on row
- `code/src/model_checker/theory_lib/bimodal/tests/README.md` - `test_certificate_a2_triangle.py` row
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py` - module docstring
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_search_period_coverage.py` - module docstring

**Verification**:
- Diff read-through confirms every hunk is prose or docstring text, and that no assertion,
  parameter list, or marker in either test module changed.
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q` unchanged in
  outcome (docstring-only edits must not alter collection).
- The three already-applied `TRUST_PIPELINE.md` edits are still present verbatim after this phase's
  edits (re-grep each).
- No test is deleted, narrowed, skipped, or given a new skip marker:
  `git diff --stat` plus a read of every test-file hunk.

---

### Phase 8: Final gate, deferred findings, and summary [NOT STARTED]

**Goal**: The whole repository is green, and everything this task deliberately did not decide is
recorded where the owning task will find it.

**Tasks**:
- [ ] Run the full project gate: `PYTHONPATH=code/src pytest code/tests/ -v` and
      `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v`, including
      the `slow`-marked A2 cases.
- [ ] Run the bimodal suite once with no checker resolvable and once with one, confirming both
      paths are green and that the default (`verify: 'auto'`) never fails on absence.
- [ ] Record the deferred findings for the certificate-wire hardening task: `ADEQUACY.md` §6.2's
      and `TRUST_PIPELINE.md`'s trust-base "kernel-checked proof for that particular certificate"
      overclaim, with the accurate narrower claim stated; and whether `BIMODAL_LOGIC_COMMIT`'s
      contents should track the companion repository automatically.
- [ ] Record the incidental observations research surfaced but did not act on: the companion
      repository now has a `translate_sentence` executable and a
      `BimodalTools.TranslateSentenceMain` target, while this repository's ledger records a
      Lean-side translation as absent and deferred (obligation S4, out of scope here); and the
      `lean-toolchain` pin (`v4.33.0-rc1`) differs from the toolchain that built the measured
      binaries (4.27.0-rc1).
- [ ] Write the implementation summary, including Phase 6's measured decision and Phase 7's
      Scope-Hypothesis reconciliation.

**Timing**: 1 hour

**Depends on**: 3, 4, 5, 7

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:
- `specs/205_certifying_countermodel_architecture/summaries/01_certifying-countermodel-architecture-summary.md` - new

**Verification**:
- Both pytest invocations green, with the exact commands and counts recorded in the summary.
- The deferred findings and incidental observations appear in the summary with their owning task or
  obligation named.

## Testing & Validation

- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py -v` — resolver and handshake unit coverage, written before the module.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py -v` — all three output states plus `verify: 'required'` withholding plus `verify: 'off'`.
- [ ] The overclaim guard: no rendered output contains "kernel-checked proof".
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` green both with and without a resolvable checker.
- [ ] The three `_lean_check.py` consumers pass with a checkout and skip cleanly without one.
- [ ] `PYTHONPATH=code/src pytest code/tests/ -v` — the whole-project gate.
- [ ] Importing `semantic/checker.py` performs no subprocess call (probe is lazy).
- [ ] No test deleted, narrowed, or newly skipped; the retained aggregate assertion in `_assert_exhaustive_triangle_agrees` is unchanged.

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/semantic/checker.py` — production checker resolver, handshake, invocation.
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_checker.py` — resolver/handshake unit tests.
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_output_gate.py` — output-state and strictness tests.
- Modified: `semantic/core.py` (`verify` setting), `semantic/model.py` (gate + three renderings), `tests/_lean_check.py` (delegating), `tests/unit/test_structure.py` (updated print expectations).
- Documentation: `docs/SETTINGS.md` (new `## Certificate Verification` section), `docs/ADEQUACY.md` (§7.4 addition, §7.1 and §7.3 corrections), `docs/USER_GUIDE.md` (cross-reference), `docs/A2_GAP.md` (§8 limit 3 discharged), `docs/SEARCH_COVERAGE.md` (§1 direction claim), `docs/TRUST_PIPELINE.md` (direction claim, row wording, item-2 extension, conformance follow-on row), `tests/README.md`, two test-module docstrings.
- `specs/205_certifying_countermodel_architecture/summaries/01_certifying-countermodel-architecture-summary.md` — including Phase 6's packaging decision and the deferred findings for the wire task.

## Rollback/Contingency

- Phases 1, 2, 3, 4 are code; each commits per green sub-step, so reverting is a per-commit
  `git revert` of the offending sub-step, not a working-tree discard. Prefer that: sibling task 206
  shares this working tree, so a whole-tree rollback would take its work with it.
- If a genuine whole-tree rollback becomes necessary, snapshot first with
  `bash .claude/scripts/git-snapshot.sh 205 --allow-out-of-scope` (the deliberate whole-tree case
  the override exists for; see `context/contracts/recovery.md`'s rollback rung), then roll back.
  Never emit a bare reverting `git-snapshot.sh 205` as a routine checkpoint — for a defensive
  checkpoint before risky work use `--no-revert`.
- Phase 3 is the only phase that changes default user-visible behaviour. Its contingency is
  narrow: ship `verify` defaulting to `'off'` instead of `'auto'`, which keeps the label
  infrastructure and the tests while restoring exactly today's output. That is a one-line change,
  not a revert.
- Phase 6 changes a file in another repository. Its contingency is to restore
  `~/Projects/BimodalLogic/lakefile.toml` and record the measurement as deferred; nothing depends
  on the number except the packaging recommendation.
- Phases 5 and 7 are prose. A bad edit is reverted per file; no code depends on them.
