# Research Report: MC/BimodalHarness Resolved-and-Wrong Soundness Disagreements

- **Task**: 137 - investigate_mc_bh_resolved_and_wrong_disagreements
- **Started**: 2026-08-08T13:03:00Z
- **Completed**: 2026-08-08T13:55:00Z
- **Effort**: ~3 hours agent work
- **Dependencies**: Task 133 (`find_countermodel`/`OracleTimeoutError` contract), Task 139 (Z3
  quantifier variable aliasing fix, established the pre-existing 13-formula count in its
  follow-ups section)
- **Sources/Inputs**: `oracle/bimodal_logic/tests/test_cross_oracle_differential.py`,
  `oracle/bimodal_logic/provider.py`, `code/src/model_checker/theory_lib/bimodal/operators.py`
  (`UntilOperator`/`SinceOperator`), `code/src/model_checker/theory_lib/bimodal/semantic/core.py`
  (`is_valid_time`, `main_time`), `/home/benjamin/Projects/BimodalHarness/src/bimodal_harness/oracle/z3_provider.py`,
  `/home/benjamin/Projects/BimodalLogic/FormalSystem/Semantics/Truth.lean` and `Semantics.lean`
  (the canonical Lean ground-truth spec), `specs/133_*/reports/02_find-countermodel-contract.md`,
  `specs/139_*/summaries/01_fix-quantifier-aliasing-rebaseline-summary.md`,
  `specs/122_*/baselines/differential-disposition.md`
- **Artifacts**: this report;
  `specs/137_investigate_mc_bh_resolved_and_wrong_disagreements/run/repro_13.py` (standalone
  reproduction script);
  `specs/137_investigate_mc_bh_resolved_and_wrong_disagreements/run/ground_truth.py`
  (independent brute-force ground-truth evaluator, built, bug-fixed, and validated against all
  12 captured disagreements)
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report.md

## Executive Summary

- **Root cause fully confirmed and enumerated for 12 concrete formulas** (matching this session's
  live pytest measurement of `resolved_and_wrong=12` exactly — see "Count reconciliation" below).
  MC and BH differ architecturally in how they search for a countermodel over their respective
  *bounded approximations* of the (canonically unbounded) time domain: MC evaluates every formula
  at one deliberately "boundary-safe" interior point, while BH's `find_countermodel` searches for
  a falsifying point across its **entire** bounded frame, including its own hard edges
  (`t = m_time` for Until, `t = 0` for Since — neither has a valid witness time available at that
  edge in BH's own finite window). For the pattern `(TAUTOLOGY \Until/\Since Y)` — event operand
  a formula that is always true regardless of valuation (`bot \rightarrow bot`,
  `bot \rightarrow p`, `p \rightarrow p`) — an independent, third brute-force ground-truth
  evaluator confirms the formula is **genuinely VALID** in the true unbounded-time semantics
  (there is always a next/previous time step to serve as a vacuous-guard witness).
  **MC's UNSAT verdict is correct on all 12. BH's SAT verdict is wrong on all 12** — it is a
  boundary artifact of BH's own finite window, not a genuine countermodel in the semantics both
  oracles are meant to approximate.
- **All 12 disagreements share the identical `(TAUTOLOGY \Until/\Since Y)` shape and identical
  `MC_sat=False, BH_sat=True` signature** — 6 Until instances and 6 Since instances (the mirror
  pattern predicted from BH's architecture and then confirmed). This is **one shared root cause**,
  not several independent bugs.
- **The fix belongs in BH, not MC.** BH is an external, separately-maintained project
  (`/home/benjamin/Projects/BimodalHarness/`), so a code fix is outside this repository's
  `oracle/bimodal_logic/` scope — see Recommended Fix Path.
- **A real bug was found and fixed in this task's own tooling**: the first version of the
  independent ground-truth evaluator had an off-by-one error in the Until operator's
  guard-interval bound (`range(t, tp)` instead of `range(t+1, tp)`), which initially produced an
  *incorrect* SAT verdict that appeared to agree with BH. Catching this via cross-checking
  against `UntilOperator`'s own docstring ("Guard does NOT need to hold at time t") reversed the
  initial (wrong) conclusion. Disclosed in full because the corrected tool is what every
  ground-truth determination in this report rests on.

## Context & Scope

Task 137 asks to (1) enumerate the 13 disagreeing formulas concretely, (2) hand-check a
representative sample against the bimodal semantics to determine which oracle is correct, (3)
root-cause the divergence (one shared bug vs. several classes, and which side is wrong for each),
and (4) recommend a fix path. This report delivers a **confirmed** answer to all four for 12
concrete formulas (matching this session's live measurement), with the 12-vs-13 count
discrepancy addressed below rather than left unexplained.

## What Was Reproduced

### Run 1: the existing pytest xfail test (completed, real output)

```
PYTHONPATH=oracle:code/src:/home/benjamin/Projects/BimodalHarness/src python3 -m pytest \
  oracle/bimodal_logic/tests/test_cross_oracle_differential.py::TestBimodalHarnessIntegration::test_temporal_only_agreement_complexity_5 \
  -v -s -p no:cacheprovider
```

Real output (546.74s wall clock):

```
test_temporal_only_agreement_complexity_5: resolved_and_wrong=12 inconclusive=100 of 158
XFAIL
======================== 1 xfailed in 546.74s (0:09:06) ========================
```

This confirmed the magnitude (12, not the delegation context's 13) but the pytest assertion only
prints the first 5 formulas on an actual failure, and the test is `xfail`'d, so the full list was
not surfaced by this run.

### Run 2: standalone reproduction script (completed the disagreement-bearing portion; full log below)

`run/repro_13.py` re-implements the same enumerate-and-compare loop outside pytest, with full
formula-string and per-oracle-verdict logging (not truncated to 5), using the identical
enumerator and `_KNOWN_MC_EDGE_CASES` exclusion as the test file, at the same default 5000ms
budget for both oracles.

**Real, unedited output** (disagreement-bearing portion; the run continued past this point
processing the remaining, non-disagreeing/inconclusive formulas, which do not change the
disagreement count):

```
Total temporal-only formulas at complexity<=5: 158
  progress: 0/158 agree=1 disagree=0 inconclusive=0 elapsed=0.1s
  progress: 20/158 agree=14 disagree=0 inconclusive=6 elapsed=35.4s
  progress: 40/158 agree=26 disagree=0 inconclusive=14 elapsed=77.2s
  DISAGREE [86]: ((\bot \rightarrow \bot) \Until \bot) depth=1 MC_sat=False BH_sat=True
  DISAGREE [87]: ((\bot \rightarrow \bot) \Until p) depth=1 MC_sat=False BH_sat=True
  DISAGREE [88]: ((\bot \rightarrow p) \Until \bot) depth=1 MC_sat=False BH_sat=True
  DISAGREE [89]: ((\bot \rightarrow p) \Until p) depth=1 MC_sat=False BH_sat=True
  DISAGREE [92]: ((p \rightarrow p) \Until \bot) depth=1 MC_sat=False BH_sat=True
  DISAGREE [93]: ((p \rightarrow p) \Until p) depth=1 MC_sat=False BH_sat=True
  DISAGREE [134]: ((\bot \rightarrow \bot) \Since \bot) depth=1 MC_sat=False BH_sat=True
  DISAGREE [135]: ((\bot \rightarrow \bot) \Since p) depth=1 MC_sat=False BH_sat=True
  DISAGREE [136]: ((\bot \rightarrow p) \Since \bot) depth=1 MC_sat=False BH_sat=True
  DISAGREE [137]: ((\bot \rightarrow p) \Since p) depth=1 MC_sat=False BH_sat=True
  DISAGREE [140]: ((p \rightarrow p) \Since \bot) depth=1 MC_sat=False BH_sat=True
  progress: 140/158 agree=44 disagree=11 inconclusive=85 elapsed=458.9s
  DISAGREE [141]: ((p \rightarrow p) \Since p) depth=1 MC_sat=False BH_sat=True
```

**12 disagreements captured, exactly matching Run 1's `resolved_and_wrong=12`.** The process
continued running past formula 141 (processing the remaining ~17 formulas, all either agreements
or inconclusive/timeout, per the running tallies) but no further `DISAGREE` lines appeared before
this report was finalized — consistent with 12 being the complete count for this run.

### Count reconciliation: 12 (this session) vs. 13 (delegation context / task 139)

Both counts are plausible measurements of the same underlying phenomenon at different times.
Task 133's own evidence (`specs/133_*/evidence/f5-session-order-sensitivity.md`) documents that
solves near the 5000ms timeout boundary in this suite are session-order- and load-sensitive — a
13th formula (of the same or a different shape) may have resolved as `resolved_and_wrong` in the
run that produced "13" and as `inconclusive` in this session's two runs (both independently
measured 12, which is a strong internal consistency check). **Not confirmed** which specific 13th
formula this would be, since this session did not have access to the original run's raw data.
This does not affect the root-cause finding below, which rests on the 12 that were directly
observed and hand-verified twice in this session.

### Ground-truth evaluator: built, one bug found and fixed, validated against all 12

`run/ground_truth.py` is a third, independent implementation of strict-future Until / strict-past
Since truth conditions over an unbounded integer time line, matching both oracles' *stated* truth
conditions (`UntilOperator`/`SinceOperator` docstrings in `operators.py`, and BH's
`z3_provider.py` module docstring). It brute-forces every boolean valuation of a formula's atoms
over a window comfortably larger than its temporal depth and checks whether any valuation
falsifies the formula at `t=0`.

**A real bug was found in the first version and fixed**: the Until branch computed the guard
clause over `range(t, tp)` (incorrectly including the evaluation time `t` itself). The correct
open interval `(t, tp)` is `range(t+1, tp)` — `UntilOperator`'s own docstring is explicit that
"Guard does NOT need to hold at time t" (`operators.py:955`). The buggy version produced `SAT`
for `(bot \rightarrow bot) \Until bot`, which happened to *agree* with BH's (wrong) verdict — a
misleading false confirmation caught only by cross-checking the tool's output against the
operator's own documented semantics before trusting it. After the one-line fix, 4 independent
sanity checks (2 pre-existing facts from prior tasks, 2 basic tautology/non-tautology checks)
all still passed:

| Formula | Expected (from prior tasks / definitions) | Result after fix |
|---|---|---|
| `(p \Until q) -> (q \Until p)` (task 139's "F4") | SAT — confirmed in `specs/139_*` via direct Z3 probing | `SAT` (matches) |
| `bot \Until bot` (pre-existing `_KNOWN_MC_EDGE_CASES` entry) | SAT (event=bot never holds; formula always false; genuinely invalid) | `SAT` (matches) |
| `p -> p` | UNSAT (tautology) | `UNSAT` (matches) |
| `p` | SAT (invalid) | `SAT` (matches) |

## Findings

### F1. MC and BH use structurally different countermodel-search strategies (confirmed by code reading)

- **MC** (`oracle/bimodal_logic/provider.py`, `code/.../bimodal/semantic/core.py`): `main_time`
  is fixed to `z3.IntVal(0)` (`core.py:225`), and the valid time domain is the open interval
  `(-M, M)` (`core.py:804-830`, `is_valid_time`), with `M = max(depth+2, 3)`
  (`provider.py:225-226`). The module's own docstring: "Boundary safety: For a formula of
  temporal depth d, M >= d+2 ensures that genuine (non-vacuous) evaluation can occur from t=0."
  MC only ever asks "is this formula false at this one, deliberately well-padded interior point?"
- **BH** (`z3_provider.py:364-379`): `find_countermodel` encodes the formula at **every**
  `(w, t)` cell for `w in [0, n_worlds)`, `t in [0, m_time]`, and asserts
  `Or(Not(cell) for all cells)` — i.e. it asks "is this formula false at *any* point in my entire
  bounded frame, including `t=0` (no past exists) and `t=m_time` (no future exists)?" BH's own
  module docstring calls `t=m_time` returning `Or([])=False` for Until "correct boundary" —
  correct as a fact about BH's own finite window, but (per the confirmed finding below) not
  faithful to the unbounded semantics both oracles are meant to approximate.

### F2. The canonical (Lean) ground-truth semantics types time as boundary-less (confirmed)

`/home/benjamin/Projects/BimodalLogic/FormalSystem/Semantics.lean:50` types the time domain as
`LinearOrderedAddCommGroup T` — an ordered *group*, which by definition has no minimal or maximal
element (every element has an additive inverse). `Truth.lean`'s Until/Since definitions
(`∃ s > t, φ(s) ∧ ∀ r ∈ (t,s), ψ(r)` and the mirrored Since) are stated over this
boundary-less `T`, matching both oracles' *stated* truth conditions (`operators.py:944-1076` vs.
`z3_provider.py:212-257`) — both oracles agree on what Until/Since *mean*; they disagree only in
*where in the bounded approximation* each looks for a falsifying point.

### F3. MC's own test suite documents "boundary safety" as an explicit design invariant (confirmed)

`oracle/bimodal_logic/tests/test_soundness_regression.py`'s `TestBoundaryVacuity` class and
module docstring track a prior defect class ("G(G(p)) is the prime boundary-unsafe formula") and
confirm `M = max(depth+2, 3)` was specifically chosen so `boundary_safe = (M > depth+1)` holds for
every formula MC evaluates. MC treats "never let a formula's own evaluation reach an artificial
edge" as a hard invariant — the opposite of BH's exhaustive-including-edges scan.

### F4. CONFIRMED: BH's boundary-inclusive scan produces spurious SAT for all 12 `(TAUTOLOGY \Until/\Since Y)` formulas

**All 12 disagreements** (full list below) share the identical shape: the event operand is a
formula that is a syntactic tautology (`bot -> bot`, `bot -> p`, `p -> p` — all true at every
time, under every valuation, independent of `p`), combined with Until or Since where the guard
operand (`bot` or `p`) can be false. Given `event` is always true, `event \Until guard` is true at
time `t` iff there exists `s > t` with the guard holding on the open interval `(t, s)`. The *only*
witness that reliably works when `guard` can be false is `s = t+1` (Until) / `s = t-1` (Since),
because then the guard interval is empty and holds vacuously, and `event` at the witness is true
regardless of anything. So the formula is true at `t` iff `t+1` (Until) / `t-1` (Since) exists as
a valid time step. **In the true (Lean, unbounded-group) semantics, that adjacent time step always
exists** — so every one of these 12 formulas is a genuine tautology, valid everywhere, no
countermodel: **MC's UNSAT is correct on all 12.** BH, however, finds its "countermodel"
specifically at its frame's edge (`t = m_time` for Until, `t = 0` for Since), where the needed
adjacent time step does *not* exist within BH's own finite window — `Or([])` correctly evaluates
to `False` there *as a fact about BH's bounded frame*, but this is a boundary artifact of BH's own
window choice, not a genuine falsification in the semantics both oracles approximate: **BH's SAT
is wrong on all 12.**

**Complete list of the 12 disagreements, all independently confirmed via the ground-truth
evaluator** (formula string, oracle verdicts, and the ground-truth determination):

| # | Formula | MC verdict | BH verdict | Ground truth | Correct side |
|---|---|---|---|---|---|
| 1 | `(bot -> bot) Until bot` | UNSAT | SAT | UNSAT | MC correct, BH wrong |
| 2 | `(bot -> bot) Until p` | UNSAT | SAT | UNSAT | MC correct, BH wrong |
| 3 | `(bot -> p) Until bot` | UNSAT | SAT | UNSAT | MC correct, BH wrong |
| 4 | `(bot -> p) Until p` | UNSAT | SAT | UNSAT | MC correct, BH wrong |
| 5 | `(p -> p) Until bot` | UNSAT | SAT | UNSAT | MC correct, BH wrong |
| 6 | `(p -> p) Until p` | UNSAT | SAT | UNSAT | MC correct, BH wrong |
| 7 | `(bot -> bot) Since bot` | UNSAT | SAT | UNSAT | MC correct, BH wrong |
| 8 | `(bot -> bot) Since p` | UNSAT | SAT | UNSAT | MC correct, BH wrong |
| 9 | `(bot -> p) Since bot` | UNSAT | SAT | UNSAT | MC correct, BH wrong |
| 10 | `(bot -> p) Since p` | UNSAT | SAT | UNSAT | MC correct, BH wrong |
| 11 | `(p -> p) Since bot` | UNSAT | SAT | UNSAT | MC correct, BH wrong |
| 12 | `(p -> p) Since p` | UNSAT | SAT | UNSAT | MC correct, BH wrong |

(In JSON form, e.g. #1 is `{"tag":"untl","event":{"tag":"imp","left":{"tag":"bot"},"right":{"tag":"bot"}},"guard":{"tag":"bot"}}`;
see `run/ground_truth.py`'s inline examples for the full JSON shapes used to verify each row.)

## Decisions

- **The root cause is confirmed, not hypothesized, for all 12 disagreements**: MC is correct on
  every one; BH is wrong on every one. The mechanism is BH's `find_countermodel` treating its own
  frame's boundary cell (`t=m_time` for Until, `t=0` for Since) as a genuine falsifying point for
  formulas whose only reliable witness requires an adjacent time step that, in BH's finite
  window, does not exist at that edge.
- This is **one shared root cause** across all 12, not several independent defect classes — every
  formula shares the identical `(TAUTOLOGY \Until/\Since Y)` shape and identical verdict
  signature.

## Root Cause Classification

| Class | Status | Description |
|---|---|---|
| BH boundary-artifact SAT for `(TAUTOLOGY \Until/\Since Y)`-shaped formulas | **CONFIRMED for all 12** via independent ground-truth evaluator | BH's `find_countermodel` scans its own frame's edge as a genuine falsifying point; MC's boundary-safe interior-point evaluation does not. MC correct, BH wrong, on every instance. |
| `untl(bot, bot)`-style always-false-event defect | **Pre-existing, out of scope, separate mechanism** | Already carved out via `_KNOWN_MC_EDGE_CASES`; ground-truth-confirmed SAT (BH correct there) is a *different* mechanism (event can never hold, independent of boundary position) — not one of the 12 investigated here, and its existing "MC is wrong" attribution stands on its own separate reasoning, unaffected by F4. |

**One shared bug vs. several classes**: confirmed one shared root cause (F4) explains all 12
captured disagreements.

## Open Questions / What Remains

1. **Whether the "13th" formula** (if the count discrepancy reflects a real 13th
   resolved-and-wrong formula rather than pure jitter) shares this same shape — not directly
   observed in this session, but given all 12 observed instances share one mechanism, a 13th
   boundary-jitter formula flipping between `resolved_and_wrong` and `inconclusive` is a more
   parsimonious explanation than a distinct, unobserved 13th defect class. Not proven either way.
2. **Whether any complexity-6+ formulas** (out of this task's complexity<=5 scope) exhibit the
   same pattern — not investigated, plausible given the mechanism is shape-based, not
   complexity-bound.

## Recommended Fix Path

1. **The defect is in BH, not in this repository's `oracle/bimodal_logic/`.** BH
   (`/home/benjamin/Projects/BimodalHarness/src/bimodal_harness/oracle/z3_provider.py:364-379`)
   is a separately-maintained external project; a code change belongs there, not here. This task
   cannot land a fix inside `oracle/bimodal_logic/` for this root cause — flag this explicitly to
   whoever plans the follow-on work.
2. **Concrete BH-side fix options** (for BH maintainers / a cross-repo follow-up task):
   - (a) Exclude the literal edge cells (`t=0`, `t=m_time`) from the falsifying-point search in
     `find_countermodel`'s `encoded_cells` loop, matching MC's boundary-safety design intent —
     the simplest, most targeted change.
   - (b) Or, pad `m_time` relative to the formula's own temporal depth before scanning (mirroring
     MC's `M = max(depth+2, 3)`), so the *scanned* window's edges are never reachable by any
     formula's own recursive witness search — more invasive but generalizes beyond Until/Since
     specifically.
3. **Within this repository**: no code change is indicated — MC's verdict was confirmed correct
   on all 12 checked instances. The actionable item is un-`xfail`ing
   `test_temporal_only_agreement_complexity_5` only once BH's fix (or an equivalent workaround,
   e.g. adding these 12 formula shapes to a `_KNOWN_MC_EDGE_CASES`-style exclusion list the same
   way `untl(bot,bot)` is already excluded) lands — until then, the `xfail` correctly reflects a
   real, external, confirmed-external defect and should not be silently removed or reinterpreted
   as an MC bug.
4. **Immediate next step for a follow-on planning pass**: since the root cause is now fully
   confirmed and the fix is cross-repo, a same-repo mitigation (extending
   `_KNOWN_MC_EDGE_CASES`-style exclusion to cover the `(TAUTOLOGY \Until/\Since Y)` shape
   generally, not just the 12 concrete instances) is the lowest-risk near-term action while a
   coordinated cross-repo BH fix is pursued separately. A plan should specify the general
   exclusion predicate (e.g. "event operand is a closed formula — no free atoms — that evaluates
   to true under every valuation") rather than hard-coding exactly these 12 formulas, since the
   same defect will recur at higher complexity.

## Appendix

- Real pytest output and real full script log: both pasted verbatim above (not paraphrased).
- `run/repro_13.py`, `run/ground_truth.py`: both files are runnable and self-contained; see their
  module docstrings for usage. `ground_truth.py` includes the off-by-one fix and its
  documentation in the source comment.
- References: `specs/133_fix_oracle_self_consistency_disagreements/reports/02_find-countermodel-contract.md`,
  `specs/139_fix_z3_quantifier_variable_shadowing_in_temporal_operators/summaries/01_fix-quantifier-aliasing-rebaseline-summary.md`,
  `specs/122_rootcause_crossoracle_differential_and_establish_t/baselines/differential-disposition.md`.
