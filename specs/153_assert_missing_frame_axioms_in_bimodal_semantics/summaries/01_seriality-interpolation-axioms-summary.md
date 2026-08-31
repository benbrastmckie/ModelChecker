# Implementation Summary: Assert Seriality and Interpolation in BimodalSemantics

- **Task**: 153 - Assert missing frame axioms in bimodal semantics
- **Plan**: `plans/01_seriality-interpolation-axioms.md`
- **Status**: PARTIAL -- both axioms implemented, tested, and documented per plan; landing blocked
  by an unresolved cost regression on two countermodel examples (`BM_CM_4`, `BM_CM_1`).

## What was implemented

- `build_seriality_constraint` and `build_interpolation_constraint` added to
  `code/src/model_checker/theory_lib/bimodal/semantic/core.py`, Skolemized per the research
  report's mandate (single top-level `ForAll` each, witness functions eliminate the existentials,
  no `z3.Exists` in either -- confirmed by direct source inspection).
- Both wired into `build_frame_constraints`'s returned list after `forward_comp` and before
  `*skolem_abundance`, taking the constraint count from 11 to 13 (M<=2).
- `core.py`'s docstrings and the `task_restriction` soundness-analysis comment corrected from
  "three TaskFrame axioms" to five, with item numbers renumbered (7-11) and a stated free/asserted
  ledger pointer to ARCHITECTURE.md.
- New `### Frame-Class Axioms` subsection in `bimodal/docs/ARCHITECTURE.md`: a 7-row
  constraint-level table (5 asserted, 2 free) with per-row citations, an explicit note resolving
  the "asserted axiom count" ambiguity (5/2 at the Z3-row level vs. 2/2 at the paper-axiom level),
  and a duration-domain-guard footnote recording the bounded-window vs. unbounded-`\Z` gap as open.
- New/renamed tests: `TestFrameConstraintsJointSatisfiability`, `TestSeriality`,
  `TestInterpolation` in `test_frame_constraints.py`; `TestSerialityPostHoc`,
  `TestInterpolationPostHoc` in `test_frame_class_mapping.py`;
  `test_three_taskframe_axioms_present_in_frame_constraints` renamed to
  `test_five_taskframe_axioms_present_in_frame_constraints`. Both files: 27/27 passing, 19.08s.

## Phase 2: definitional-reachability alternative -- measured, not adopted

Prototyped `task_rel` as bounded R-reachability (unrolled disjunction over the `2M-1` duration
window, Skolemized chain witnesses, no nested `Exists`, no `z3.TransitiveClosure`) via a
process-local `ReachabilitySemantics` subclass; `core.py` untouched by this measurement. Result on
the six-example subset: `BM_TH_3`/`BM_TH_4` stay `match` at comparable timing (0.05s/0.05s vs.
baseline 0.11s/0.04s), `BM_TH_1`/`BM_TH_2` unchanged `inconclusive`-at-30s, no Z3-specific API
needed (had to drop one existing `MultiPattern` hint on `forward_comp`).

**Outcome: "go" on the narrow macro-substitution question measured, but this does not cover the
redesign's actual soundness payoff** (deriving `nullity_identity`/`converse`/`forward_comp` as
theorems rather than assertions, which would require a materially harder shared-witness design not
attempted here). Per the plan's scope call, this does not expand the task -- both axioms were
implemented against the Skolemized direct-fix regardless. **Recommended as a follow-on task** if
the reachability redesign is pursued, with this measurement's scope caveat carried forward.

## Blocker: BM_CM_4 cost regression, not resolved

Full detail in `baselines/README.md`'s "Phase 7" section; summarized here.

**The finding (well-evidenced)**: `BM_CM_4` (N=2, M=2 countermodel example, `\Diamond A -> \past A`)
regresses from a clean, fast, decided countermodel (4.07s `match` pre-change; 18.26s-20.29s in the
task 152 baseline and this task's own Phase 1 pre-change run) to `inconclusive` at its own
`max_time=120` with both new axioms present. Four independent measurements against the real,
committed `build_seriality_constraint`/`build_interpolation_constraint` methods all agree:
`pytest -k "BM_CM_4"` (120.78s, FAILED), a direct `run_enhanced_test` call (120.37s,
`inconclusive`), the full 52-example Phase 7 suite run (120.36s, `inconclusive`), and an isolation
probe at a shorter 40s budget (40.21s, `inconclusive`). This is a **cost** regression, not a shown
soundness/verdict flip: the axioms have not been shown to eliminate `BM_CM_4`'s countermodel, only
to make the search not finish within budget.

`BM_CM_1` (the pre-existing, documented-`unstable` example) shows the same before/after direction
(decided `match` pre-change, `inconclusive` at its own `max_time=60` post-change), but its
isolation table is **non-monotonic and contradicts `BM_CM_4`'s pattern** (its `both` configuration
decides *faster*, 16.43s, than `neither`, 22.55s; its `interpolation_only` configuration is the one
that fails to decide). This rules out stating a single general mechanism ("the two axioms interact
superlinearly") -- the honest statement is that Z3's solving cost here is highly sensitive to the
exact constraint set and to incidental formula-construction details in ways that are not
compositional, corroborated independently by a harness artifact discovered mid-investigation
(symbol naming alone -- `serial_succ` vs. `serial_succ_inline` -- changed `BM_CM_4` from
120s-`inconclusive` to 4.56s-`match`). `BM_CM_1`'s own `neither` baseline in this isolation run
(22.55s) is already well above its documented median (~7-8s), confirming it is inherently
high-variance independent of this task's changes; its `unstable` marker is not re-adjudicated.

**`TN_CM_2`** (`inconclusive` at 10.1s post-change) is confirmed unchanged -- already `inconclusive`
pre-change in both the task 152 baseline (10.09s) and this task's own Phase 1 run (10.1s). Not a
new or affected example. **`BM_TH_1`/`BM_TH_2`** remain unchanged `inconclusive`-at-~30.3s in all
three sources -- per the plan's own rule, reported as no signal, never as evidence of no
regression. **`BM_TH_3`/`BM_TH_4`** stay `match`, exactly as the research report's Skolemized
benchmark predicted.

**Mitigation attempted**: an explicit Z3 pattern anchoring `build_interpolation_constraint` to its
premise's ground `task_rel` term (mirroring `build_forward_comp_constraint`'s existing
`MultiPattern` convention) did not recover a decided result on `BM_CM_4` (still `inconclusive` at
40s). Guard-tightening was not attempted separately: both axioms' guards are already exactly as
tight as their mathematical content allows (no slack to remove without changing what the axiom
means).

**What settling the mechanism would need**: repeated runs per configuration to characterize the
variance distribution, distinguishing genuine superlinear interaction from Z3 search-cost variance
that happens to correlate with constraint-set changes. This is beyond this task's budget and is
recommended as a follow-on.

**Why the plan's own documented fallback was not applied**: the plan's rollback section names
"land Seriality alone, defer Interpolation" as the safe fallback for exactly this failure mode. It
was not applied here because (a) isolation shows neither axiom alone is responsible for `BM_CM_4`'s
regression -- both individually stay decided at modest cost -- so dropping Interpolation alone
would not obviously fix it and would also not obviously be necessary; and (b) it would silently
narrow this task's shipped scope (both axioms asserted, per the task's own stated definition of
done) without the user's decision. Both axioms remain in the implementation as specified; this is
recorded as an open scope decision for the user, not resolved unilaterally.

## Plan Deviations

- Phase 1's harness script includes a `with_new_axioms` arm (inline reconstruction) that was
  discovered during Phase 7 to diverge from the real committed methods due to Z3 MBQI sensitivity
  to symbol naming -- documented in `baselines/README.md` with a correction note; Phase 7's actual
  post-change run used the `baseline` arm against the post-Phase-4 tree instead.
- Phase 7's "full bimodal suite green" verification item is not met: 5 failures (`BM_CM_1`,
  `BM_CM_4`, and 3 `test_bound_var_counter_isolation.py` parametrizations of `BM_CM_4`), all
  attributable to the characterized cost regression, none new or unexplained.
- The broader `code/tests/ -v` suite was not run in this session given the time budget -- recorded
  as incomplete, not assumed clean.
- No axiom was dropped, no example's `max_time` was raised, no test was marked `unstable` or
  `xdist_serial`, and no expected verdict was adjusted to route around the regression. The
  regression is reported as found, not engineered away.

## Out-of-scope follow-ups (flagged, not fixed)

- `oracle/bimodal_logic/provider.py:17`-`70` carries a frame-axiom table quoting `core.py`'s
  now-superseded three-axiom claim (outside this task's `file_scope`) and will diverge further as
  `core.py`'s docstring has now changed. Needs a follow-on task.
- The definitional-reachability redesign (Phase 2) is measured but not implemented; a follow-on
  task should carry the theorem-derivation half of that measurement forward if pursued.
- The BM_CM_4/BM_CM_1 cost-regression mechanism needs a repeated-runs variance study to settle
  whether it is a genuine axiom interaction or Z3 search-cost sensitivity, or both.
- The duration-domain gap (bounded window `(-M, M)` vs. the paper's unbounded `\Z`) remains
  recorded, not resolved, per Deliverable 4's own scope.

## Artifacts

- `specs/153_assert_missing_frame_axioms_in_bimodal_semantics/baselines/` -- regression harness,
  pre-change and post-change verdict JSON, reachability-alternative measurement, README with full
  Phase 7 diff and flip accounting.
- `specs/153_assert_missing_frame_axioms_in_bimodal_semantics/handoffs/` -- per-phase handoffs.
- Modified: `code/src/model_checker/theory_lib/bimodal/semantic/core.py`,
  `code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md`,
  `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_constraints.py`,
  `code/src/model_checker/theory_lib/bimodal/tests/unit/test_frame_class_mapping.py`.
