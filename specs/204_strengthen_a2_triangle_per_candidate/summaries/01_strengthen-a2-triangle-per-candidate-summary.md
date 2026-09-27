# Implementation Summary: Per-Candidate A2-Triangle Leg (i)/(iii) Comparison

- **Task**: 204 - strengthen_a2_triangle_per_candidate
- **Status**: [COMPLETED]
- **Started**: 2026-09-27T06:42:07Z
- **Completed**: 2026-09-27T21:29:28Z
- **Effort**: ~6.5 hours (matches plan estimate)
- **Dependencies**: 195 (research complete; concurrent implementation coordinated via territory contract, no collision)
- **Artifacts**: plans/01_strengthen-a2-triangle-per-candidate.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Replaced the one-bit aggregate leg (i)/(iii) comparison in the A2-triangle encoding-completeness
test (`test_certificate_a2_triangle.py`, `docs/ADEQUACY.md` section 7.3) with a per-candidate
comparison: for every enumerated candidate, `certificate.recheck`'s verdict is now checked
against a solver-free, compile-once evaluation of the encoder's own emitted Z3 constraint set,
raising on the first divergence rather than only comparing SAT/UNSAT totals. All five plan phases
completed and committed; the strengthened comparison found no genuine A2 divergence across all
six Tier 1 cases.

## What Changed

- New `code/src/model_checker/theory_lib/bimodal/tests/_pinned_eval.py`: a compile-once,
  interpret-many evaluator (`compile_constraints`/`CompiledConstraints`) for the encoder's closed
  six-operator Z3 constraint set (`And`, `Or`, `Not`, `Implies`, `BoolRef == BoolRef`, `AtMost`),
  plus `PinnedAssignmentBuilder` -- the exact inverse of `BimodalSemantics.extract_certificate` --
  which parses each interned atom name into a typed resolver once per structure and projects a
  candidate's data into a preallocated assignment row with no per-candidate string hashing.
  `full_constraints(structure)` reconstructs the true, post-`finalize_certificate` constraint set
  (see Plan Deviations).
- New `code/src/model_checker/theory_lib/bimodal/tests/unit/test_pinned_eval.py`: 50 unit tests
  covering all six operators (both polarities, degenerate 0/1-arg `And`/`Or`, `AtMost`'s bound
  pinned against a solver-backed cross-check), loud-failure paths (unsupported operator,
  unpopulated atom, atom-name collision), the closed operator-inventory assertion, exact
  assignment-coverage assertion, and the extracted-certificate round-trip self-check -- all
  green.
- Modified `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py`:
  `_run_exhaustive_triangle` now compiles the encoder's constraint set once, binds an assignment
  builder once, and compares legs (i) and (iii) per candidate inside the existing enumeration
  loop, raising immediately on the first divergence with the candidate, the disagreeing side, and
  the offending constraint or `recheck` failure entries.
  `_assert_exhaustive_triangle_agrees` additionally cross-checks the pinned-accepted and
  recheck-accepted totals. The existing aggregate assertions are retained unchanged. Module and
  class docstrings updated with the measured per-candidate-comparison wall-clock figures and the
  tiering decision.

## Decisions

- Tier placement decided from measurement, not the research report's estimate: both `slow`-marked
  boxed cases stay unconditional (17.77s and 123.29s under CI's exact invocation shape over the
  real repository target set), since the measured ~1.91x multiplier matched the report's ~2x
  estimate rather than exceeding it, and 123.29s leaves ~59% headroom under the 300s ceiling. No
  candidate enumeration was narrowed.
- The host-speed margin that headroom assumes (~2.4x, `300s / 123.29s`) is documented explicitly
  in `TestExhaustiveTriangleWithBox`'s docstring rather than left implicit, per the orchestrator's
  cross-check note that CI hardware speed relative to the implementation host is an unverified
  assumption.
- The existing aggregate assertion is retained alongside the new per-candidate one (not replaced):
  they check different facts (the emitted constraint set vs. the real Z3 search verdict), per the
  plan's Non-Goals.

## Plan Deviations

- **Phase 2, `PinnedAssignmentBuilder` construction (design change, not a scope reduction)**: the
  plan's literal design ("every slot x every closure formula") produces atom names the compiled
  constraints never reference (e.g. a plain `Atom` is never bound directly at a position, only as
  an `Untl`/`Snce` neighbour or a premise/conclusion target) -- caught immediately by the
  coverage assertion the same phase requires (`missing=[] stray=[...]`). Fixed by inverting the
  direction: the builder parses each of the compiled `atom_index`'s own key strings into a typed
  resolver once per structure, so the produced key set is exactly `atom_index`'s key set by
  construction. Documented inline in the plan at Phase 2.
- **Phase 3, constraint-set source (harness bug found and fixed, not an encoder finding)**:
  compiling literally against `structure.model_constraints.all_constraints`, as the plan's own
  Phase 3 task list named it, manufactured a false per-candidate divergence on the very first
  Tier 1 case. Root cause: `ModelConstraints.__init__` computes `all_constraints` via list `+` at
  construction time, before `BimodalSemantics.finalize_certificate()` (the bulk of the real
  encoding) extends `frame_constraints` in place -- `all_constraints` stays frozen at 1 constraint
  while the real, solved set has 13. Confirmed against `models/structure.py`'s own solve path,
  which reads `frame_constraints` directly, never `all_constraints`. Fixed by adding
  `_pinned_eval.full_constraints(structure)`, which reconstructs the true set post-construction,
  and using it throughout (including the Phase 1/2 unit tests). Documented inline in the plan at
  Phase 3; not reported as an A2 finding, since it is a defect in this task's own new test
  harness, not in the encoder under test.

## Impacts

- The A2-triangle differential now catches a candidate-level divergence that happens to cancel
  out in the aggregate SAT/UNSAT totals -- a strictly stronger guarantee than before this task,
  with no weakening of the pre-existing aggregate assertion.
- No production (`semantic/`, `models/`) source file was touched; this task strengthens a test
  differential only.
- `_pinned_eval.py` is reusable test-support infrastructure for any future solver-free
  translation-validation work over this encoder's constraint set (the report's own Context
  Extension Recommendation, still open -- see Follow-ups).

## Findings

**No genuine A2 per-candidate divergence was found.** `pinned_accepted == accepted` held for all
six Tier 1 cases (the two box-free closures at both grid sizes, and the two single-box closures
at both grid sizes) across every run performed in this task: Phase 3's box-free `-m "not slow"`
run, Phase 4's module-alone and CI-shaped `-n 4` runs, and Phase 5's full bimodal suite and
repository-gate runs. This is itself a meaningful result: A2's per-candidate biconditional (every
emitted constraint holds for a candidate iff `recheck` accepts it) held exactly, not merely in
aggregate, for every candidate in every tested closure and grid combination -- strengthening
confidence in the encoder beyond what the prior aggregate-only comparison could show. The one
apparent divergence encountered during Phase 3 was traced to this task's own harness defect (see
Plan Deviations), not the encoder, and was fixed before any tier was finalized.

## Follow-ups

- `docs/ADEQUACY.md` section 7.3 / `A2_GAP.md`: record that leg (iii) is now checked per
  candidate, not only in aggregate. Deferred because task 195's concurrent implementation owns
  edits to those same sections (Non-Goals); a second concurrent editor was avoided deliberately.
- Research report's Context Extension Recommendation: a short context note (e.g. under
  `context/project/python/`) on the compile-vs-interpret cost distinction for solver-free Z3
  clause evaluation -- this task's own `_pinned_eval.py` is now a concrete worked example of the
  pattern, for any future solver-free translation-validation work (the report names task 195's
  Stage 2b round-trip as a likely reuser).
- `models/structure.py:344-349`'s debug print (`constraints = self.model_constraints.all_constraints`)
  reads the same stale, pre-`finalize_certificate` attribute this task's Phase 3 deviation
  diagnosed -- surfaced here as a follow-up, not fixed, since it is production (non-test) source
  and out of this task's scope.
- 3 pre-existing, unrelated test failures observed during the repository-gate run
  (`theory_lib/exclusion/tests/unit/test_print_encoding.py::TestWitnessFunctionsEncoding`),
  confirmed via `git log` to originate from an unrelated, already-committed task (`4cb1a76b`,
  "task 182 phase 2: failing cp1252 regression coverage for the print sites") whose own module
  docstring states the cases are intentionally RED pending that task's own Phase 3. Not caused by
  this task and out of scope to fix here; flagged so the gate result is read correctly.

  **Orchestrator correction, added after this task closed.** This bullet does not hold up and
  should not be carried forward. That module's 5 tests all PASS, verified directly and again
  inside the full repository gate (`code/tests/ code/src/model_checker` under CI's marker
  expression and `-n 4`: 3098 passed, 1 skipped, 0 failed). The task whose Phase 2 landed those
  cases RED is `completed`, and its Phase 3 routed the call site through
  `model_checker.utils.glyphs`, turning them green; `4cb1a76b` is the only commit that has ever
  touched that file, so no later change reverted it. The misreading came from the module
  docstring, which still asserted the assertions "expected to FAIL against unmodified source"
  long after that stopped being true -- that stale paragraph has now been corrected at source,
  so the next reader is not misled the same way. Nothing in this task's own scope is affected:
  its gate was in fact clean.

## References

- `specs/204_strengthen_a2_triangle_per_candidate/plans/01_strengthen-a2-triangle-per-candidate.md`
- `specs/204_strengthen_a2_triangle_per_candidate/reports/01_strengthen-a2-triangle-per-candidate.md`
- `code/src/model_checker/theory_lib/bimodal/tests/_pinned_eval.py`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_pinned_eval.py`
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py`
- `docs/ADEQUACY.md` section 7.3
