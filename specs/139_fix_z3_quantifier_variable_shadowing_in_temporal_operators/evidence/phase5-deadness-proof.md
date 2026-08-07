# Phase 5: `false_at` deadness proof -- results and flipped decision

## Instrument

`evidence/false_at_deadness_probe.py`, run via:
```
PYTHONPATH=code/src:oracle python3 specs/139_.../evidence/false_at_deadness_probe.py \
  > specs/139_.../evidence/false_at_deadness_probe.log 2>&1
```
Full output: `evidence/false_at_deadness_probe.log` (399 lines).

Monkeypatches the five quantified operators' `false_at` methods (`NecessityOperator`,
`FutureOperator`, `PastOperator`, `UntilOperator`, `SinceOperator`) with counting wrappers, then
runs, in-process:

1. The full bimodal package suite (`code/src/model_checker/theory_lib/bimodal/tests/`, unit +
   integration): **298 passed in 108.62s**.
2. The oracle gating suite's fast tests (`test_soundness_regression.py` +
   `test_encoding_nondegeneracy.py`): **34 passed in 494.12s**.

Both suites green under instrumentation -- the monkeypatch itself introduced no regressions.

## Result: counters

| Operator | `false_at` invocation count |
|---|---|
| `NecessityOperator` | 0 |
| `FutureOperator` | 1 |
| `PastOperator` | 1 |
| `UntilOperator` | 3 |
| `SinceOperator` | 2 |

**Total: 7 invocations across 4 of the 5 operators.** The deadness proof therefore **FAILS**: not
all counters are zero.

## Gate outcome: deletion is OFF

Per the plan's explicit gate ("if any counter is non-zero, the deletion is off. Fall back to
keep-and-fix for the invoked methods... record which caller reached them and why the research's
grep missed it, and skip the remaining tasks in this phase"), **the Phase 5 deletion is
cancelled**. The five `false_at` methods are kept, unmodified beyond their existing Phase 2
`_fresh_bound_int()` fix (already applied at all 5 sites -- reconfirmed by direct grep of
`operators.py`, no further code change needed for "keep-and-fix").

## Callers identified

Every recorded first-call-site traceback bottoms out in a **unit test that calls
`operator.false_at(...)` directly**, not in the semantic evaluation pipeline
(`BimodalSemantics.false_at` / `find_countermodel()`):

| Operator | Caller (test file:line, test name) |
|---|---|
| `FutureOperator` | `bimodal/tests/unit/test_foralltime.py:186`, `test_future_operator_false_structure_uses_quantifier` |
| `PastOperator` | `bimodal/tests/unit/test_foralltime.py:240`, `test_past_operator_false_structure_uses_quantifier` |
| `UntilOperator` | `bimodal/tests/unit/test_until_since.py:164`, `test_until_false_at_returns_z3_expression` (2 more calls from sibling structure/naming tests in the same file) |
| `SinceOperator` | `bimodal/tests/unit/test_until_since.py:251`, `test_since_false_at_returns_z3_expression` (1 more call from a sibling naming test) |
| `NecessityOperator` | none (0 calls) -- no unit test invokes `NecessityOperator.false_at` directly |

These tests instantiate the operator directly, monkeypatch `semantics.false_at` to a mock
(`z3.Bool('mock_not_p')`), and call `operator.false_at(...)` to assert its *structural* shape
(`isinstance(result, z3.ExprRef)`, `z3.is_quantifier(result)`, or variable-naming checks). They
are unit-level API-contract tests of the operator's own method -- not exercises of the live
`find_countermodel()` evaluation pipeline. `BimodalSemantics.false_at` (`semantic/core.py:1624`,
unconditionally `Not(true_at(...))`) is never invoked by these tests, and no call originates from
`find_countermodel()` in any recorded traceback. The research report's core claim -- that no
*production evaluation path* reaches `operator.false_at` -- is not contradicted by this finding.

## Why the research's grep missed these callers

The research report (§2) states: "I grepped the whole `bimodal` package for direct calls to
`.false_at(` and `operator.false_at` and found none outside `semantics.false_at` itself and the
dead methods calling each other." Re-running an equivalent grep now
(`grep -rn "\.false_at(" code/src/model_checker/theory_lib/bimodal/`) *does* surface these seven
call sites in `test_foralltime.py` and `test_until_since.py`. The most plausible explanation,
verifiable from the report's own framing, is scope: the research was answering "is
`operator.false_at` reachable from `find_countermodel()`" -- a runtime-reachability question about
the semantic evaluation pipeline -- and its grep search and manual trace were conducted against
that production call graph (semantics/operators source files), not against the unit test suite
that separately exercises each operator's public methods as an API contract independent of the
pipeline. A grep literally scoped to "the whole package" including `tests/` should have found
these lines; the discrepancy is recorded here as unresolved rather than asserted with false
confidence, since the exact grep invocation used in the research phase was not preserved
verbatim. What is certain and independently reproduced is: the production reachability claim
holds (no `find_countermodel()`-originated call reaches `operator.false_at` in this run's
traceback samples); the whole-package-including-tests reachability claim does not.

## Decision: keep-and-fix (flipped from the plan's default DELETE)

**The Phase 5 plan's default decision to DELETE the five `false_at` implementations is
overridden by this run's evidence.** They are kept as-is. This is not a silent judgement call --
it is the plan's own pre-declared contingency, exercised here because its gate condition (any
non-zero counter) fired.

Consequences for the remaining Phase 5 tasks, all explicitly skipped per the plan's "skip the
remaining tasks in this phase" instruction once the gate fires:

- The deletion of the five `false_at` methods: **skipped** (methods retained).
- Expanding `BimodalSemantics.false_at`'s docstring to state operator-level `false_at` is *never
  defined*: **skipped** -- that docstring claim would now be false, since these five methods do
  still exist and are exercised (by tests, not the pipeline).
- Removing the Phase 2 `_fresh_bound_int()` edits at the five sites "as a consequence of the
  deletion": **skipped** -- there is no deletion, so those edits remain in place and remain
  correct (Phase 2's fix already covers these sites; no further code change was needed here).

No file outside `specs/139_.../evidence/` was modified in this phase.
