# Research Report: Strengthening the A2-Triangle Leg (i)/(iii) Comparison to Per-Candidate

- **Task**: 204 - strengthen_a2_triangle_per_candidate
- **Started**: 2026-09-27T06:13:48Z
- **Completed**: 2026-09-27T06:45:00Z
- **Effort**: ~30 minutes agent time
- **Dependencies**: 195 (research_encoder_spec_proof_routes, complete -- this task executes that
  report's Stage 1 recommendation)
- **Sources/Inputs**:
  - Local code: `theory_lib/bimodal/tests/integration/test_certificate_a2_triangle.py`,
    `theory_lib/bimodal/semantic/{witness_registry.py, witness_constraints.py, certificate.py,
    core.py}`, `theory_lib/bimodal/semantic/proposition.py`, `models/constraints.py`,
    `models/structure.py`, `theory_lib/bimodal/tests/unit/test_witness_constraints.py`
  - Local docs: `theory_lib/bimodal/docs/ADEQUACY.md` section 7.3, `theory_lib/bimodal/docs/A2_GAP.md`
  - Local artifacts: `specs/195_research_encoder_spec_proof_routes/reports/01_encoder-spec-proof-routes.md`
    (Stage 1 recommendation and its cost claim), `specs/193_extend_a2_triangle_grid_to_nb_nf_2/`
    (measured candidate counts for the current grid)
  - CI config: `.github/workflows/tests.yml` (exact gating invocation), `code/pyproject.toml`
    (marker registration)
- **Artifacts**: `specs/204_strengthen_a2_triangle_per_candidate/reports/01_strengthen-a2-triangle-per-candidate.md`
- **Standards**: report-format.md, subagent-return.md
- **Task Type**: python
- **Domains**: python (test/implementation mechanics), formal/logic (the A2 statement itself)

## Project Context

- **Upstream Dependencies**: task 195's report, whose Executive Summary and Stage 1 recommendation
  name exactly this strengthening as "the immediate work" and gives the cost argument this report
  verifies against the actual code.
- **Downstream Dependents**: none identified; this is the lead recommendation, not a prerequisite
  for anything else in the 195 report's staged path.
- **Alternative Paths**: task 195 evaluated and rejected four other routes (verified generator,
  translation validation against a verified spec, Z3 UNSAT-proof reconstruction, and full
  per-candidate Z3 re-solving); none is revisited here.
- **Potential Extensions**: the same pinned-evaluation mechanism, once built, is reusable for
  195's Stage 2b (`family -> assignment` round-trip against `extract_certificate`).

## Executive Summary

- **The one-bit comparison is real and exactly as described.** `_assert_exhaustive_triangle_agrees`
  asserts `(accepted > 0) == structure.z3_model_status == expected_sat`
  (`test_certificate_a2_triangle.py:232`), collapsing up to 10,485,760 enumerated candidates into a
  single boolean per closure/grid combination.
- **A per-candidate leg (iii) does not require a Z3 solve per candidate, and one already exists in
  spirit: the emitted clause list is directly readable and is a pure Boolean formula.** Every
  constraint the encoder emits (`structure.model_constraints.all_constraints`,
  `models/constraints.py:97-102`) is built from exactly six operators --  `And`, `Or`, `Not`,
  `Implies`, `==` (biconditional between two `BoolRef`s), and `AtMost` -- applied to three families
  of atomic Z3 `Bool` variables: `registry.bit(lasso, slot, formula)`, `registry.guess(formula)`,
  and `generator.sel(t)` (`witness_registry.py:134-154`, `witness_constraints.py:138-146`). A
  candidate (`WitnessFamily` + `target_time`) determines a truth value for every one of those atoms
  directly from its own data, with no solving: this is exactly the inverse of
  `extract_certificate` (`core.py:352-412`), which reads the same atoms *out of* a satisfying model.
- **The evaluator is a one-time AST walk, not a per-candidate one, if built as a compiler rather
  than an interpreter.** Because the constraint list itself never changes across candidates (only
  the *assignment* does), compiling each constraint once (Z3 `BoolRef` tree -> a closure over plain
  Python dict lookups and `and`/`or`/`not`) before the candidate loop keeps the Z3-Python boundary
  crossing (`decl()`/`arg()`/`kind()` calls) out of the hot loop entirely. Re-walking the Z3 AST
  fresh for every (constraint, candidate) pair -- the naive reading of task 195's "~50 line
  evaluator" -- risks costing several times `recheck`'s measured 6.15us/candidate
  (`10,485,760` candidates / `~64.5s` = `6.15us`, `test_certificate_a2_triangle.py:328-336`), which
  could push the widest already-`slow`-marked case past CI's 300s per-test ceiling. This is the one
  concrete risk this report adds to task 195's cost claim, and it is measurable before committing.
- **CI's exact gating invocation admits `slow`-marked tests unconditionally.** `slow` is *not*
  deselected in `code/`'s CI job (`.github/workflows/tests.yml:208`:
  `-m "not packaging and not performance and not unstable and not xdist_serial" -n 4 ... --timeout=300
  --timeout-method=thread`); `code/pyproject.toml:93`'s marker text confirms "these run in the
  default suite". So every existing tier boundary in this test module is a *local-iteration-speed*
  boundary only, and the per-candidate addition must fit the same 300s-per-test, `-n 4`-contended
  ceiling the existing `slow` cases already clear with margin (measured ~64.5s worst case).
- **Recommendation: add the per-candidate assertion beside the existing aggregate one, reusing the
  same tiers, but gate the widest grid point's inclusion on an explicit timed measurement taken
  under the real CI invocation shape rather than a doubled-cost estimate.** Tier 2's clean-skip
  discipline is untouched -- this change is entirely inside Tier 1's leg (i)/(iii) comparison.

## Context & Scope

A2 (`ADEQUACY.md` section 7.3) holds iff the Z3 constraint set is *exactly* the conjunction of
(C1)-(C4), with no extra constraint. The current deciding test enumerates every candidate and
checks leg (i) (`certificate.recheck`) per candidate, but only checks leg (iii) (the Z3 encoding)
in aggregate -- one `structure.z3_model_status` for the whole closure
(`test_certificate_a2_triangle.py:157-236`, `_run_exhaustive_triangle`/`_assert_exhaustive_triangle_agrees`).
A candidate the encoder wrongly rejects and `recheck` accepts (or vice versa) is invisible whenever
the two aggregate bits still happen to agree. Task 195's report identified this as the highest-value
local finding and recommended, as its Stage 1, a solver-free per-candidate evaluator over the
already-built constraint list. This task's scope is to determine feasibility and design of that
evaluator against the actual code (not just the prior report's estimate), and to give tiering
guidance measured against CI's real invocation. Diagnosing any genuine divergence the strengthened
test finds is explicitly out of scope (per the dispatch); it is to be reported as a finding.

## Findings

### What the current comparison actually asserts, and where

1. `_assert_exhaustive_triangle_agrees` (`test_certificate_a2_triangle.py:195-244`) builds one
   `BimodalStructure` per parametrized case, enumerates every candidate via `_run_exhaustive_triangle`
   (leg i only, `:157-171`), and asserts three things: the candidate count matches a closed form
   (`:226-228`), the accepted count matches an expected literal (`:229-231`), and
   `(accepted > 0) == structure.z3_model_status == expected_sat` (`:232-238`, dispatch cites `:238`
   for the same assertion -- the block spans both line numbers). Only the third assertion is the
   leg (i)/(iii) comparison, and it is aggregate.
2. `_candidates` (`:101-155`) already enumerates the full candidate space exhaustively and cheaply;
   the per-candidate work this task adds slots into the same loop `_run_exhaustive_triangle` already
   runs, no new enumeration is needed.

### The emitted clause list is a plain Boolean formula over three atom families -- confirmed by reading every generator

3. `WitnessRegistry` (`witness_registry.py`) allocates exactly three kinds of Z3 atoms, all
   memoized dicts keyed by hashable Python data, not by position:
   - `bit(lasso, t, formula)` (`:134-144`) -- one Boolean per `(lasso, slot, formula)`, where `slot
     = wrap(t)` collapses every position sharing a period into one variable (`:125-132`).
   - `guess(formula)` (`:146-154`) -- one Boolean per boxed subformula, global (not per-lasso).
   - `WitnessConstraintGenerator.sel(t)` (`witness_constraints.py:138-146`) -- one Boolean per
     position in the target window, held in the generator (`self._sel`), not the registry.
4. `WitnessConstraintGenerator`'s four constraint families (`witness_constraints.py`) use only
   `z3.And`, `z3.Or`, `z3.Not`, `z3.Implies`, Python `==` between two `BoolRef`s (a Z3
   biconditional, e.g. `:113,117,124,131`), and `z3.AtMost` (`:165`, the target selector's
   exactly-one). No `Ite`, `Distinct`, arithmetic, or quantifiers appear anywhere in this module or
   in `core.py`'s `_premise_behavior`/`_conclusion_behavior` (`core.py:234-260`, which contribute
   only `And`/`Implies`/`Not` over the same `bit`/`sel` atoms). This closes the operator set a
   solver-free evaluator must handle to exactly the six named in task 195's report.
5. The complete emitted list, reachable directly from the test's already-built `structure` object,
   is `structure.model_constraints.all_constraints` (`models/constraints.py:97-102`): frame
   constraints (`= semantics.frame_constraints`, populated by `finalize_certificate`,
   `core.py:291-346`) plus `model_constraints` (per-sentence-letter; **empty** for bimodal --
   `proposition.py:110-113` returns `[]` since atoms are deliberately unconstrained) plus
   `premise_constraints`/`conclusion_constraints` (one `And`-of-`Implies` term per premise/
   conclusion, from `semantics.premise_behavior`/`conclusion_behavior`). This is the exact target
   set for a per-candidate evaluator; nothing outside it needs to be located.

### A candidate already determines every atom's value -- this is `extract_certificate`'s exact inverse

6. `extract_certificate` (`core.py:352-412`) is the existing reverse direction: given a satisfying
   Z3 model, it reads `bit`/`guess`/`sel` values via `z3_model.eval(..., model_completion=True)` to
   build a `WitnessFamily` + `target_time` (`:369-410`). The forward direction this task needs is
   mechanical and symmetric:
   - For each active lasso index and each `t` in `registry.target_window()` (the same window
     `extract_certificate` iterates, `:371`), the candidate's `LabelledLasso` already stores one
     label (a `frozenset[Formula]`) per slot in `back + mid + fwd` order (matching
     `witness_registry.py`'s slot layout described in its module docstring, `:24-41`). So
     `assignment[bit(lasso, t, f)] = f in label` for every closure member `f`, read directly off
     the candidate -- no enumeration beyond what `_candidates` already does per candidate.
   - `assignment[guess(f.child)] = family.bx[f.child]` for every boxed closure member -- `bx` is
     already exactly this dict (`certificate.py`'s `WitnessFamily`, referenced in the test's
     `Candidate = Tuple[WitnessFamily, int]` type alias, `test_certificate_a2_triangle.py:63`).
   - `assignment[sel(t)] = (t == target_time)` for every `t` in the window -- the one-hot selector
     is fully determined by the candidate's own `target_time` component.
   - Because `bit`'s memoization is per-*slot*, not per raw position, this assignment automatically
     and correctly covers every wide-window reference `local_coherence_constraints` and
     `fulfilment_constraints` make (`witness_constraints.py:99,195`, which range over
     `_coherence_window`, a window strictly wider than `target_window()`) -- those calls return the
     *same* memoized variable as the in-window representative for their shared slot, so the
     assignment built from the window alone is already total over every atom the constraint list
     references.

### Cost: a per-candidate Z3 solve is infeasible; a per-candidate *evaluation* is not, but must be built as a compiler, not an interpreter

7. Task 195's report already rules out a Z3 `check()` per candidate ("10M solver calls is
   infeasible") and estimates pinned evaluation at "microsecond-scale, comparable to `recheck`'s
   measured 6.4us/candidate". This report's own cross-check from the test file's docstrings agrees:
   `10,485,760` candidates at `~64.5s` (`test_certificate_a2_triangle.py:325-329`) is `6.15us`/
   candidate for `recheck` alone, consistent with the 195 report's figure.
   - `recheck` (`certificate.py:361-...`) is pure Python: frozenset membership, dict lookups, no
     Z3 object access at all once `family`/`target_time` are in hand.
   - A structural evaluator that re-walks each constraint's Z3 `BoolRef` tree (`decl()`, `kind()`,
     `arg(i)`, `num_args()`) *fresh for every candidate* pays a Python->Z3-C-API call at every AST
     node, for every one of the (roughly) `O(lassos x coherence_window_size x |closure|)` top-level
     constraints, for every one of up to 10.5 million candidates. That per-node cost is typically
     several times a pure-Python dict/frozenset operation; multiplied across millions of candidates
     it is the one place this task's cost story could diverge sharply from the "comparable to
     `recheck`" estimate, and it is exactly the risk the dispatch's "measure before committing"
     instruction is guarding against.
   - **The fix is architectural, not a tuning knob**: compile each constraint **once**, after
     `finalize_certificate()` and before the candidate loop, into a plain Python closure (or a
     small tree of Python callables) over the finite, already-known set of atom names -- turning
     `And`/`Or`/`Not`/`Implies`/`==`/`AtMost` into `all(...)`/`any(...)`/`not`/`(not a) or b`/
     `a == b`/`sum(...) <= k` once per constraint. The candidate loop then only does dict lookups
     and Python boolean operations, matching `recheck`'s own cost profile rather than paying the
     Z3-Python boundary per candidate. This turns an O(candidates x constraints x tree-size) count
     of Z3 API calls into an O(constraints x tree-size) one, with the O(candidates x constraints)
     remainder being cheap native Python -- the same shape `recheck` already has.
   - Building the evaluator this way is a small addition of design complexity over task 195's "~50
     line" estimate (a one-time compile pass plus the interpreter), but it is what makes "comparable
     to `recheck`" a design property rather than a hope to be measured after the fact.

### CI's actual gating shape, and what it means for tiering

8. `.github/workflows/tests.yml:208`: `pytest tests/ src/model_checker -m "not packaging and not
   performance and not unstable and not xdist_serial" -n 4 -q --timeout=300 --timeout-method=thread`.
   `slow` is **not** in that exclusion list, and `code/pyproject.toml:93`'s marker text says so
   explicitly ("these run in the default suite"). Every `slow`-marked case in this module today
   (`TestExhaustiveTriangleWithBox`, both cases, `:332,343`) already runs on every gating CI run,
   inside a 300s-per-test budget, under `-n 4` worker contention, with only local `-m "not slow"`
   iteration exempted -- confirmed by the module's own measured figures (~11s and ~64.5s,
   `:310-329`).
9. The existing tiering already reflects a measure-first discipline (the module docstring records
   host-measured wall clock for every case, `:1-38`), so the per-candidate addition should follow
   the identical discipline rather than introduce a new policy: add the per-candidate assertion
   inside the same test functions (same parametrize rows, same `slow` markers), re-measure each
   case's wall clock under this exact CI invocation shape once the evaluator exists, and only then
   decide whether any case needs to move tiers (e.g., from unconditional to `slow`) or needs a
   narrower per-case scope. The two box-free cases (`<0.1s`/`~1.06s` combined today) have enormous
   headroom even under a pessimistic multiplier; the size-2 `nb=2,fwd=2` boxed case (`~64.5s`
   today, already `slow`) is the one case close enough to the 300s ceiling that it must be measured
   before being trusted to stay under budget with the naive (non-compiled) evaluator design.
10. Tier 2 (`TestBoundedLeanCrossCheck`, `:359-522`) is untouched by this change: it exercises leg
    (ii) via `lake exe check_certificate` on a bounded sample and is unrelated to the leg (i)/(iii)
    comparison this task strengthens. Its `skipif(SKIP_REASON is not None, ...)` clean-skip
    discipline (`:459`) needs no changes.

### What a genuine divergence would mean, and that diagnosis is out of scope

11. `ADEQUACY.md` section 7.3 and the test module's own docstring already state the two-sided
    interpretation a per-candidate divergence would carry: a candidate `recheck` accepts that the
    pinned-evaluated constraint set rejects is an **encoding incompleteness** (the encoder imposes
    a constraint (C1)-(C4) does not require); the reverse is an **encoding unsoundness** (caught at
    runtime today by `models/model.py`'s section-6.2 fail-fast guard, per the test module's own
    docstring `:20-23`). Per the dispatch, any such divergence found while implementing this
    strengthening should be reported as a finding, with diagnosis of the encoder scoped separately.

## Decisions

- **Recommend implementing the per-candidate leg (i)/(iii) comparison as Stage 1 of task 195's
  report describes**, using `structure.model_constraints.all_constraints` as the target clause set
  and the candidate-to-assignment mapping in Finding 6 (the direct inverse of `extract_certificate`).
- **Recommend building the evaluator as a one-time compile pass (Z3 AST -> Python closures) plus a
  cheap per-candidate interpretation step, not a fresh AST walk per candidate.** This is the one
  design choice this report adds beyond task 195's report, and it is what makes the "comparable to
  `recheck`" cost claim achievable rather than merely hoped for.
- **Recommend reusing the existing tier structure (unconditional for the two box-free cases, `slow`
  for the boxed cases) rather than inventing a new one**, contingent on re-measuring each case's
  wall clock, under the exact CI invocation (`-n 4 --timeout=300 --timeout-method=thread`), once the
  evaluator is implemented -- especially the `~64.5s` size-2 `nb=2,fwd=2` boxed case, which has the
  least headroom to the 300s ceiling.
- **Recommend leaving Tier 2 untouched.**

## Recommendations

1. **Implement the assignment builder** (Finding 6): a function `_assignment_for(structure, family,
   target_time) -> Dict[z3.BoolRef, bool]` (or an equivalent name-keyed dict, since Z3 `BoolRef`s
   are not natively hashable by identity across separate `Bool(...)` calls -- use the variable's
   Z3 declaration name, exactly the `lab_{lasso}_{slot}_{repr}` / `bx_{repr}` / `sel_{t}` spelling
   `witness_registry.py`/`witness_constraints.py` already construct, as the dict key), built once
   per candidate from the candidate's own `LabelledLasso`/`bx`/`target_time` data, with no Z3 calls.
2. **Implement the compile-once evaluator** (Finding 7): walk `structure.model_constraints.
   all_constraints` exactly once per built `structure` (not per candidate), producing one Python
   callable per top-level constraint (or one callable over the whole conjunction) that takes the
   name-keyed assignment dict and returns a bool, dispatching on the six operators named in
   Finding 4. Reuse this compiled form across every candidate in that structure's enumeration.
3. **Add the per-candidate assertion beside the existing aggregate one** inside
   `_run_exhaustive_triangle` (or a sibling helper called from the same loop in
   `_assert_exhaustive_triangle_agrees`), asserting per candidate that "every compiled constraint
   evaluates true under the candidate's assignment" iff `recheck`'s verdict is `"countermodel"`,
   and reporting the first divergent candidate (family, target_time, and which side disagreed) on
   failure, per the dispatch's "report the first divergence with enough of the candidate to
   diagnose it".
4. **Measure wall clock for every existing parametrized case under the real CI invocation shape**
   (`-n 4 -q --timeout=300 --timeout-method=thread`, matching `.github/workflows/tests.yml:208`,
   not an idle-host bare run) before deciding final tier placement, per the dispatch's own
   instruction. Keep the two box-free cases unconditional if headroom holds; keep the boxed cases
   `slow`; if the size-2 `nb=2,fwd=2` boxed case's measured wall clock materially threatens the
   300s ceiling, consider narrowing that one case's scope (e.g., sampling within it) rather than
   weakening the assertion itself -- the dispatch is explicit that the assertion must not be
   weakened.
5. **Do not attempt to diagnose any divergence found**; report it as a finding with the localizing
   detail Finding 11 names (incompleteness vs. unsoundness), per the dispatch and per `ADEQUACY.md`
   section 7.3's own framing.

## Risks & Mitigations

- **Risk**: the compile-once evaluator still costs more than `recheck` per candidate even after
  removing the AST-walk-per-candidate cost, because dict lookups keyed by long string names are
  slower than `recheck`'s frozenset operations. **Mitigation**: measure (Recommendation 4) before
  committing to unconditional execution for any case close to budget; if needed, key the assignment
  dict by a compact integer index assigned once per unique atom rather than by its full string name.
- **Risk**: a genuine divergence is found, and diagnosing it balloons scope beyond this task.
  **Mitigation**: explicitly out of scope per the dispatch; report and stop, as Finding 11/
  Recommendation 5 state.
- **Risk**: the `AtMost` operator's evaluation is mis-implemented (e.g., off-by-one on the bound
  argument's position in `z3.AtMost(*sels, 1)`). **Mitigation**: `test_witness_constraints.py`'s
  existing `TestSelectorConservativity`/exactly-one tests (`:111-138`) already exercise `AtMost`
  with small solver-backed checks; the new evaluator's `AtMost` case can be unit-tested against
  those same small cases before being trusted at the full enumeration scale.
- **Risk**: `bit`'s memoization-by-slot (Finding 6's last bullet) is assumed but not re-verified at
  implementation time, causing an incomplete assignment (a referenced atom with no entry) to be
  silently treated as unconstrained rather than erroring. **Mitigation**: have the evaluator raise
  loudly on any atom name it encounters that the assignment builder did not populate, rather than
  defaulting it -- this turns a coverage gap into a hard implementation-time failure instead of a
  silently-wrong evaluation.

## Context Extension Recommendations

- **Topic**: The compile-vs-interpret cost distinction for solver-free Z3 clause evaluation.
  **Gap**: no context file records that repeatedly walking a Z3 expression tree via its Python API
  is markedly more expensive per node than native Python operations, or that this cost is avoided
  by compiling once and interpreting many times. This distinction will recur for any future
  solver-free translation-validation work (task 195's Stage 2b round-trip, in particular).
  **Recommendation**: a short note under `context/project/python/` (or wherever this repository's
  Z3-performance notes live) naming the pattern, cross-referenced from `A2_GAP.md` or `ADEQUACY.md`
  section 7.3.

## Appendix

### Key file:line references

- Aggregate comparison: `test_certificate_a2_triangle.py:232-238` (the assertion), `:157-171`
  (`_run_exhaustive_triangle`), `:195-244` (`_assert_exhaustive_triangle_agrees`), `:101-155`
  (`_candidates`).
- Tiers: `:257-308` (`TestExhaustiveTriangleBoxFree`, unconditional), `:310-357`
  (`TestExhaustiveTriangleWithBox`, `slow`-marked at `:332,343`), `:359-522`
  (`TestBoundedLeanCrossCheck`, Tier 2, untouched).
- Z3 atom layer: `witness_registry.py:125-154` (`wrap`, `bit`, `guess`), `witness_constraints.py:
  138-146` (`sel`).
- Constraint generators (operator inventory): `witness_constraints.py:93-252` (all four families).
- Emitted clause list accessor: `models/constraints.py:80-102` (`all_constraints`),
  `models/structure.py:162-195` (`_setup_solver`'s `constraint_groups`, corroborating the same four
  groups), `proposition.py:110-113` (confirms the per-sentence-letter group is empty for bimodal).
- Reverse mapping to mirror: `core.py:352-412` (`extract_certificate`).
- CI invocation: `.github/workflows/tests.yml:208` (parallel pass), `:212` (serial `xdist_serial`
  pass, not relevant here), `code/pyproject.toml:88-96` (marker registration, including `slow`'s
  "run in the default suite" text).
- Prior recommendation: `specs/195_research_encoder_spec_proof_routes/reports/01_encoder-spec-proof-routes.md`,
  Executive Summary bullet 2, Findings 4/11, Recommendations Stage 1.
