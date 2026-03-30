---
next_project_number: 64
---

# Task List

## Tasks

<!-- New tasks are prepended below this line -->

### 63. Migrate builder and iterate modules to solver abstraction
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Language**: z3
- **Dependencies**: 59

**Description**: Replace all direct `import z3` usage in the builder and iterate modules with the solver abstraction layer. Files: `builder/example.py` (2 refs), `builder/runner.py` (3 refs), `builder/z3_utils.py` (15 refs), `iterate/base.py` (4 refs), `iterate/build_example.py` (2 refs), `iterate/constraints.py` (25 refs), `iterate/graph.py` (1 ref), `iterate/models.py` (21 refs). Total ~73 z3 references. Also migrate `models/constraints.py` (1 ref) and `models/semantic.py` (3 refs) if not already covered. Verify: all existing iterate and builder tests pass with z3 backend; `comparison.py` still gives 138/138 z3 pass.

---

### 62. Migrate bimodal theory to solver abstraction
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Language**: z3
- **Dependencies**: 59

**Description**: Replace all direct `import z3` usage in the bimodal theory with the solver abstraction layer. Files: `theory_lib/bimodal/semantic.py` (162 refs - largest single file), `theory_lib/bimodal/operators.py` (21 refs), `theory_lib/bimodal/iterate.py` (4 refs), `theory_lib/bimodal/semantic/witness_constraints.py` (12 refs), `theory_lib/bimodal/semantic/witness_registry.py` (12 refs). Total ~211 z3 references. Uses z3.And, z3.Or, z3.Not, z3.BitVec, z3.BoolVal, z3.Function, z3.Solver, z3.Z3Exception heavily. Verify: bimodal tests pass with z3 backend.

---

### 61. Migrate logos operator subtheories to solver abstraction
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Language**: z3
- **Dependencies**: 59

**Description**: Replace all direct `import z3` usage in logos subtheory operator files with the solver abstraction layer. Files: `theory_lib/logos/subtheories/constitutive/operators.py` (81 refs), `theory_lib/logos/subtheories/extensional/operators.py` (51 refs), `theory_lib/logos/subtheories/first_order/operators.py` (24 refs), `theory_lib/logos/subtheories/counterfactual/operators.py` (13 refs), `theory_lib/logos/subtheories/modal/operators.py` (6 refs). Also: `theory_lib/logos/iterate.py` (14 refs), `theory_lib/logos/protocols.py` (7 refs). Total ~196 z3 references. These files use z3.And, z3.Or, z3.Not, z3.Implies, z3.BitVec, z3.BoolVal, z3.Function, z3.Select, z3.ForAll, z3.Exists heavily. Verify: `comparison.py` gives 138/138 z3 pass after migration.

---

### 60. Migrate logos/semantic.py to solver abstraction
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Language**: z3
- **Dependencies**: 59

**Description**: Replace all direct `import z3` usage in `theory_lib/logos/semantic.py` with the solver abstraction layer. This is the second-largest file with 97 z3 references including `z3.And`, `z3.Or`, `z3.Not`, `z3.BitVec`, `z3.BitVecVal`, `z3.BitVecSort`, `z3.BoolVal`, `z3.Bool`, `z3.Int`, `z3.IntSort`, `z3.Function`, `z3.Select`, `z3.Solver`, `z3.sat`, `z3.unsat`, `z3.simplify`, `z3.is_true`, `z3.is_false`, `z3.Z3Exception`, `z3.ModelRef`, `z3.FuncDeclRef`, `z3.ExprRef`, `z3.BoolRef`, `z3.BitVecRef`. This is the core file where solver expressions are created for the entire logos theory - it's the critical path for cvc5 compatibility. Also migrate `syntactic/assignments.py` (4 refs) and `syntactic/sentence.py` remaining refs. Verify: `comparison.py` gives 138/138 z3 pass; single cvc5 example progresses further than "derived_type invalid".

---

### 59. Extend solver expressions.py and compat.py for full API coverage
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Completed**: 2026-03-30
- **Language**: z3

**Description**: Extend `solver/expressions.py` and `solver/compat.py` with all z3 API functions needed by the core pipeline. Currently missing from expressions.py: `Bool` (66 uses), `Int` (56), `IntSort` (44), `BoolVal` (77), `Function` (25), `Select` (15), `Solver` (104) -- wait, Solver is via create_solver. Missing type predicates: `is_true` (1), `is_false` (1), `is_bool` (8), `is_int` (3), `is_int_value` (8), `is_real` (8), `is_bv` (1), `is_quantifier` (6). Missing type refs for runtime use: `BoolRef` (95), `BitVecRef` (21), `ExprRef` (16), `FuncDeclRef` (21), `ModelRef` (37), `Z3Exception` (37), `CheckSatResult` (3). Also need: `Sum` (1), `Var` (1), `set_param` (1), `reset_params` (1), `ArraySort` (1). Add backend-aware versions of all these to expressions.py or a new `solver/types_runtime.py`. For type refs, provide runtime-importable aliases that resolve to the correct backend's types. For `Z3Exception`, provide a `SolverException` wrapper. Verify: `from model_checker.solver.expressions import X` works for every function used in the codebase.

---

### 58. Wire solver registry into core solving loop
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Language**: z3
- **Research**: [01_solver-registry-wiring.md](058_wire_solver_registry_into_core/reports/01_solver-registry-wiring.md)
- **Plan**: [01_solver-registry-wiring-plan.md](058_wire_solver_registry_into_core/plans/01_solver-registry-wiring-plan.md)
- **Completed**: 2026-03-30
- **Summary**: [01_solver-registry-wiring-summary.md](058_wire_solver_registry_into_core/summaries/01_solver-registry-wiring-summary.md)

**Description**: structure.py hardcodes `import z3` and `z3.Solver()` throughout, bypassing the solver switching infrastructure (registry, adapters, z3_shim). This means `switch_solver('cvc5')` has no effect on actual SAT checking. Need to systematically replace all direct `import z3` / `from z3 import ...` in the solving pipeline with `from model_checker.z3_shim import ...` (or the adapter layer), so that the active backend from the registry is actually used. Key files: structure.py (lines 16, 156, 232-235, 248, 277, 288, 885), runner.py (lines 15, 312), and any other files in the solving pipeline that import z3 directly. Must preserve existing behavior when z3 is the default backend while enabling actual cvc5 usage when switched.

---

### 57. Design v2 scaling solver comparison benchmark
- **Effort**: TBD
- **Status**: [COMPLETED]
- **Language**: python
- **Research**:
  - [01_scaling-benchmark-design.md](057_v2_scaling_solver_comparison/reports/01_scaling-benchmark-design.md)
  - [02_max-model-discovery.md](057_v2_scaling_solver_comparison/reports/02_max-model-discovery.md)
  - [03_existing-infrastructure.md](057_v2_scaling_solver_comparison/reports/03_existing-infrastructure.md)
- **Plan**:
  - [02_implementation-plan.md](057_v2_scaling_solver_comparison/plans/02_implementation-plan.md)
  - [03_revised-implementation-plan.md](057_v2_scaling_solver_comparison/plans/03_revised-implementation-plan.md) (current)
- **Completed**: 2026-03-30
- **Summary**: [03_scaling-benchmark-summary.md](057_v2_scaling_solver_comparison/summaries/03_scaling-benchmark-summary.md)

**Description**: Research and design a v2 solver comparison benchmark that progressively scales model sizes (number of worlds, propositions, accessibility relations) to identify divergence points between z3 and cvc5. The current v1 (code/comparison.py) runs 138 examples with both solvers getting identical results. V2 should: (1) parameterize model size dimensions (world count, proposition count, relation density), (2) progressively increase scale until solvers diverge in result or timeout, (3) identify the specific model size thresholds where divergence occurs, (4) report per-subtheory scaling curves and divergence points.

---

### 50. Create standalone solver comparison script using dev_cli.py
- **Effort**: TBD
- **Status**: [NOT STARTED]
- **Language**: python

**Description**: Create standalone solver comparison script that runs each logos example through dev_cli.py twice (once with z3, once with cvc5), displaying concrete model/countermodel output with timing data for side-by-side comparison.

---

### 36. Fill placeholders and fix metadata
- **Effort**: TBD
- **Status**: [NOT STARTED]
- **Language**: latex
- **Dependencies**: None

**Description**: Fix all placeholder and incomplete content in `latex/paper.tex`:

1. **Author information** (line 216): Replace `\author*[1]{\fnm{Author} \sur{Name}}` and `\email{author@example.com}` with real author name and email.

2. **Affiliation** (line 218): Replace `\orgdiv{Department}, \orgname{University}, \orgaddress{\city{City}, \state{State}, \country{Country}}` with real institutional affiliation.

3. **Code availability** (line 1332): Replace `[repository URL]` and `[license]` with the actual GitHub/PyPI URL and license name (MIT).

4. **Author contributions** (line 1336): Replace `[Author contributions to be added]` with appropriate contribution statement.

5. **Verify URLs**: Confirm that `https://github.com/benbrastmckie/ModelChecker` (if referenced) and `https://pypi.org/project/model-checker/` are live and accessible. Consider adding a Zenodo DOI for the specific version used in benchmarks.

6. **MSC Classification** (line 245): Uncomment and verify the MSC codes (`03B45, 68T15, 68Q60`) are appropriate for the paper's content, or update them.

---

### 35. Fix first-order semantics and predicate extension display
- **Effort**: TBD
- **Status**: [NOT STARTED]
- **Language**: python
- **Dependencies**: None

**Description**: Upon running the first-order theory in the model-checker, the output shows the model-checker is running but does not find or produce a reasonable looking model. Each n-place predicate should get mapped to a set of verifiers and falsifiers (functions from n states to a state) where the positive extension of a predicate in a world is the set of state n-tuples which get mapped to a state that is part of that world by SOME verifier for the predicate. Review the semantics in `/home/benjamin/Projects/Logos/Theory/typst/manual/chapters/02-constitutive.typ` and `/home/benjamin/Projects/Logos/Theory/typst/manual/chapters/03-dynamics.typ` to verify the first-order semantics in the model-checker is correct. Then evaluate and redesign the elements needed to extract predicate extensions at each world and display these when printing a model.

---
