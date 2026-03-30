---
next_project_number: 58
---

# Task List

## Tasks

<!-- New tasks are prepended below this line -->

### 57. Design v2 scaling solver comparison benchmark
- **Effort**: TBD
- **Status**: [PLANNED]
- **Language**: python
- **Research**:
  - [01_scaling-benchmark-design.md](057_v2_scaling_solver_comparison/reports/01_scaling-benchmark-design.md)
  - [02_max-model-discovery.md](057_v2_scaling_solver_comparison/reports/02_max-model-discovery.md)
  - [03_existing-infrastructure.md](057_v2_scaling_solver_comparison/reports/03_existing-infrastructure.md)
- **Plan**:
  - [02_implementation-plan.md](057_v2_scaling_solver_comparison/plans/02_implementation-plan.md)
  - [03_revised-implementation-plan.md](057_v2_scaling_solver_comparison/plans/03_revised-implementation-plan.md) (current)

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
