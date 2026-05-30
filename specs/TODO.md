---
next_project_number: 99
---

# Task List

## Tasks

<!-- New tasks are prepended below this line -->

### 98. Investigate Z3 OOM kills during bimodal theorem verification
- **Effort**: medium
- **Status**: [NOT STARTED]
- **Task Type**: python
- **Dependencies**: 97

**Description**: Investigate Z3 OOM kills during bimodal theorem verification. earlyoom kills python3.12 when running bimodal examples with M>=3, especially M=4/M=5 examples (BX5-BX13, BX7) which have 20-60s timeouts. Z3's quantifier instantiation engine has no memory cap and expands ground terms unboundedly when processing the capped Skolem abundance constraint combined with forward_comp (5 quantified variables) and world_uniqueness (ForAll/Exists). Research: (1) Z3 memory limiting options (memory_max_size param, per-solver limits), (2) quantifier instantiation strategies (MBQI vs E-matching, pattern annotations) that reduce memory footprint, (3) whether constraint restructuring (e.g., grounding Skolem abundance for small M) would help, (4) interaction between abundance constraint and frame axioms that amplifies instantiation. System has 30GB RAM.

### 97. Optimize build_frame_constraints for Z3 solver performance
- **Effort**: medium
- **Status**: [IMPLEMENTING]
- **Task Type**: python
- **Research**: [097_optimize_build_frame_constraints/reports/01_team-research.md]
- **Plan**: [097_optimize_build_frame_constraints/plans/01_implementation-plan.md]

**Description**: Optimize build_frame_constraints in code/src/model_checker/theory_lib/bimodal/semantic.py for Z3 solver performance without compromising the architecture or changing which examples are valid/invalid. The function (lines 467-687) builds 13 constraint groups including ForAll/Exists quantifiers, Skolem functions, and frame axioms. Target areas: redundant tautological constraints (classical_truth is always true), potential for Z3 quantifier patterns/triggers on heavy quantifier blocks (lawful, task_restriction, world_uniqueness), possible constraint ordering optimizations, and reducing solver overhead in helper methods (capped_skolem_abundance_constraint, world_interval_constraint, build_forward_comp_constraint with 5 quantified variables). Must preserve identical valid/invalid classification for all existing examples.
