---
next_project_number: 66
---

# Task List

## Tasks

### 65. Fix cvc5 Sort conversion errors in semantic modules
- **Effort**: medium
- **Status**: [NOT STARTED]
- **Language**: z3

**Description**: Migrate remaining z3_shim imports in semantic modules (bimodal/semantic.py, bimodal/witness_registry.py, bimodal/witness_constraints.py, logos/semantic.py) to use solver.expressions abstraction layer. All 138 comparison examples fail with "Cannot convert Sort to cvc5.cvc5_python_base.Sort" because z3 Sort objects are hardcoded instead of using backend-agnostic IntSort/BitVecSort/BoolSort/Function from solver.expressions
