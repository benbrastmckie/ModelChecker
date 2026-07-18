---
next_project_number: 117
---

# TODO

## Task Order

*Updated 2026-07-18. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 116 | -- | documentation |

**Grouped by Topic** (indented = depends on parent):

### Documentation

116 [NOT STARTED] — Draft a brief email for a Python expert explaining how the ModelC

## Tasks

### 116. Draft email modelchecker architecture
- **Status**: [NOT STARTED]
- **Task Type**: markdown
- **Topic**: documentation
- **Dependencies**: None

**Description**: Draft a brief email for a Python expert explaining how the ModelChecker supports modular extensions: each model structure is built over shared general infrastructure and supports a range of operators supplied semantic clauses using that model structure's resources. Explain the basic architecture and the pipeline by which logical claims are processed into SMTlib, solved, then passed back to print a model, where key methods are provided by each operator. Culminate with code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py as a worked example. Draw on docs/ and distributed README.md files as appropriate.
