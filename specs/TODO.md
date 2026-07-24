---
next_project_number: 118
---

# TODO

## Task Order

*Updated 2026-07-24. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 117 | -- | packaging |

**Grouped by Topic** (indented = depends on parent):

### Packaging

117 [PLANNED] — Review and stabilize the repo after recent revisions: verify the 

## Tasks

### 117. Review cli pypi parity nix flake release
- **Status**: [PLANNED]
- **Task Type**: python
- **Topic**: packaging
- **Dependencies**: None
- **Research**: [117_review_cli_pypi_parity_nix_flake_release/reports/01_team-research.md]
- **Plan**: [117_review_cli_pypi_parity_nix_flake_release/plans/01_restore-model-checker-release.md]

**Description**: Review and stabilize the repo after recent revisions: verify the CLI works, audit discrepancies with the model-checker package on PyPI, build a Nix flake for testing on NixOS (pip install is impractical there), complete full testing, and prepare a top-quality release to push to PyPI

---

### 116. Draft email modelchecker architecture
- **Status**: [COMPLETED]
- **Task Type**: markdown
- **Topic**: documentation
- **Dependencies**: None

**Description**: Draft a brief email for a Python expert explaining how the ModelChecker supports modular extensions: each model structure is built over shared general infrastructure and supports a range of operators supplied semantic clauses using that model structure's resources. Explain the basic architecture and the pipeline by which logical claims are processed into SMTlib, solved, then passed back to print a model, where key methods are provided by each operator. Culminate with code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py as a worked example. Draw on docs/ and distributed README.md files as appropriate.
