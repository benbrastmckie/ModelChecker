---
next_project_number: 33
---

# Task List

## Tasks

<!-- New tasks are prepended below this line -->

### 32. Consolidate first-order subtheory to standard structure
- **Effort**: TBD
- **Status**: [NOT STARTED]
- **Language**: python
- **Dependencies**: None

**Description**: Refactor first-order subtheory (`code/src/model_checker/theory_lib/logos/subtheories/first-order/`) to contain only the standard files (`__init__.py`, `examples.py`, `operators.py`, `README.md`) matching other subtheories. Review contents of `constraints.py` and `denotation.py` to identify correct integration points. Ensure the logos theory structure remains systematic and extensible for future subtheories.

---

### 28. Archive unused theory libraries
- **Effort**: 1-2 hours
- **Status**: [COMPLETED]
- **Plan**: [implementation-001.md](028_archive_unused_theories/plans/implementation-001.md)
- **Summary**: [implementation-summary-20260303.md](028_archive_unused_theories/summaries/implementation-summary-20260303.md)
- **Language**: python
- **Dependencies**: None

**Description**: Archive `theory_lib/exclusion/` and `theory_lib/imposition/` directories to `code/boneyard/`. Update any references to these theories in the codebase. Ensure the boneyard directory structure preserves the original organization. Run tests to confirm no regression from removing these theories from active code paths.

---

### 29. Clean up specs directories
- **Effort**: 1 hour
- **Status**: [COMPLETED]
- **Research**: [research-001.md](029_cleanup_specs_directories/reports/research-001.md)
- **Plan**: [implementation-002.md](029_cleanup_specs_directories/plans/implementation-002.md)
- **Summary**: [implementation-summary-20260303.md](029_cleanup_specs_directories/summaries/implementation-summary-20260303.md)
- **Language**: general
- **Dependencies**: None

**Description**: Remove all `specs/` directories throughout the repository except for `ModelChecker/specs/`. Identify any specs content that should be preserved and migrate it appropriately before deletion. Document what was removed for reference.

---

### 30. Consolidate documentation directories
- **Effort**: 4-6 hours
- **Status**: [COMPLETED]
- **Research**: [research-001.md](030_consolidate_documentation/reports/research-001.md)
- **Plan**: [implementation-001.md](030_consolidate_documentation/plans/implementation-001.md)
- **Summary**: [implementation-summary-20260303.md](030_consolidate_documentation/summaries/implementation-summary-20260303.md)
- **Language**: general
- **Dependencies**: Task #27

**Description**: Reduce documentation to two directories: `ModelChecker/docs/` for general project information (less technical overviews, user guides) and `code/docs/` for technical documentation (API references, architecture, development standards). Review existing documentation across all docs directories, eliminate redundancy, preserve valuable content, and improve organization. Update all documentation cross-references.

---

### 31. Clean scripts and artifacts
- **Effort**: 2-3 hours
- **Status**: [PLANNED]
- **Research**: [research-001.md](031_clean_scripts_and_artifacts/reports/research-001.md)
- **Plan**: [implementation-001.md](031_clean_scripts_and_artifacts/plans/implementation-001.md)
- **Language**: general
- **Dependencies**: Task #27

**Description**: Review scripts and artifacts throughout `code/` subdirectories. Remove unnecessary scripts and artifacts. Improve organization and documentation of those that are needed. Ensure any cleanup scripts, maintenance utilities, or development tools are properly documented and organized.
