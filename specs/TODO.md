---
next_project_number: 32
---

# Task List

## Tasks

<!-- New tasks are prepended below this line -->

### 27. Flatten code/src/ directory structure
- **Effort**: 4-6 hours
- **Status**: [RESEARCHING]
- **Research**: [research-027.md](027_flatten_code_src_directory/reports/research-027.md)
- **Language**: python
- **Dependencies**: None

**Description**: Move contents of `code/src/model_checker/` into `code/src/` to eliminate unnecessary directory depth. Update all import references (relative and absolute), pyproject.toml, setup.py if present, and any other configuration files. Run tests before and after to confirm no regression. Track all path changes systematically.

---

### 28. Archive unused theory libraries
- **Effort**: 1-2 hours
- **Status**: [NOT STARTED]
- **Language**: python
- **Dependencies**: Task #27

**Description**: Archive `theory_lib/exclusion/` and `theory_lib/imposition/` directories to `code/boneyard/`. Update any references to these theories in the codebase. Ensure the boneyard directory structure preserves the original organization. Run tests to confirm no regression from removing these theories from active code paths.

---

### 29. Clean up specs directories
- **Effort**: 1 hour
- **Status**: [PLANNED]
- **Research**: [research-001.md](029_cleanup_specs_directories/reports/research-001.md)
- **Plan**: [implementation-001.md](029_cleanup_specs_directories/plans/implementation-001.md)
- **Language**: general
- **Dependencies**: None

**Description**: Remove all `specs/` directories throughout the repository except for `ModelChecker/specs/`. Identify any specs content that should be preserved and migrate it appropriately before deletion. Document what was removed for reference.

---

### 30. Consolidate documentation directories
- **Effort**: 4-6 hours
- **Status**: [NOT STARTED]
- **Language**: general
- **Dependencies**: Task #27

**Description**: Reduce documentation to two directories: `ModelChecker/docs/` for general project information (less technical overviews, user guides) and `code/docs/` for technical documentation (API references, architecture, development standards). Review existing documentation across all docs directories, eliminate redundancy, preserve valuable content, and improve organization. Update all documentation cross-references.

---

### 31. Clean scripts and artifacts
- **Effort**: 2-3 hours
- **Status**: [NOT STARTED]
- **Language**: general
- **Dependencies**: Task #27

**Description**: Review scripts and artifacts throughout `code/` subdirectories. Remove unnecessary scripts and artifacts. Improve organization and documentation of those that are needed. Ensure any cleanup scripts, maintenance utilities, or development tools are properly documented and organized.
