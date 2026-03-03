# Research Report: Task #30

**Task**: 30 - consolidate_documentation
**Started**: 2026-03-03T00:00:00Z
**Completed**: 2026-03-03T00:30:00Z
**Effort**: Medium (documentation reorganization with cross-reference updates)
**Dependencies**: Task #27 (completed)
**Sources/Inputs**: Codebase exploration (Glob/Grep/Read)
**Artifacts**: specs/030_consolidate_documentation/reports/research-001.md
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- Repository has 5 documentation directories: `docs/`, `code/docs/`, and 3 theory-specific `docs/` directories within `code/src/model_checker/theory_lib/`
- Clear separation already exists between user-facing (`docs/`) and technical (`code/docs/`) documentation
- Primary consolidation opportunity: `docs/maintenance/` should move to `code/docs/` since it covers code-specific standards
- Theory-specific documentation in `theory_lib/*/docs/` should remain in place (co-located with implementation)
- Approximately 90+ cross-references need updating after reorganization

## Context & Scope

### Research Objectives
1. Inventory all documentation directories and files
2. Categorize documentation by audience (user vs developer)
3. Identify redundancy and consolidation opportunities
4. Map cross-references requiring updates

### Current Documentation Structure

```
ModelChecker/
├── docs/                                    # ~50 files, User/researcher-facing
│   ├── README.md                            # Documentation hub
│   ├── installation/                        # 10 files - Setup guides
│   ├── usage/                               # 9 files - Usage workflows
│   ├── architecture/                        # 12 files - System concepts (visual)
│   ├── theory/                              # 5 files - Theoretical background
│   └── maintenance/                         # 9 files - Documentation standards
│
├── code/docs/                               # ~35 files, Developer-facing
│   ├── README.md                            # Technical docs hub
│   ├── core/                                # 4 files - CODE_STANDARDS, ARCHITECTURE, etc.
│   ├── development/                         # 7 files - Development workflow
│   ├── implementation/                      # 4 files - Implementation patterns
│   ├── quality/                             # 4 files - Metrics, testing
│   ├── contracts/                           # 3 files - System contracts
│   ├── specific/                            # 5 files - Component standards
│   ├── api/                                 # 2 files - API references
│   ├── guides/                              # 2 files - Developer guides
│   └── templates/                           # 1 file - Code templates
│
├── code/src/model_checker/theory_lib/docs/  # 7 files, Theory library docs
├── code/src/model_checker/theory_lib/logos/docs/     # 6 files
└── code/src/model_checker/theory_lib/bimodal/docs/   # 6 files
```

## Findings

### 1. Content Analysis by Target Audience

#### User/Researcher-Facing (should stay in `docs/`)
| Directory | Content Type | Recommendation |
|-----------|--------------|----------------|
| `docs/installation/` | Setup guides, troubleshooting | Keep in `docs/` |
| `docs/usage/` | Workflows, examples, operators | Keep in `docs/` |
| `docs/architecture/` | System concepts with diagrams | Keep in `docs/` |
| `docs/theory/` | Theoretical background | Keep in `docs/` |

#### Developer-Facing (should stay in `code/docs/`)
| Directory | Content Type | Recommendation |
|-----------|--------------|----------------|
| `code/docs/core/` | Code standards, architecture patterns | Keep in `code/docs/` |
| `code/docs/development/` | Feature implementation, debugging | Keep in `code/docs/` |
| `code/docs/quality/` | Metrics, review checklists | Keep in `code/docs/` |
| `code/docs/implementation/` | Error handling, performance | Keep in `code/docs/` |

#### Misplaced Content (consolidation opportunity)
| Directory | Current Location | Issue | Recommendation |
|-----------|-----------------|-------|----------------|
| `docs/maintenance/` | `docs/` | Contains code/documentation standards, targets developers | Move to `code/docs/standards/` |
| `docs/maintenance/quality/` | `docs/` | Documentation quality control | Move to `code/docs/standards/documentation/` |
| `docs/maintenance/templates/` | `docs/` | README templates for code directories | Move to `code/docs/templates/` |

### 2. Redundancy Analysis

#### Identified Overlaps

1. **Architecture Documentation**
   - `docs/architecture/README.md` (236 lines) - Visual, conceptual overview
   - `code/docs/core/ARCHITECTURE.md` (901 lines) - Code patterns, implementation details
   - **Verdict**: NOT redundant - different audiences and detail levels
   - **Action**: Keep both, ensure clear cross-references

2. **Documentation Standards**
   - `docs/maintenance/quality/DOCUMENTATION_STANDARDS.md` (275 lines) - General doc standards
   - `code/docs/core/DOCUMENTATION.md` (if exists) - Code documentation
   - **Verdict**: Partially redundant, both target documentation creation
   - **Action**: Consolidate into `code/docs/` since it's primarily for contributors

3. **Templates**
   - `docs/maintenance/templates/` - README templates for theory directories
   - `code/docs/templates/` - Code templates (theory_template.py, etc.)
   - **Verdict**: Related but distinct purposes
   - **Action**: Merge into `code/docs/templates/` with subdirectories

### 3. Theory-Specific Documentation

Theory documentation within `code/src/model_checker/theory_lib/*/docs/` should **remain co-located** with implementations:

- `theory_lib/docs/` - Cross-theory documentation (USAGE_GUIDE, CONTRIBUTING)
- `theory_lib/logos/docs/` - Logos-specific API, architecture
- `theory_lib/bimodal/docs/` - Bimodal-specific documentation

**Rationale**: Theory documentation is tightly coupled to implementation code. Co-location aids discovery and maintenance.

### 4. Cross-Reference Impact Analysis

Found approximately **90+ cross-references** between documentation files:

| Reference Pattern | Count | Impact |
|-------------------|-------|--------|
| `code/docs/` from `docs/` | 41 | None (keep target) |
| `docs/maintenance/` from anywhere | 6 | Must update |
| `../README.md` relative paths | 50+ | May need updates depending on moves |
| Absolute GitHub URLs | 15+ | Must update if files move |

### 5. Proposed Final Structure

```
ModelChecker/
├── docs/                                    # User/researcher documentation
│   ├── README.md                            # Documentation hub
│   ├── installation/                        # Setup and configuration
│   ├── usage/                               # Practical workflows
│   ├── architecture/                        # Conceptual system overview
│   └── theory/                              # Theoretical foundations
│
└── code/docs/                               # Technical/developer documentation
    ├── README.md                            # Technical docs hub
    ├── core/                                # Core standards
    │   ├── CODE_STANDARDS.md
    │   ├── ARCHITECTURE.md
    │   ├── TESTING_GUIDE.md
    │   └── DOCUMENTATION.md
    ├── development/                         # Development practices
    ├── implementation/                      # Implementation patterns
    ├── quality/                             # Quality assurance
    ├── contracts/                           # System contracts
    ├── specific/                            # Component standards
    ├── api/                                 # API references
    ├── guides/                              # Developer guides
    ├── standards/                           # NEW: from docs/maintenance/
    │   ├── documentation/                   # Documentation standards
    │   │   ├── DOCUMENTATION_STANDARDS.md
    │   │   ├── README_STANDARDS.md
    │   │   └── CONTINUOUS_IMPROVEMENT.md
    │   ├── AUDIENCE.md
    │   └── VERSION_CONTROL.md
    └── templates/                           # EXPANDED: merge with docs/maintenance/templates/
        ├── code/                            # Code templates (existing)
        └── documentation/                   # Documentation templates (from maintenance)
```

## Decisions

1. **Keep dual docs/ and code/docs/ structure** - This separation already serves its purpose well
2. **Move docs/maintenance/ to code/docs/standards/** - This content targets contributors, not users
3. **Preserve theory_lib/*/docs/ in place** - Co-location with implementation is valuable
4. **Do NOT merge architecture docs** - Different detail levels serve different audiences

## Risks & Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Broken cross-references | High | Medium | Systematic search-and-replace; test all links |
| User confusion during transition | Low | Low | Update README navigation first |
| Lost content | Low | High | Git history preserves all; no deletions without review |
| Incomplete migration | Medium | Medium | Create checklist of all files to move |

## Implementation Recommendations

### Phase 1: Prepare
1. Create `code/docs/standards/` and `code/docs/standards/documentation/` directories
2. Update `code/docs/README.md` to reference new structure
3. Create `code/docs/templates/documentation/` directory

### Phase 2: Move Files
1. Move `docs/maintenance/quality/*.md` to `code/docs/standards/documentation/`
2. Move `docs/maintenance/templates/*.md` to `code/docs/templates/documentation/`
3. Move `docs/maintenance/AUDIENCE.md` and `VERSION_CONTROL.md` to `code/docs/standards/`
4. Delete empty `docs/maintenance/` directory

### Phase 3: Update Cross-References
1. Search for all references to `docs/maintenance/`
2. Update paths to new `code/docs/standards/` locations
3. Update `docs/README.md` to remove maintenance section
4. Update navigation links in moved files

### Phase 4: Verify
1. Test all documentation links
2. Review README navigation paths
3. Ensure GitHub renders correctly

## Appendix

### Files to Move

| Source | Destination |
|--------|-------------|
| `docs/maintenance/README.md` | `code/docs/standards/README.md` |
| `docs/maintenance/AUDIENCE.md` | `code/docs/standards/AUDIENCE.md` |
| `docs/maintenance/VERSION_CONTROL.md` | `code/docs/standards/VERSION_CONTROL.md` |
| `docs/maintenance/quality/README.md` | `code/docs/standards/documentation/README.md` |
| `docs/maintenance/quality/DOCUMENTATION_STANDARDS.md` | `code/docs/standards/documentation/DOCUMENTATION_STANDARDS.md` |
| `docs/maintenance/quality/README_STANDARDS.md` | `code/docs/standards/documentation/README_STANDARDS.md` |
| `docs/maintenance/quality/CONTINUOUS_IMPROVEMENT.md` | `code/docs/standards/documentation/CONTINUOUS_IMPROVEMENT.md` |
| `docs/maintenance/templates/README.md` | `code/docs/templates/documentation/README.md` |
| `docs/maintenance/templates/README_TEMPLATE.md` | `code/docs/templates/documentation/README_TEMPLATE.md` |
| `docs/maintenance/templates/THEORY_README.md` | `code/docs/templates/documentation/THEORY_README.md` |
| `docs/maintenance/templates/SUBTHEORY_README.md` | `code/docs/templates/documentation/SUBTHEORY_README.md` |

### Search Patterns for Cross-Reference Updates

```bash
# Find all references to maintenance directory
grep -r "docs/maintenance" --include="*.md" .

# Find all references needing update after move
grep -r "maintenance/quality" --include="*.md" .
grep -r "maintenance/templates" --include="*.md" .
```

### Documentation Statistics

| Directory | File Count | Total Lines |
|-----------|------------|-------------|
| `docs/` | ~50 | ~8,500 |
| `code/docs/` | ~35 | ~12,000 |
| `theory_lib/*/docs/` | ~19 | ~3,000 |
| **Total** | ~104 | ~23,500 |
