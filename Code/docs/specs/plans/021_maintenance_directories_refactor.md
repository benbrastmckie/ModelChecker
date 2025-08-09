# Plan 021: Maintenance Directories Refactor

## Overview

This plan separates maintenance documentation into two distinct domains:

- **Code/maintenance/**: Standards and upkeep for all code-related activities
- **Docs/maintenance/**: Standards and upkeep for educational/methodological documentation

The refactor eliminates overlap between these directories while preserving Code/docs/ for technical but general documentation.

## Current State Analysis

### Docs/maintenance/

Currently contains a mix of:

- **Code-specific standards**: FORMULA_FORMATTING.md, EXAMPLES_STRUCTURE.md, CODE_ORGANIZATION.md, ERROR_HANDLING.md, PERFORMANCE.md, TESTING_STANDARDS.md
- **Documentation standards**: DOCUMENTATION_STANDARDS.md, README_STANDARDS.md, AUDIENCE.md
- **Process standards**: VERSION_CONTROL.md, UNICODE_GUIDELINES.md
- **Templates**: README templates for various purposes

### Code/docs/

Currently contains:

- Technical documentation for development (IMPLEMENTATION.md, DEVELOPMENT.md, ARCHITECTURE.md)
- Quick references (STYLE_GUIDE.md, TESTS.md)
- Process documentation that overlaps with maintenance standards

## Proposed Structure

### Code/maintenance/

```
Code/maintenance/
├── README.md                       # Code maintenance hub
├── IMPLEMENT.md                    # Spec execution guide (concise workflow)
├── CODE_STANDARDS.md               # Unified code quality standards
├── FORMULA_FORMATTING.md           # LaTeX notation in code
├── EXAMPLES_STRUCTURE.md           # examples.py file standards
├── CODE_ORGANIZATION.md            # Module structure and imports
├── ERROR_HANDLING.md               # Exception handling patterns
├── PERFORMANCE.md                  # Z3 optimization guidelines
├── TESTING_STANDARDS.md            # Test requirements and TDD
├── UNICODE_GUIDELINES.md           # Character encoding for code
├── VERSION_CONTROL.md              # Git workflow for code changes
└── templates/
    ├── THEORY_TEMPLATE.py          # Theory implementation template
    ├── EXAMPLES_TEMPLATE.py        # Examples file template
    └── TEST_TEMPLATE.py            # Test file template
```

### Docs/maintenance/

```
Docs/maintenance/
├── README.md                       # Documentation maintenance hub
├── DOCUMENTATION_STANDARDS.md      # General documentation principles
├── README_STANDARDS.md             # README structure guidelines
├── AUDIENCE.md                     # Interdisciplinary accessibility
├── EDUCATIONAL_CONTENT.md          # Tutorial and guide standards
├── METHODOLOGICAL_DOCS.md          # Research methodology standards
├── CROSS_REFERENCES.md             # Inter-document linking standards
└── templates/
    ├── README_TEMPLATE.md          # General README template
    ├── TUTORIAL_TEMPLATE.md        # Educational content template
    └── METHODOLOGY_TEMPLATE.md     # Research documentation template
```

### Code/docs/ (unchanged focus)

```
Code/docs/
├── README.md                       # Technical documentation hub
├── IMPLEMENTATION.md               # Feature development process (comprehensive guide)
├── DEVELOPMENT.md                  # Environment setup
├── ARCHITECTURE.md                 # System design
├── TOOLS.md                        # Advanced debugging
├── LICENSE_INHERITANCE.md          # License guidelines
├── INTERACTIVE_SAVE.md             # Feature documentation
└── specs/                          # Technical specifications
```

**Note**: IMPLEMENTATION.md remains in Code/docs/ as a comprehensive guide for planning and designing features, while the new IMPLEMENT.md in Code/maintenance/ provides a concise execution workflow for implementing approved specs.

## Migration Strategy

### Phase 1: Create New Directories

1. Create Code/maintenance/ with initial README
2. Create IMPLEMENT.md in Code/maintenance/ with spec execution workflow
3. Update Docs/maintenance/ README to reflect new scope

### Phase 2: Migrate Code-Related Standards

Move from Docs/maintenance/ to Code/maintenance/:

- FORMULA_FORMATTING.md
- EXAMPLES_STRUCTURE.md
- CODE_ORGANIZATION.md
- ERROR_HANDLING.md
- PERFORMANCE.md
- TESTING_STANDARDS.md
- VERSION_CONTROL.md (code-specific parts)
- UNICODE_GUIDELINES.md (code-specific parts)

### Phase 3: Split Shared Standards

1. VERSION_CONTROL.md → Split into:
   - Code/maintenance/VERSION_CONTROL.md (code commits, branching)
   - Docs/maintenance/VERSION_CONTROL.md (documentation updates)

2. UNICODE_GUIDELINES.md → Split into:
   - Code/maintenance/UNICODE_GUIDELINES.md (LaTeX in code)
   - Docs/maintenance/UNICODE_GUIDELINES.md (Unicode in docs)

### Phase 4: Remove Redundancies

1. Consolidate overlapping content between Code/docs/STYLE_GUIDE.md and new Code/maintenance/ files
2. Update Code/docs/TESTS.md to reference Code/maintenance/TESTING_STANDARDS.md
3. Remove process documentation from Code/docs/ that belongs in maintenance

### Phase 5: Update Cross-References

1. Update all relative links in moved files
2. Update CLAUDE.md to reference new structure
3. Update main README files to point to correct maintenance directories

## Key Principles

### Separation of Concerns

- **Code/maintenance/**: How to write, test, and maintain code
- **Docs/maintenance/**: How to write and maintain documentation
- **Code/docs/**: Technical guides for using the framework

### No Duplication

- Each standard lives in exactly one place
- Cross-references connect related standards
- Clear ownership of each maintenance aspect

### Accessibility

- Code contributors look in Code/maintenance/
- Documentation contributors look in Docs/maintenance/
- Framework users look in Code/docs/

## Benefits

1. **Clear Navigation**: Contributors know exactly where to find relevant standards
2. **Reduced Overlap**: No more duplicate or conflicting guidelines
3. **Focused Maintenance**: Each directory has a clear maintenance scope
4. **Better Organization**: Standards grouped by their application domain

## Implementation Checklist

- [ ] Create Code/maintenance/ directory structure
- [ ] Write new Code/maintenance/README.md
- [ ] Create IMPLEMENT.md with focused spec execution guide
- [ ] Update Docs/maintenance/README.md for new scope
- [ ] Migrate code-specific standards files
- [ ] Split shared standards (VERSION_CONTROL, UNICODE)
- [ ] Create new templates for Code/maintenance/
- [ ] Update educational templates in Docs/maintenance/
- [ ] Consolidate overlapping content in Code/docs/
- [ ] Update all cross-references and relative links
- [ ] Update CLAUDE.md with new structure and IMPLEMENT.md reference
- [ ] Test all documentation links
- [ ] Update any automated documentation tools

## Testing

After implementation:

1. Verify all moved files retain correct formatting
2. Check all relative links work correctly
3. Ensure no broken references in documentation
4. Confirm templates are in appropriate directories
5. Test that contributors can navigate to correct standards

## Rollback Plan

If issues arise:

1. Git revert the commit(s) that moved files
2. Restore original cross-references
3. Document lessons learned for future attempt

## Success Criteria

- Zero broken links in documentation
- Clear separation between code and documentation maintenance
- All contributors can find relevant standards easily
- No duplicate maintenance guidelines
- Simplified navigation structure
