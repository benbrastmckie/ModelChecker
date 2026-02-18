# Implementation Plan: Add Subtheory Selection to CLI

**Date**: January 2025
**Author**: ModelChecker Development Team
**Status**: In Progress

## Executive Summary

This plan outlines the implementation of a new CLI feature that allows users to specify which logos subtheories to load when using the ModelChecker. Currently, using `-l logos` loads a default set of subtheories. This enhancement will provide fine-grained control over subtheory loading.

## 1. Problem Statement

Currently, when users run `model-checker -l logos`, it automatically loads the default subtheories (extensional, modal, constitutive, counterfactual). Users cannot:
- Load only specific subtheories they need
- Load experimental subtheories (like relevance) via CLI
- Create projects with only specific subtheories

## 2. Proposed Solution

### 2.1 CLI Interface Design

Add a new `--subtheory` (short form: `-st`) flag that accepts one or more subtheory names:

```bash
# Load specific subtheories
model-checker -l logos --subtheory counterfactual constitutive
model-checker -l logos --subtheory modal  # Auto-loads dependencies (extensional, counterfactual)
model-checker -l logos -st extensional    # Short form

# No special keywords - default loads all subtheories

# Backward compatibility
model-checker -l logos                      # Unchanged (loads default subtheories)
```

### 2.2 Dependency Management

Subtheories have dependencies that must be automatically resolved:
- `modal` → requires `extensional`, `counterfactual`
- `counterfactual` → requires `extensional`
- `relevance` → requires `constitutive`
- `constitutive` → no dependencies
- `extensional` → no dependencies

## 3. Implementation Details

### 3.1 Code Changes

#### A. CLI Parser Updates (`/src/model_checker/__main__.py`)

```python
theory_group.add_argument(
    '--subtheory', '-st',
    nargs='+',
    choices=['extensional', 'modal', 'constitutive', 'counterfactual',
             'relevance', 'all', 'default', 'minimal'],
    help='Specify which logos subtheories to load (applies only to logos theory)'
)
```

#### B. Theory Loading Logic (`/src/model_checker/builder/project.py`)

```python
def __init__(self, theory: str = 'logos', subtheories: Optional[List[str]] = None) -> None:
    self.theory = theory
    self.subtheories = subtheories

    # Handle special keywords
    if subtheories:
        if 'all' in subtheories:
            self.subtheories = ['extensional', 'modal', 'constitutive',
                               'counterfactual', 'relevance']
        elif 'default' in subtheories:
            self.subtheories = ['extensional', 'modal', 'constitutive',
                               'counterfactual']
        elif 'minimal' in subtheories:
            self.subtheories = ['extensional']
```

#### C. Module Loading (`/src/model_checker/builder/module.py`)

Update to pass subtheories to the logos theory loader when specified.

### 3.2 Documentation Updates

#### Files to Update:
1. `/Docs/usage/SETTINGS.md` - Remove 'verbose' from examples (not a valid setting)
2. `/Docs/usage/WORKFLOW.md` - Document new --subtheory usage
3. `/Docs/usage/PROJECT.md` - Show project creation with specific subtheories
4. `/Docs/usage/EXAMPLES.md` - Add examples using new syntax
5. `/Docs/usage/TOOLS.md` - Mention subtheory selection
6. `/Docs/installation/GETTING_STARTED.md` - Update quick start guide
7. `/Docs/installation/README.md` - Update installation examples

### 3.3 Error Handling

- Invalid subtheory names → Clear error message listing valid options
- Non-logos theory with --subtheory → Error: "The --subtheory flag only applies to the logos theory"
- Conflicting options → Resolve gracefully (e.g., if both 'all' and specific subtheories are given)

## 4. Testing Strategy

### 4.1 Unit Tests
- Test argument parsing with various combinations
- Test special keyword handling
- Test dependency resolution
- Test error cases

### 4.2 Integration Tests
- Test project creation with subtheories
- Test example execution with subtheory selection
- Test backward compatibility

### 4.3 Manual Testing Checklist
- [ ] `model-checker -l logos` works as before
- [ ] `model-checker -l logos --subtheory modal` loads modal + dependencies
- [ ] `model-checker -l logos --subtheory all` loads all subtheories
- [ ] `model-checker -l exclusion --subtheory modal` produces helpful error
- [ ] Project creation works with subtheory specification
- [ ] Help text clearly explains the feature

## 5. Rollout Plan

### Phase 1: Core Implementation (Current)
1. Update CLI parser
2. Modify theory loading logic
3. Test basic functionality

### Phase 2: Project Generation
1. Update BuildProject class
2. Ensure proper file copying
3. Update generated examples

### Phase 3: Documentation
1. Fix incorrect examples (verbose setting)
2. Update all documentation
3. Add comprehensive examples

### Phase 4: Testing & Release
1. Run full test suite
2. Manual testing
3. Update changelog

## 6. Success Criteria

- Users can load specific logos subtheories via CLI
- Dependencies are automatically resolved
- Backward compatibility is maintained
- Documentation is clear and comprehensive
- All tests pass

## 7. Future Enhancements

- GUI for subtheory selection in Jupyter interface
- Configuration file support for default subtheory sets
- Subtheory compatibility checking
- Dynamic subtheory discovery

## 8. Notes

- The 'verbose' setting mentioned in SETTINGS.md appears to be invalid and will be removed
- The relevance subtheory is experimental and not loaded by default
- Dependency resolution ensures all required operators are available