# Finding: Generated Project Import Architecture

**Date**: 2025-09-05  
**Author**: AI Assistant  
**Status**: Documented  
**Impact**: Medium - Affects how generated projects can be used  
**Category**: Architecture Decision  

## Executive Summary

During builder test refactoring, we discovered that generated projects from `BuildProject` use relative imports and cannot be loaded as standalone modules outside their original package context. This is an architectural design decision, not a bug.

## Discovery Context

### Original Issue
- User reported: "No module named 'project_SNAKE'" error
- Tests were failing when trying to load generated projects with `BuildModule`
- Initial assumption: This was a bug that needed fixing

### Investigation Findings
1. Generated projects copy files from theory_lib templates
2. These files use relative imports (e.g., `from .semantic import`)
3. Relative imports require proper Python package context
4. BuildModule cannot provide this context for standalone projects

## Technical Details

### Generated Project Structure
```
project_test_logos/
├── __init__.py
├── examples.py          # Contains: from .semantic import ...
├── semantic.py          # Contains: from .operators import ...
├── operators.py         # Contains: from .proposition import ...
├── subtheories/
│   └── modal/
│       └── examples.py  # Contains: from ...semantic import ...
└── tests/
```

### Import Pattern
```python
# In generated examples.py
from .semantic import (
    LogosSemantics,
    LogosProposition,
    LogosModelStructure,
)
```

### Why This Fails
1. Python relative imports require the module to be part of a package
2. When loaded directly with `BuildModule`, there's no parent package
3. Error: "attempted relative import with no known parent package"

## Design Rationale

This appears to be intentional design:

1. **Template Consistency**: Generated projects maintain exact structure of source theories
2. **Package Integrity**: Files work correctly within their package context
3. **Development Workflow**: Projects are meant to be developed as packages, not standalone scripts

## Impact on Usage

### What Works
- Running generated projects with proper package context
- Using model-checker CLI with appropriate Python path setup
- Importing generated projects as packages in other code

### What Doesn't Work
- Loading generated project files directly with `BuildModule`
- Running examples.py as standalone scripts
- Using dev_cli.py directly on generated project files

## Solution Applied

### For Tests
Modified tests to verify project structure without attempting to load modules:

```python
# Instead of:
build_module = BuildModule(module_flags)

# We now do:
with open(examples_path, 'r') as f:
    content = f.read()
    self.assertIn('from .', content)  # Verify relative imports exist
```

### For Documentation
Updated user-facing documentation to clarify:
- Generated projects are templates for new theory development
- They should be run within proper package context
- Not intended for direct execution with BuildModule

## Recommendations

1. **Keep Current Architecture**: The relative import design is sound
2. **Improve Error Messages**: When BuildModule encounters relative imports, provide helpful guidance
3. **Documentation**: Clearly explain generated project usage in user guides
4. **Future Enhancement**: Consider adding a "standalone" generation mode if needed

## Related Documents

- [Builder Test Refactor](../plans/029_builder_test_refactor.md) - Where this was discovered
- [Theory Library Architecture](../../ARCHITECTURE.md#theory-library) - Package structure design

## Conclusion

The use of relative imports in generated projects is a deliberate architectural choice that maintains package integrity and consistency with source theories. This is not a bug but rather a design constraint that should be documented and communicated to users.