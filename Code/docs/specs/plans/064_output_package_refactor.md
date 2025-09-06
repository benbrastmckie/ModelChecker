# Plan 064: Output Package Refactor Implementation

**Status:** Planning Complete  
**Created:** 2025-01-09  
**Priority:** MEDIUM  
**Current Compliance:** 72%  
**Target Compliance:** 85%+  
**Estimated Effort:** 15 hours  

## Executive Summary

The output/ package needs architectural improvements, method extraction, and test modernization. Key focus areas are implementing strategy pattern for output modes and improving component separation.

## Critical Issues

1. **Method Complexity** - Several methods exceed guidelines
2. **Weak Architecture** - No clear pattern for output modes
3. **Test Organization** - Tests need modernization
4. **Mixed Responsibilities** - OutputManager handles too much

## Implementation Plan

### Phase 1: Foundation Cleanup (3 hours)
- Standardize import organization
- Extract constants for output configurations
- Create output strategy interface
- Fix documentation gaps

### Phase 2: Method Refinement (5 hours)
- Extract `save_model_interactive()` (65 lines)
- Refactor `_create_interactive_summary()` (60 lines)
- Break down `finalize()` method
- Extract formatting logic to helpers

### Phase 3: Architectural Improvements (4 hours)
- Implement OutputStrategy protocol
- Create BatchOutputStrategy, SequentialOutputStrategy
- Add dependency injection for strategies
- Separate concerns between manager and formatter

### Phase 4: Test Enhancement (3 hours)
- Reorganize tests by type
- Add isolation fixtures
- Create strategy pattern tests
- Add output verification tests

## Key Refactoring Tasks

### Strategy Pattern Implementation
```python
# Create output strategy protocol
class IOutputStrategy(Protocol):
    def save_example(self, name: str, data: Dict, formatted: str) -> None: ...
    def finalize(self) -> None: ...

# Implement strategies
class BatchOutputStrategy:
    """Accumulate and save at end."""
    
class SequentialOutputStrategy:
    """Save immediately to files."""
    
class InteractiveOutputStrategy:
    """Save with user prompts."""
```

### Method Extraction Example
```python
# Extract from save_model_interactive
def save_model_interactive(self, example_name, model_data, formatted_output, model_num):
    directory = self._ensure_example_directory(example_name)
    self._save_markdown_file(directory, model_num, formatted_output)
    self._save_json_file(directory, model_num, model_data)
    self._track_interactive_save(example_name, model_num)
    self._display_save_location(directory, model_num)
```

## Success Metrics
- All methods under 40 lines
- Clear strategy pattern implementation
- Test coverage above 80%
- Clean separation of concerns

---

**Next Action**: Implement after jupyter/ package complete