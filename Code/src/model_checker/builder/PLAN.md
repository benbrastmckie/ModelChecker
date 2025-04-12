# Builder Package Refactoring: Progress and Next Steps

## Implementation Progress

The refactoring of `builder.py` into a modular package is now underway. The following components have been implemented:

### Completed Components

✅ **Package Structure**: Basic directory structure created with proper test organization

- Core implementation in `builder/`
- Tests in `builder/tests/`
  ✅ **Core Utilities**:
- `progress.py`: Thread-based progress spinner extracted from BuildModule
- `validation.py`: Parameter validation utilities with explicit error messages
- `z3_utils.py`: Z3 model utilities for difference constraints and model extraction
  ✅ **Initial Class Implementations**:
- Basic implementations of `BuildModule`, `BuildProject`, and `BuildExample`
  ✅ **Test Infrastructure**:
- Comprehensive unit tests for all utility modules (21 tests passing)
- Custom test runner script (`test_builder.py`) for testing the package
- Test location follows pattern of keeping tests close to implementation
  ✅ **Documentation**:
- Package README with usage examples
- Docstrings for all classes and methods

### Current State

- Original `builder.py` remains intact
- New `builder/` package exists in parallel
- Tests validate core utility functionality

## Remaining Work

### 1. Core Class Implementations

#### 1.1 BuildModule Enhancements

- [ ] **Complete Module Loading**: Finalize module loading with proper error handling
- [ ] **Simplify Concurrency**: Improve concurrency models in `compare_semantics`
- [ ] **Improve Theory Translation**: Refine operator translation methods
- [ ] **Unit Tests**: Add tests in `tests/test_module.py` covering BuildModule functionality

#### 1.2 BuildProject Completion

- [ ] **Improve Template Handling**: Enhance file copying with better validation
- [ ] **Remove Interactive Components**: Replace all calls to `input()` with parameters
- [ ] **Enhance Error Messaging**: Improve error messages for file operations
- [ ] **Unit Tests**: Add tests in `tests/test_project.py` covering BuildProject functionality

#### 1.3 BuildExample Completion

- [ ] **Complete Z3 Integration**: Finish integration with z3_utils module
- [ ] **Improve Model Reporting**: Enhance model result formatting
- [ ] **Separate Result Presentation**: Complete separation of data and presentation
- [ ] **Unit Tests**: Add tests in `tests/test_example.py` covering BuildExample functionality

### 2. Integration and Testing

- [ ] **Integration Tests**: Tests covering interactions between components
- [ ] **Edge Cases**: Tests for boundary conditions and error handling
- [ ] **Performance Testing**: Verify performance of refactored code matches original

### 3. Migration Plan

#### Phase 1: Parallel Operation (Current)

- Both `builder.py` and `builder/` subpackage exist side-by-side
- Direct access to `builder.py` classes continues to work
- New development occurs in the subpackage

#### Phase 2: Transition Support

- [ ] Add deprecation warnings to `builder.py` (version n)
- [ ] Implement compatibility layer in `__init__.py` that routes old API calls to new implementations
- [ ] Update documentation to recommend new API

#### Phase 3: Complete Migration

- [ ] Remove compatibility layer (version n+1)
- [ ] Remove original `builder.py` file
- [ ] Update all internal usage to new API

## Implementation Strategy

### Approach to Completeness

1. **Iterative Enhancement**: Gradually enhance each component with improved functionality
2. **Test Coverage First**: For each enhancement, write tests before implementation
3. **Documentation Updates**: Keep documentation in sync with implementation changes

### Priorities

1. Complete core functionality in standalone modules
2. Add integration with existing codebase
3. Replace interactive I/O with parameter-based approach
4. Implement thorough testing

## Design Principles Applied

The implementation follows these key design principles from CLAUDE.md:

1. **Fail Fast**: Explicit validation with clear error messages
2. **Required Parameters**: No default values that mask errors
3. **Clear Data Flow**: Consistent data passing between components
4. **No Silent Failures**: Errors surface naturally without masking
5. **Break Old Code When Necessary**: Prioritize clarity over backward compatibility

## Completed Examples

Here are examples of the refactored approach in the implemented utilities:

### Progress Tracking

```python
# Before: Nested class with direct printing to stdout
class ProgressSpinner:
    def update(self):
        print(f"\rRunning model-checker: {self.progress_chars[self.current]}",
              end="", flush=True)

# After: Standalone class with configurable output and thread management
class Spinner:
    def __init__(self, message="Running model-checker", stream=sys.stdout):
        self.message = message
        self.stream = stream
        self._thread = None

    def start(self):
        self._thread = threading.Thread(target=self._spin)
        self._thread.daemon = True
        self._thread.start()
```

### Validation

```python
# Before: Inline validation with repetitive code
if not isinstance(premises, list) or not all(isinstance(p, str) for p in premises):
    raise TypeError(
        f"First element must be a list of strings, got {type(premises)}"
    )

# After: Standalone validation functions
def validate_example_case(example_case):
    """Validate an example case contains premises, conclusions and settings."""
    if not isinstance(example_case, (list, tuple)) or len(example_case) != 3:
        raise TypeError(
            "example_case must be a list/tuple containing exactly 3 elements"
        )
    # ...
```

### Z3 Utilities

```python
# Before: Complex Z3 handling embedded in BuildExample methods
def _update_solver(self, old_z3_model):
    try:
        # Complex Z3 operations with inconsistent error handling

# After: Clear, focused Z3 utilities
def create_difference_constraint(old_model, variables):
    """Create a constraint requiring the new model to differ from the old one."""
    if old_model is None:
        raise ValueError("Cannot create difference constraint from None model")
    # ...
```

## Next Immediate Steps

1. Complete the `BuildModule.run_model_check()` implementation
2. Add tests for BuildModule functionality
3. Enhance BuildProject's template handling
4. Complete the BuildExample implementation with improved Z3 integration
5. Develop additional test cases for full coverage

## Conclusion

The refactoring is progressing well with a strong foundation of utilities and tests. The modular approach is proving effective in separating concerns and improving clarity. The next phases will focus on completing the core class implementations and adding comprehensive tests before beginning the migration from the original monolithic file.
