# Progress Module Tests

[← Back to Progress](../README.md) | [Test Standards →](../../../../../maintenance/TESTING_STANDARDS.md)

## Test Suite Structure

```
tests/
├── README.md               # This file - test documentation
├── __init__.py            # Test package initialization  
├── test_animated.py       # Animated progress bar tests
├── test_core.py           # Core progress tracking tests
├── test_display.py        # Display adapter tests
└── test_spinner.py        # Spinner component tests
```

## Running Tests

```bash
# Run all progress tests
pytest src/model_checker/output/progress/tests/

# Run specific test file
pytest src/model_checker/output/progress/tests/test_core.py

# Run with coverage
pytest --cov=model_checker.output.progress src/model_checker/output/progress/tests/

# Run specific test method
pytest -k "test_single_model_progress"
```

## Test Categories

### Unit Tests

#### Core Components (test_core.py) - 14 tests
- `TestUnifiedProgress`: Main progress tracking functionality (6 tests)
  - Single model progress tracking
  - Multiple model iteration tracking
  - Isomorphic model skip counting
  - Timing and elapsed time calculations
  - Model not found scenarios
  - Cleanup and finalization
- `TestProgressBar`: Abstract interface tests (3 tests)
  - Abstract method enforcement
  - Interface method definitions
  - Concrete implementation patterns
- `TestUnifiedProgressEdgeCases`: Edge case handling (5 tests)
  - Zero models requested
  - Custom start time synchronization
  - Multiple starts for same model
  - Skipped count reset between searches
  - Default display creation

#### Animated Progress (test_animated.py) - 9 tests
- `TestTimeBasedProgress`: Time-based progress animation
  - Progress animation over time
  - Immediate completion handling
  - Timeout-based completion
  - Model/skip count tracking
  - Visual progress bar rendering
  - Thread cleanup on completion
  - Color support detection
  - Custom start time synchronization

#### Display Adapters (test_display.py) - 18 tests
- `TestProgressDisplay`: Base display interface (2 tests)
  - Abstract method enforcement
  - Interface method verification
- `TestTerminalDisplay`: Terminal output adapter (11 tests)
  - Stream initialization (custom and default)
  - Enabled state management
  - Message length tracking
  - Carriage return behavior
  - Line clearing logic
  - Terminal width handling
  - Update/complete/clear operations
- `TestBatchDisplay`: Batch mode display (4 tests)
  - Initialization with stream
  - No-op behavior verification
  - Silent operation in batch mode

#### Spinner Component (test_spinner.py) - 13 tests
- `TestSpinner`: Loading spinner functionality
  - Initialization with defaults and custom values
  - Progress character verification
  - Thread creation and daemon mode
  - Start/stop behavior
  - Animation cycling
  - Display clearing on stop
  - Multiple start call handling
  - Index wrapping behavior
  - Message formatting

## Test Coverage Requirements

Following the testing standards:
- Minimum 80% code coverage for all modules
- 100% coverage for public interfaces
- All edge cases and error conditions tested

Current coverage targets:
- `core.py`: Full coverage of UnifiedProgress class
- `animated.py`: Full coverage including threading behavior
- `display.py`: All display adapters and terminal detection
- `spinner.py`: Complete spinner lifecycle

## Test Organization

Tests follow the Arrange-Act-Assert pattern:

```python
def test_specific_behavior(self):
    """Test description of specific behavior."""
    # Arrange
    display = MockDisplay()
    progress = UnifiedProgress(total_models=3, display=display)
    
    # Act
    progress.start_model_search(1)
    progress.model_checked()
    
    # Assert
    assert progress.models_checked == 1
    assert len(display.messages) > 0
```

## Mock Objects and Test Utilities

### MockDisplay
A test double for ProgressDisplay that captures all output:
- Records all update messages
- Tracks completion and clear calls
- Simulates non-TTY environment

### Test Fixtures
Common test data and utilities are defined at module level:
- Timeout values for animation tests
- Standard progress bar configurations
- Expected output patterns

## Adding New Tests

When adding tests for new functionality:

1. Choose the appropriate test file based on component
2. Create descriptive test method names
3. Include docstrings explaining what is tested
4. Use mocks to isolate components
5. Test both success and failure cases
6. Verify thread safety for animated components

Example test structure:
```python
def test_new_feature_behavior(self):
    """Test that new feature behaves correctly under specific conditions."""
    # Setup test conditions
    # Execute the feature
    # Verify expected outcomes
    # Check edge cases
```

## Performance Considerations

- Animation tests use short timeouts (0.1-0.5s) to keep test suite fast
- Thread cleanup is verified to prevent resource leaks
- Large iteration counts are tested but with minimal delays

## Known Limitations

- Color support testing relies on environment detection
- Thread timing tests may be sensitive to system load
- Terminal width detection uses standard assumptions

---

[← Back to Progress](../README.md) | [Test Standards →](../../../../../maintenance/TESTING_STANDARDS.md)