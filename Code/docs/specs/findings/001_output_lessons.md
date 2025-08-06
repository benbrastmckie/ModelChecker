# Debugging Findings: Output System Integration

[← Back to Output Package](../README.md) | [Implementation Plan →](SAVE_OUTPUT.md)

## Overview

This document captures debugging insights from the output system implementation, following the [Debugging Philosophy](../../../../CLAUDE.md#debugging-philosophy). These findings reveal systemic patterns that can improve the entire codebase.

## Error Pattern: API Signature Mismatches

### Discovery Context

During output system integration, we encountered:
```python
TypeError: LogosModelStructure.print_to() got an unexpected keyword argument 'print_impossible'
```

### Root Cause Analysis

The error revealed a systemic issue with API evolution:

1. **Historical API**: `print_to(default_settings, example_name, theory_name, print_constraints=None, output=sys.__stdout__)`
2. **New Integration**: Attempted to pass individual settings as keyword arguments
3. **Pattern**: Integration layers making incorrect assumptions about existing APIs

### Systemic Solution

```python
# PATTERN: When integrating with existing APIs, always verify signatures
# BAD: Assume keyword arguments based on parameter names
model_structure.print_to(
    example_name=example_name,
    print_impossible=self.print_impossible,  # WRONG: Not a parameter
    ...
)

# GOOD: Match exact signature, passing settings as expected
default_settings = {
    'print_impossible': self.print_impossible,
    'print_constraints': self.print_constraints,
    # ... other settings
}
model_structure.print_to(
    default_settings,  # Positional argument
    example_name,      # Positional argument
    theory_name,       # Positional argument
    print_constraints=self.print_constraints,  # Valid kwarg
    output=output or sys.stdout
)
```

### Prevention Measures

1. **API Documentation**: Add explicit signature documentation to all public methods
2. **Integration Tests**: Test integration points specifically for signature compatibility
3. **Type Hints**: Use type hints to make signatures explicit and checkable

## Error Pattern: Stateful Context Managers

### Discovery Context

Output capture was returning empty despite correct flag settings:
```python
DEBUG: Captured text length: 0  # Despite output being displayed
```

### Root Cause Analysis

The OutputCapture context manager was resetting its buffer on entry:
```python
# ANTI-PATTERN: Using decorator for context manager
@contextmanager
def capture(self):
    self.captured = StringIO()  # BUG: Resets previous captures
    # ...
```

### Systemic Solution

```python
# PATTERN: Implement context managers as classes without decorators
class OutputCapture:
    def __init__(self):
        self.captured = StringIO()
        self.original_stdout = None
        self.original_stderr = None
        self.tee_mode = True
        
    def __enter__(self):
        """Enter the context manager - start capturing output."""
        # Don't reset buffer - accumulate captures
        self.original_stdout = sys.stdout
        self.original_stderr = sys.stderr
        
        if self.tee_mode:
            sys.stdout = TeeOutput(self.original_stdout, self.captured)
            sys.stderr = TeeOutput(self.original_stderr, self.captured)
        else:
            sys.stdout = self.captured
            sys.stderr = self.captured
            
        return self
        
    def __exit__(self, exc_type, exc_val, exc_tb):
        """Exit the context manager - restore original streams."""
        sys.stdout = self.original_stdout
        sys.stderr = self.original_stderr
        return False  # Don't suppress exceptions
        
    def reset(self):
        """Explicitly reset capture buffer when needed."""
        self.captured = StringIO()
        
    def get_output(self, strip_ansi=True):
        """Get captured output, optionally stripping ANSI codes."""
        output = self.captured.getvalue()
        if strip_ansi:
            return self.strip_ansi_codes(output)
        return output
```

### Prevention Measures

1. **Explicit State Management**: Make state changes explicit rather than implicit
2. **Separation of Concerns**: Separate initialization from usage contexts
3. **Clear Documentation**: Document when state is modified

## Cross-Cutting Improvements

### 1. Default Parameter Pattern

**Issue**: Runtime values captured at function definition
```python
def function(output=sys.stdout):  # BUG: Captures stdout at import time
```

**Solution**: Project-wide pattern
```python
def function(output=None):
    output = output or sys.stdout  # Evaluate at runtime
```

### 2. Integration Testing Pattern

**Issue**: Integration points not tested for compatibility
**Solution**: Specific integration test suite
```python
class TestIntegrationCompatibility:
    def test_print_to_signature_compatibility(self):
        # Verify all theory print_to methods have compatible signatures
        for theory in ALL_THEORIES:
            sig = inspect.signature(theory.ModelStructure.print_to)
            assert list(sig.parameters.keys())[:3] == ['self', 'default_settings', 'example_name']
```

### 3. API Evolution Pattern

**Issue**: APIs evolve inconsistently across theories
**Solution**: Base class enforcement without decorators
```python
class BaseModelStructure:
    """Base class enforcing consistent API signatures across theories."""
    
    def print_to(self, default_settings: dict, example_name: str, 
                 theory_name: str, **kwargs) -> None:
        """Enforced signature for all implementations.
        
        Subclasses MUST override this method with the same signature.
        """
        raise NotImplementedError(
            f"{self.__class__.__name__} must implement print_to() method "
            f"with signature: print_to(default_settings, example_name, theory_name, **kwargs)"
        )
```

## Refactored Save Output Implementation

### Complete Solution Without Decorators

The save_output functionality should be refactored to avoid decorators and fix the capture issue:

```python
# output/capture.py - Full implementation without decorators
class OutputCapture:
    """Captures stdout/stderr output with ANSI stripping capabilities."""
    
    def __init__(self):
        """Initialize the output capture system."""
        self.captured = StringIO()
        self.original_stdout = None
        self.original_stderr = None
        self.tee_mode = True  # Show output while capturing
        self._in_context = False
        
    def __enter__(self):
        """Enter the context manager - start capturing output."""
        if self._in_context:
            raise RuntimeError("OutputCapture context already active")
            
        self._in_context = True
        self.original_stdout = sys.stdout
        self.original_stderr = sys.stderr
        
        if self.tee_mode:
            sys.stdout = TeeOutput(self.original_stdout, self.captured)
            sys.stderr = TeeOutput(self.original_stderr, self.captured)
        else:
            sys.stdout = self.captured
            sys.stderr = self.captured
            
        return self
        
    def __exit__(self, exc_type, exc_val, exc_tb):
        """Exit the context manager - restore original streams."""
        sys.stdout = self.original_stdout
        sys.stderr = self.original_stderr
        self._in_context = False
        return False  # Don't suppress exceptions
        
    def get_output(self, strip_ansi=True):
        """Get captured output, optionally stripping ANSI codes."""
        output = self.captured.getvalue()
        if strip_ansi:
            return self.strip_ansi_codes(output)
        return output
        
    def strip_ansi_codes(self, text):
        """Remove ANSI escape sequences from text.
        
        Note: This is an instance method, not static, to avoid decorators.
        """
        import re
        ansi_escape = re.compile(r'\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])')
        return ansi_escape.sub('', text)
        
    def reset(self):
        """Explicitly reset capture buffer when needed."""
        if self._in_context:
            raise RuntimeError("Cannot reset while capture is active")
        self.captured = StringIO()


# output/__init__.py - OutputManager using the capture properly
class OutputManager:
    """Main interface for the unified output system."""
    
    def __init__(self, settings):
        """Initialize output manager with settings."""
        self.settings = settings
        self.color_manager = ColorManager(force_color=None)
        self.print_manager = PrintManager(settings, self.color_manager)
        self.save_manager = SaveManager()
        
        # Create single capture instance for the entire session
        if settings.get('save_output', False):
            self.capture = OutputCapture()
        else:
            self.capture = None
    
    def start_capture(self):
        """Start output capture for saving.
        
        Returns:
            The capture object to use as context manager, or None if disabled
        """
        return self.capture  # Return the capture object itself
        
    def save_output_if_enabled(self, context=None):
        """Save captured output if enabled."""
        if self.capture and self.settings.get('save_output', False):
            output_text = self.capture.get_output(strip_ansi=True)
            if output_text:
                return self.save_manager.prompt_save(output_text, context)
        return None


# builder/module.py - Usage in BuildModule
def run_examples(self):
    """Run examples with proper output capture."""
    from datetime import datetime
    
    # Get capture object (not a context manager method)
    capture = self.output_manager.start_capture()
    
    try:
        if capture:
            # Use the capture object as context manager
            with capture:
                self._run_examples_internal()
        else:
            self._run_examples_internal()
    finally:
        # Handle saving after execution
        if self.general_settings.get('save_output'):
            context = {
                'module_name': self.module_name,
                'timestamp': datetime.now()
            }
            self.output_manager.save_output_if_enabled(context)
```

### Key Changes

1. **No Decorators**: Context manager implemented with `__enter__` and `__exit__` methods
2. **Single Capture Instance**: One OutputCapture object for the entire session
3. **State Preservation**: Buffer is not reset between captures
4. **Clear Separation**: OutputManager returns the capture object, not a context method
5. **Error Handling**: Proper state validation to prevent nested contexts

## Lessons Learned

1. **Integration Points are Fragile**: Where components meet, assumptions break
2. **State Management Requires Clarity**: Implicit state changes cause subtle bugs
3. **Consistency Enables Evolution**: Consistent patterns allow safe refactoring
4. **Tests Reveal Design Issues**: Good tests expose architectural problems
5. **Decorators Hide Complexity**: Explicit implementations are clearer and more maintainable

## Action Items

1. **Audit Integration Points**: Check all places where components interface
2. **Remove All Decorators**: Replace with explicit implementations throughout codebase
3. **Document API Contracts**: Make signatures and expectations explicit
4. **Create Integration Test Suite**: Specifically test component boundaries
5. **Implement Refactored Solution**: Apply the decorator-free save_output implementation

## References

- [Debugging Philosophy](../../../../CLAUDE.md#debugging-philosophy) - Root cause analysis approach
- [Style Guide](../../../../docs/STYLE_GUIDE.md#debugging-philosophy) - Quick reference for debugging
- [Testing Guide](../../../../docs/TESTS.md) - Test-driven debugging methodology

---

[← Back to Output Package](../README.md) | [Implementation Plan →](SAVE_OUTPUT.md)