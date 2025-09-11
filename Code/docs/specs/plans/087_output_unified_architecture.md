# Plan 087: Output Package Unified Architecture

**Status:** Approved  
**Priority:** P0 (EMERGENCY)  
**Timeline:** 1 week  
**Compliance Score:** 92/100 → 95/100  
**Dependencies:** [Research 043: Output Package and Notebook Generation Issues](../research/043_output_notebook_generation_issues.md)

## Executive Summary

The output package has **critical functional issues** despite high compliance scores. Tests are failing and notebook generation is broken when using `--save` without arguments. This plan implements Solution 3 from Research 043: **unifying all output generation through a single architectural pipeline** to create the highest quality product for the next package release.

## Critical Issues (from Research 043)

### Issue 1: Failing Test
- `test_from_cli_args_save_flag_ignores_jupyter` expects notebook format to be filtered
- OutputConfig actually includes FORMAT_NOTEBOOK in enabled_formats
- **Impact:** Test suite fails, unclear design intent

### Issue 2: Broken Notebook Generation
- `--save` without arguments doesn't generate notebooks
- Empty args.save list causes notebook detection to fail
- **Impact:** Users must explicitly specify `--save jupyter` 

### Issue 3: Architectural Split
- OutputManager handles markdown/json through unified pipeline
- BuildModule handles notebooks through direct calls
- **Impact:** Duplicate logic, inconsistent behavior, maintenance burden

## Requirements

### Functional Requirements
1. **`--save` generates ALL output types** (markdown, json, notebook)
2. **`--save <formats>` generates only specified formats**
3. **Future formats automatically included in `--save` default**
4. **All formats use unified generation pipeline**
5. **All tests pass with clear design intent**

### Architectural Requirements
Following [Code Maintenance Standards](../../../maintenance/README.md):
1. **Protocol-based design** (per ARCHITECTURAL_PATTERNS.md)
2. **Clean error hierarchy** (per ERROR_HANDLING.md)
3. **No backwards compatibility** - break freely for clean design
4. **Test-driven development** - tests define behavior
5. **Fail-fast philosophy** - clear, deterministic failures

## Implementation Strategy

### Day 1: Fix Immediate Issues and Define Architecture

#### Morning: Emergency Fixes
```python
# 1. Fix OutputConfig.from_cli_args() to handle notebook properly
# constants.py
DEFAULT_FORMATS = [FORMAT_MARKDOWN, FORMAT_JSON, FORMAT_NOTEBOOK]  # Add notebook

# 2. Fix BuildModule._should_generate_notebook()
def _should_generate_notebook(self):
    if hasattr(self.module_flags, 'save') and self.module_flags.save is not None:
        if isinstance(self.module_flags.save, list):
            # Empty list means all formats (including notebook)
            if len(self.module_flags.save) == 0:
                return True
            return 'jupyter' in self.module_flags.save or 'notebook' in self.module_flags.save
    return False

# 3. Update test to match intended behavior
def test_from_cli_args_save_flag_includes_jupyter(self):
    """Test --save jupyter is included in enabled formats."""
    args = Mock()
    args.save = ['markdown', 'jupyter', 'json']
    
    config = OutputConfig.from_cli_args(args)
    
    self.assertTrue(config.save_output)
    self.assertEqual(config.enabled_formats, {FORMAT_MARKDOWN, FORMAT_JSON, FORMAT_NOTEBOOK})
```

#### Afternoon: Define Unified Architecture
```python
# output/protocols.py - Define clear contracts
from typing import Protocol, Dict, Any, Optional

class IOutputStrategy(Protocol):
    """Protocol for output generation strategies."""
    
    def can_generate(self, format_name: str) -> bool:
        """Check if this strategy handles the given format."""
        ...
    
    def generate(self, data: Dict[str, Any], output_path: str) -> None:
        """Generate output to the specified path."""
        ...
    
    def get_file_extension(self) -> str:
        """Return the file extension for this format."""
        ...

class IOutputPipeline(Protocol):
    """Protocol for unified output pipeline."""
    
    def register_strategy(self, format_name: str, strategy: IOutputStrategy) -> None:
        """Register a strategy for a format."""
        ...
    
    def generate_outputs(self, data: Dict[str, Any], config: OutputConfig) -> None:
        """Generate all configured outputs."""
        ...
```

### Day 2: Create NotebookStrategy

#### Create Unified Notebook Strategy
```python
# output/strategies/notebook_strategy.py
from typing import Dict, Any
from ..protocols import IOutputStrategy
from ..notebook.streaming_generator import StreamingNotebookGenerator

class NotebookStrategy:
    """Strategy for generating Jupyter notebooks through unified pipeline."""
    
    def __init__(self):
        self.generator = StreamingNotebookGenerator()
    
    def can_generate(self, format_name: str) -> bool:
        """Check if this handles notebook format."""
        return format_name in ('notebook', 'jupyter')
    
    def generate(self, data: Dict[str, Any], output_path: str) -> None:
        """Generate notebook using streaming approach."""
        # Extract what notebook generation needs
        module_vars = data.get('module_vars', {})
        source_path = data.get('source_path', '')
        
        # Use existing streaming generator
        self.generator.generate_notebook_stream(
            module_vars=module_vars,
            source_path=source_path,
            output_path=output_path
        )
    
    def get_file_extension(self) -> str:
        """Return notebook extension."""
        return 'ipynb'
```

### Day 3: Unify Output Pipeline

#### Update OutputManager for Strategy Pattern
```python
# output/manager.py
class OutputManager:
    """Unified output manager using strategy pattern."""
    
    def __init__(self, config: OutputConfig):
        self.config = config
        self.strategies: Dict[str, IOutputStrategy] = {}
        self._register_default_strategies()
    
    def _register_default_strategies(self):
        """Register built-in output strategies."""
        # Existing strategies
        self.register_strategy(FORMAT_MARKDOWN, MarkdownStrategy())
        self.register_strategy(FORMAT_JSON, JsonStrategy())
        
        # NEW: Unified notebook strategy
        self.register_strategy(FORMAT_NOTEBOOK, NotebookStrategy())
    
    def register_strategy(self, format_name: str, strategy: IOutputStrategy):
        """Register an output strategy."""
        self.strategies[format_name] = strategy
    
    def generate_all_outputs(self, data: Dict[str, Any]):
        """Generate all configured output formats."""
        for format_name in self.config.enabled_formats:
            if format_name not in self.strategies:
                raise ValueError(f"No strategy registered for format: {format_name}")
            
            strategy = self.strategies[format_name]
            output_path = self._get_output_path(format_name, strategy)
            
            try:
                strategy.generate(data, output_path)
                print(f"Generated {format_name}: {output_path}")
            except Exception as e:
                # Follow fail-fast philosophy with helpful errors
                raise OutputGenerationError(
                    f"Failed to generate {format_name} output",
                    format_name=format_name,
                    output_path=output_path,
                    error=str(e)
                )
```

### Day 4: Remove Direct Notebook Generation

#### Clean up BuildModule
```python
# builder/module.py - Remove direct notebook handling
class BuildModule:
    def __init__(self, module_flags):
        # ... existing init ...
        # REMOVE: self.generate_notebook check
        # REMOVE: generate_notebook_if_requested method
        
        # Just use OutputManager for everything
        self._initialize_output_management()
    
    def process_all_outputs(self):
        """Process all outputs through unified pipeline."""
        # Prepare data for all strategies
        output_data = {
            'module_vars': self.module_variables,
            'source_path': self.module_path,
            'examples': self.processed_examples,
            'models': self.collected_models
        }
        
        # Let OutputManager handle all formats
        self.output_manager.generate_all_outputs(output_data)
```

#### Update __main__.py
```python
# __main__.py - Remove separate notebook generation
def main():
    # ... parse arguments ...
    
    module = BuildModule(module_flags)
    
    # REMOVE: module.generate_notebook_if_requested()
    
    # Run examples
    module.process_examples()
    
    # Generate ALL outputs through unified pipeline
    if module.save_output:
        module.process_all_outputs()
```

### Day 5: Enhanced Error Handling

#### Create Error Hierarchy
```python
# output/errors.py
from typing import Optional, Dict, Any

class OutputError(Exception):
    """Base exception for output package errors."""
    
    def __init__(self, message: str, context: Optional[Dict[str, Any]] = None):
        super().__init__(message)
        self.context = context or {}

class OutputGenerationError(OutputError):
    """Raised when output generation fails."""
    
    def __init__(self, message: str, format_name: str = None, 
                 output_path: str = None, error: str = None):
        formatted_message = message
        if format_name:
            formatted_message += f"\nFormat: {format_name}"
        if output_path:
            formatted_message += f"\nOutput path: {output_path}"
        if error:
            formatted_message += f"\nError details: {error}"
        
        super().__init__(formatted_message, {
            'format_name': format_name,
            'output_path': output_path,
            'error': error
        })

class StrategyNotFoundError(OutputError):
    """Raised when no strategy is registered for a format."""
    pass

class OutputConfigError(OutputError):
    """Raised for configuration issues."""
    pass
```

### Day 6: Testing and Validation

#### Update All Tests
```python
# tests/unit/test_config.py
def test_from_cli_args_save_flag_includes_all_formats(self):
    """Test --save includes all formats including notebook."""
    args = Mock()
    args.save = []  # Empty means all
    
    config = OutputConfig.from_cli_args(args)
    
    self.assertTrue(config.save_output)
    self.assertEqual(
        config.enabled_formats, 
        {FORMAT_MARKDOWN, FORMAT_JSON, FORMAT_NOTEBOOK}
    )

def test_from_cli_args_save_specific_formats(self):
    """Test --save with specific formats."""
    args = Mock()
    args.save = ['markdown', 'jupyter']
    
    config = OutputConfig.from_cli_args(args)
    
    self.assertTrue(config.save_output)
    self.assertEqual(
        config.enabled_formats,
        {FORMAT_MARKDOWN, FORMAT_NOTEBOOK}
    )

# tests/integration/test_unified_pipeline.py
class TestUnifiedPipeline(unittest.TestCase):
    """Test unified output generation pipeline."""
    
    def test_all_formats_generated_with_save(self):
        """Test --save generates all formats."""
        # Mock CLI args
        args = Mock()
        args.save = []
        
        # Create manager with config
        config = OutputConfig.from_cli_args(args)
        manager = OutputManager(config)
        
        # Generate outputs
        data = create_test_data()
        manager.generate_all_outputs(data)
        
        # Verify all formats created
        self.assertTrue(Path('output_dir/EXAMPLES.md').exists())
        self.assertTrue(Path('output_dir/MODELS.json').exists())
        self.assertTrue(Path('output_dir/NOTEBOOK.ipynb').exists())
```

#### Run Comprehensive Testing
```bash
# Run all output package tests
./run_tests.py --package output

# Verify notebook generation
echo "a" | ./dev_cli.py counterfactual/examples.py --save
ls ../output_*/  # Should see EXAMPLES.md, MODELS.json, NOTEBOOK.ipynb

# Test specific formats
echo "a" | ./dev_cli.py examples.py --save markdown jupyter
ls ../output_*/  # Should see EXAMPLES.md, NOTEBOOK.ipynb (no JSON)
```

### Day 7: Documentation and Polish

#### Update Documentation
- Update output/README.md with unified architecture
- Document strategy pattern for future formats
- Add migration guide for dependent packages
- Update API documentation

#### Performance Validation
- Ensure no performance regression
- Memory usage should remain constant (streaming)
- File I/O should be efficient

## Success Metrics

### Required Outcomes
- ✅ All output package tests pass (259/259)
- ✅ `--save` generates markdown, json, and notebook
- ✅ `--save jupyter` generates only notebook
- ✅ Unified pipeline for all formats
- ✅ Clear error messages with context
- ✅ No duplicate code between pipelines

### Quality Indicators
- Single responsibility: OutputManager handles all generation
- Clean interfaces: Protocol-based strategies
- Extensible: Easy to add new formats
- Maintainable: No split architecture
- Tested: Comprehensive test coverage

## Migration Impact

### For Users
```bash
# Before (broken):
./dev_cli.py examples.py --save  # Missing notebook

# After (fixed):
./dev_cli.py examples.py --save  # All formats including notebook
```

### For Developers
```python
# Before: Split architecture
module.generate_notebook_if_requested()  # Direct call
output_manager.save_outputs()  # Separate pipeline

# After: Unified architecture
output_manager.generate_all_outputs(data)  # Everything
```

### For Future Formats
```python
# Easy to add new format
class PdfStrategy:
    def can_generate(self, format_name: str) -> bool:
        return format_name == 'pdf'
    
    def generate(self, data: Dict[str, Any], output_path: str) -> None:
        # PDF generation logic
        pass

# Register and it works with --save
manager.register_strategy('pdf', PdfStrategy())
DEFAULT_FORMATS.append('pdf')  # Automatically included in --save
```

## Risk Assessment

### Low Risk
- Clear solution from Research 043
- Existing streaming generator works
- Protocol pattern proven in builder/

### Medium Risk
- Breaking change to BuildModule
- Need to update dependent tests
- Documentation needs updates

### Mitigation
- Comprehensive testing at each step
- Feature branch for isolation
- Run full test suite frequently

## Definition of Done

- [ ] OutputConfig test updated and passing
- [ ] DEFAULT_FORMATS includes notebook
- [ ] NotebookStrategy implemented
- [ ] OutputManager uses strategy pattern
- [ ] BuildModule direct calls removed
- [ ] All 259 output tests passing
- [ ] Manual testing confirms all formats generated
- [ ] Documentation updated
- [ ] No performance regression
- [ ] Compliance score ≥ 95/100

## Conclusion

This plan fixes the critical output package issues by implementing a **unified, protocol-based architecture** for all output generation. Following Solution 3 from Research 043 and the maintenance standards, we create a clean, maintainable, and extensible system that ensures `--save` works as users expect while preparing for future format additions.

The investment in proper architecture will yield:
- **Immediate functionality** - --save works correctly
- **Clean design** - Single pipeline for all formats
- **Future extensibility** - Easy to add new formats
- **Better testing** - Unified approach easier to test
- **Reduced maintenance** - No duplicate code paths

---

**Related Documents:**
- [Research 043: Output Package and Notebook Generation Issues](../research/043_output_notebook_generation_issues.md)
- [Plan 080: Framework Complete Refactor Overview](080_framework_complete_refactor_overview.md)
- [Code Maintenance Standards](../../../maintenance/README.md)
- [Architectural Patterns](../../../maintenance/ARCHITECTURAL_PATTERNS.md)
- [Error Handling Standards](../../../maintenance/ERROR_HANDLING.md)