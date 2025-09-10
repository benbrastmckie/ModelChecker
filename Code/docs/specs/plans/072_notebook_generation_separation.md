# Plan 072: Complete Separation of Notebook Generation from Output Pipeline

## Status: COMPLETED ✅

## Problem Statement

The current notebook generation is tightly coupled with the JSON/markdown output pipeline in OutputManager. This creates unnecessary complexity and data flow through intermediate formats. The notebook generation should be completely independent, working directly from theory templates and the variables defined in examples.py.

### Current Issues

1. **Coupled Architecture**: Notebook generation happens in OutputManager.finalize() alongside JSON/markdown
2. **Data Pipeline Dependency**: Example data flows through the same pipeline as other outputs
3. **Unnecessary Complexity**: Data is transformed and passed through multiple layers
4. **JSON Serialization Issues**: Semantic theory objects cause serialization errors
5. **Mixed Concerns**: OutputManager handles both model output formats AND notebook generation

## Proposed Solution

Create a completely separate notebook generation system that:
1. Works directly with the loaded module's variables (semantic_theories, example_range)
2. Uses theory templates without any intermediate data transformation
3. Operates independently from the OutputManager's JSON/markdown pipeline
4. Is invoked separately when --save jupyter is specified

## Architecture Design

### Current Flow (PROBLEMATIC)
```
examples.py → BuildModule → OutputManager → NotebookGenerator
                ↓              ↓                ↓
         (loads module)  (passes data)    (uses template)
                ↓              ↓                ↓
         example_data    models_data      notebook output
                ↓              ↓
            (coupled)    (JSON layer)
```

### New Flow (CLEAN SEPARATION)
```
examples.py → BuildModule ──┬→ OutputManager → JSON/Markdown
                ↓           │      ↓
         (loads module)     │  (models only)
                ↓           │
         module vars        └→ NotebookGenerator
                ↓                    ↓
     semantic_theories,        (direct access)
     example_range                   ↓
                                template.generate()
                                     ↓
                                EXAMPLES.ipynb
```

## Implementation Plan

### Phase 1: Create Independent Notebook Generation Path

#### 1.1 Modify BuildModule Structure
```python
# In builder/module.py
class BuildModule:
    def __init__(self, module_flags):
        # ... existing initialization ...
        
        # Store module variables for direct access
        self.module_variables = {
            'semantic_theories': self.semantic_theories,
            'example_range': self.example_range,
            'general_settings': self.general_settings,
            # Any other relevant module-level variables
        }
        
        # Separate notebook generation flag
        self.generate_notebook = self._should_generate_notebook()
    
    def _should_generate_notebook(self):
        """Check if notebook generation is requested."""
        if hasattr(self.module_flags, 'save') and self.module_flags.save:
            if 'jupyter' in self.module_flags.save or len(self.module_flags.save) == 0:
                return True
        return False
    
    def generate_notebook_if_requested(self):
        """Generate notebook independently from output pipeline."""
        if not self.generate_notebook:
            return
            
        from model_checker.notebook import IndependentNotebookGenerator
        
        generator = IndependentNotebookGenerator()
        notebook_json = generator.generate_from_module_vars(
            self.module_variables,
            self.module_path
        )
        
        # Save directly to output directory
        if self.output_manager and self.output_manager.output_dir:
            notebook_path = os.path.join(self.output_manager.output_dir, 'EXAMPLES.ipynb')
            with open(notebook_path, 'w', encoding='utf-8') as f:
                f.write(notebook_json)
```

### Phase 2: Create Independent Notebook Generator

#### 2.1 New Notebook Package Structure
```
src/model_checker/notebook/
├── __init__.py
├── generator.py           # Independent generator
├── template_loader.py     # Template discovery and loading
└── templates/            # Move templates here
    ├── base.py
    ├── logos.py
    ├── exclusion.py
    └── imposition.py
```

#### 2.2 Independent Generator Implementation
```python
# src/model_checker/notebook/generator.py
class IndependentNotebookGenerator:
    """Generate notebooks directly from module variables.
    
    This generator works independently from the output pipeline,
    using only the module variables and theory templates.
    """
    
    def generate_from_module_vars(self, module_vars: Dict, source_path: str) -> str:
        """Generate notebook from module variables.
        
        Args:
            module_vars: Dictionary containing:
                - semantic_theories: dict of theory configurations
                - example_range: dict of example definitions
                - general_settings: optional settings dict
            source_path: Path to source file for metadata
            
        Returns:
            JSON string of complete notebook
        """
        # Extract components
        semantic_theories = module_vars.get('semantic_theories', {})
        example_range = module_vars.get('example_range', {})
        
        if not semantic_theories or not example_range:
            raise ValueError("Missing required module variables")
        
        # Get appropriate template
        template = self._get_template(semantic_theories)
        
        # Generate cells directly from module data
        cells = []
        
        # Title cell
        cells.append(self._create_title_cell(source_path))
        
        # Setup cell from template
        cells.append(template.create_setup_cell(semantic_theories, example_range))
        
        # Example cells
        for name, definition in example_range.items():
            cells.extend(template.create_example_cells(name, definition))
        
        # Create notebook structure
        return self._create_notebook_json(cells)
    
    def _get_template(self, semantic_theories: Dict):
        """Get the appropriate template based on semantic theory."""
        # Determine theory type from semantic class
        theory_name, theory_config = next(iter(semantic_theories.items()))
        semantics_class = theory_config.get('semantics')
        
        if not semantics_class:
            raise ValueError("No semantics class found in theory")
        
        # Import and instantiate appropriate template
        from model_checker.notebook.template_loader import TemplateLoader
        loader = TemplateLoader()
        return loader.get_template_for_class(semantics_class)
```

### Phase 3: Refactor Templates for Direct Generation

#### 3.1 Enhanced Template Base Class
```python
# src/model_checker/notebook/templates/base.py
class DirectNotebookTemplate:
    """Base template for direct notebook generation.
    
    Templates work directly with module variables without
    any intermediate data transformation.
    """
    
    def create_setup_cell(self, semantic_theories: Dict, example_range: Dict) -> Dict:
        """Create setup cell with imports and theory configuration.
        
        Args:
            semantic_theories: Raw semantic theories from module
            example_range: Raw example definitions from module
            
        Returns:
            Cell dictionary for Jupyter notebook
        """
        # Analyze what's needed based on examples
        operators_used = self._detect_operators(example_range)
        
        # Generate imports
        imports = self.get_required_imports(operators_used)
        
        # Generate theory setup
        setup_code = self.generate_theory_setup(semantic_theories, operators_used)
        
        return {
            'cell_type': 'code',
            'metadata': {},
            'source': imports + ['\n'] + setup_code,
            'outputs': [],
            'execution_count': None
        }
    
    def create_example_cells(self, name: str, definition: Union[List, Tuple]) -> List[Dict]:
        """Create cells for a single example.
        
        Args:
            name: Example name from example_range keys
            definition: Raw definition (premises, conclusions, settings)
            
        Returns:
            List of cell dictionaries
        """
        cells = []
        
        # Header cell
        cells.append(self._create_header_cell(name))
        
        # Code cell with example
        cells.append(self._create_example_code_cell(name, definition))
        
        # Result interpretation placeholder
        cells.append(self._create_interpretation_cell())
        
        return cells
    
    def _detect_operators(self, example_range: Dict) -> Set[str]:
        """Detect which operators are used in examples."""
        operators = set()
        
        for name, definition in example_range.items():
            # Extract premises and conclusions
            if isinstance(definition, (list, tuple)):
                premises = definition[0] if len(definition) > 0 else []
                conclusions = definition[1] if len(definition) > 1 else []
                
                # Scan formulas for operators
                for formula in premises + conclusions:
                    operators.update(self._extract_operators(formula))
        
        return operators
```

### Phase 4: Remove Notebook Generation from OutputManager

#### 4.1 Clean OutputManager
```python
# src/model_checker/output/manager.py
class OutputManager:
    """Manages output for model checking results.
    
    Responsible ONLY for JSON and Markdown output formats.
    Notebook generation is handled separately.
    """
    
    def __init__(self, save_output: bool, mode: str = 'batch', 
                 sequential_files: str = 'multiple',
                 interactive_manager=None,
                 config: Optional[OutputConfig] = None):
        """Initialize output manager.
        
        Note: source_filepath and example_data parameters removed.
        Notebook generation is no longer handled here.
        """
        self.save_output = save_output
        self.output_dir = None
        self.models_data = []
        self.interactive_manager = interactive_manager
        # Remove: self.source_filepath = source_filepath
        # Remove: self.example_data = example_data
        
        # ... rest of initialization ...
    
    def finalize(self):
        """Finalize output and save JSON/Markdown files only."""
        # Let strategy handle finalization
        if hasattr(self.strategy, 'finalize'):
            self.strategy.finalize(lambda name, outputs: self._finalize_outputs(name, outputs))
        
        # Create summary for interactive mode
        if self.mode == 'interactive':
            self._create_interactive_summary()
                
        # Save models JSON if JSON format is enabled
        if self.config.is_format_enabled(FORMAT_JSON):
            self._save_models_json()
        
        # REMOVED: Notebook generation
        # Notebooks are now generated separately in BuildModule
```

### Phase 5: Update CLI Flow

#### 5.1 Modify Main Execution
```python
# src/model_checker/__main__.py
def main():
    # ... existing setup ...
    
    module = BuildModule(module_flags)
    
    # ... existing model checking ...
    
    # Run examples through output pipeline (JSON/Markdown only)
    module.runner.run_examples()
    
    # Generate notebook independently if requested
    module.generate_notebook_if_requested()
    
    # ... rest of main ...
```

## Migration Strategy

### Step 1: Create New Structure (Non-Breaking)
1. Create new `notebook/` package with independent generator
2. Copy templates to new location (keep old ones temporarily)
3. Implement IndependentNotebookGenerator

### Step 2: Add Alternative Path
1. Add generate_notebook_if_requested() to BuildModule
2. Test with both paths working
3. Verify notebooks generate correctly

### Step 3: Remove Old Path
1. Remove notebook generation from OutputManager
2. Remove example_data parameter from OutputManager
3. Remove old template locations
4. Update all tests

### Step 4: Cleanup
1. Remove FORMAT_NOTEBOOK from output constants
2. Remove JupyterNotebookFormatter
3. Simplify OutputConfig
4. Update documentation

## Benefits

1. **Clean Separation**: Notebook generation is completely independent
2. **Direct Access**: Works directly with module variables
3. **No Intermediate Layers**: No JSON serialization or data transformation
4. **Simpler Architecture**: Each component has a single responsibility
5. **Easier Testing**: Can test notebook generation in isolation
6. **Better Maintainability**: Changes to output formats don't affect notebooks

## Testing Plan

### Unit Tests
```python
# tests/notebook/test_generator.py
def test_independent_generation():
    """Test notebook generation with mock module variables."""
    module_vars = {
        'semantic_theories': {...},
        'example_range': {...}
    }
    
    generator = IndependentNotebookGenerator()
    notebook_json = generator.generate_from_module_vars(module_vars, 'test.py')
    
    # Verify notebook structure
    notebook = json.loads(notebook_json)
    assert 'cells' in notebook
    assert len(notebook['cells']) > 0

def test_template_selection():
    """Test correct template is selected for each theory."""
    # Test for Logos, Exclusion, Imposition
    pass

def test_operator_detection():
    """Test operator detection from example formulas."""
    pass
```

### Integration Tests
```python
# tests/integration/test_notebook_generation.py
def test_full_notebook_generation():
    """Test complete flow from examples.py to notebook."""
    # Create test examples.py
    # Run with --save jupyter
    # Verify notebook created
    # Verify notebook is runnable
    pass

def test_notebook_json_separation():
    """Verify notebook generation doesn't affect JSON output."""
    # Run with --save (all formats)
    # Verify JSON doesn't contain semantic_theory
    # Verify notebook still generates correctly
    pass
```

## Success Criteria

1. Notebooks generate successfully for all theories
2. No data flows through JSON layer for notebooks
3. OutputManager only handles JSON/Markdown
4. All existing tests pass
5. New notebook package has >90% test coverage
6. Documentation updated to reflect new architecture

## Risk Mitigation

1. **Risk**: Breaking existing notebook generation
   - **Mitigation**: Keep both paths during migration
   - **Validation**: Test with all example files

2. **Risk**: Missing module variables
   - **Mitigation**: Comprehensive module variable collection
   - **Validation**: Unit tests for each theory type

3. **Risk**: Template compatibility
   - **Mitigation**: Careful template migration
   - **Validation**: Compare output before/after

## Timeline

- Phase 1-2: Create new structure (2 hours)
- Phase 3: Refactor templates (1 hour)  
- Phase 4: Remove old path (1 hour)
- Phase 5: Update CLI flow (30 minutes)
- Testing: Comprehensive testing (1 hour)
- Documentation: Update docs (30 minutes)

Total estimated time: 6 hours

## Related Files

### Files to Create
- `src/model_checker/notebook/` (new package)
- `tests/notebook/` (new test suite)

### Files to Modify
- `src/model_checker/builder/module.py`
- `src/model_checker/__main__.py`
- `src/model_checker/output/manager.py`
- `src/model_checker/output/config.py`

### Files to Remove (Eventually)
- `src/model_checker/output/notebook_generator.py`
- `src/model_checker/output/formatters/notebook.py`
- `src/model_checker/theory_lib/*/notebook_template.py` (after moving)