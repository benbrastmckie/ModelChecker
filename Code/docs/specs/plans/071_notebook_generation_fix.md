# Plan 071: Template-Based Notebook Generation

## Status: COMPLETED ✅ - Template-Based Approach Implemented

## Core Strategy

Generate Jupyter notebooks using theory-specific templates that provide all imports and setup code, with the framework only inserting the actual example data at runtime.

## Key Principles

1. **Theory-Owned Templates**: Each theory/subtheory provides a complete notebook template
2. **Data Flow Through Pipeline**: Example data flows through normal execution pipeline
3. **Theory-Agnostic Output**: The output/ directory has no theory-specific logic
4. **No Module Reloading**: Never try to reload examples.py files
5. **Portable Design**: No absolute paths, all relative to framework structure

## Core Requirement

When user runs `--save jupyter` or `--save` (all formats), generate a Jupyter notebook that:
1. Contains the EXACT examples from examples.py with their actual formulas
2. Includes all necessary imports to run those examples
3. Follows the style of counterfactual_examples.ipynb
4. Has minimal headers (users add explanations after running)
5. Is immediately runnable to generate the countermodels

**NO separate --notebook flag** - this functionality is part of --save jupyter

## Current Problems

### Critical Issue: Module Import Failures
Attempting to reload examples.py files fails because:
1. Relative imports don't work when loading modules directly
2. Path manipulation creates portability issues
3. AST parsing is too fragile for real-world code

### Root Cause
The current approach tries to re-extract data from source files instead of using the data that's already flowing through the execution pipeline.

## Solution: Template-Based Generation

### Architecture

```
examples.py → BuildModule → Runner → OutputManager → NotebookGenerator
                 ↓                        ↓              ↓
         (loads examples)         (passes data)    (uses template)
                                                         ↓
                                               NotebookTemplate.get_notebook()
                                                         ↓
                                                  EXAMPLES.ipynb
```

### Approach
When --save includes jupyter format:
1. BuildModule loads examples.py normally (handling all imports)
2. Runner passes example data to OutputManager
3. OutputManager stores actual example definitions (not just results)
4. NotebookGenerator asks theory's NotebookTemplate for complete notebook structure
5. Template provides full notebook with placeholders for examples
6. Generator inserts actual example data and saves

### Key Design Decisions

1. **No --notebook flag**: Use `--save jupyter` instead
2. **Template-driven**: Each theory provides complete notebook structure
3. **Data pipeline**: Example data flows through normal execution
4. **No file reloading**: Never reload examples.py after initial load
5. **Theory agnostic**: output/ directory has no theory-specific code

## Implementation Plan

### Phase 1: Data Flow Enhancement

Modify BuildModule to pass example definitions through:
```python
# In builder/module.py Runner.run_examples()
for example_name in self.example_range:
    example_def = self.examples[example_name]
    # Pass the raw definition along with results
    model_data = {
        'example_name': example_name,
        'example_def': example_def,  # (premises, conclusions, settings)
        'semantic_theory': self.semantic_theory,
        # ... rest of model data
    }
    self.output_manager.add_model(model_data)
```

### Phase 2: Template Enhancement

Extend NotebookTemplate to provide complete notebook:
```python
# In theory_lib/base_template.py
class NotebookTemplate:
    def get_notebook_structure(self) -> Dict:
        """Return complete notebook structure.
        
        Returns:
            Dict with:
            - 'cells': List of cell definitions
            - 'metadata': Notebook metadata
        """
        return {
            'cells': [
                self._title_cell(),
                self._setup_cell(),
                # Placeholder marker for examples
                {'type': 'examples_placeholder'}
            ],
            'metadata': self._notebook_metadata()
        }
    
    def format_example_cells(self, example_data: Dict) -> List[Dict]:
        """Format an example into notebook cells.
        
        Args:
            example_data: Contains example_name, premises, conclusions, settings
            
        Returns:
            List of cell dictionaries (markdown headers, code cells, etc.)
        """
        cells = []
        # Add section header
        cells.append(self._markdown_cell(f"## {example_data['example_name']}"))
        # Add code cell with example
        cells.append(self._code_cell(self.format_example(example_data)))
        return cells
```

### Phase 3: NotebookGenerator Refactor

Simplify NotebookGenerator to use templates and data:
```python
class NotebookGenerator:
    def generate_notebook(self, examples_data: List[Dict], 
                         semantic_theory: Dict) -> str:
        """Generate notebook from example data.
        
        Args:
            examples_data: List of example definitions with formulas
            semantic_theory: The semantic theory dictionary
            
        Returns:
            JSON string of complete notebook
        """
        # Get template from semantic theory
        template = self._get_template(semantic_theory)
        
        # Get base notebook structure from template
        notebook = template.get_notebook_structure()
        
        # Find placeholder and replace with example cells
        cells = []
        for cell in notebook['cells']:
            if cell.get('type') == 'examples_placeholder':
                # Insert all example cells here
                for example_data in examples_data:
                    cells.extend(template.format_example_cells(example_data))
            else:
                cells.append(cell)
        
        notebook['cells'] = cells
        return json.dumps(notebook, indent=2)
```

### Phase 4: OutputManager Integration

OutputManager collects and passes example data:
```python
class OutputManager:
    def __init__(self, config, semantic_theory=None):
        self.config = config
        self.semantic_theory = semantic_theory
        self.examples_data = []  # Collect example definitions
        
    def add_model(self, model_data):
        # Store example definition for notebook generation
        if 'example_def' in model_data:
            self.examples_data.append({
                'example_name': model_data['example_name'],
                'premises': model_data['example_def'][0],
                'conclusions': model_data['example_def'][1],
                'settings': model_data['example_def'][2] if len(model_data['example_def']) > 2 else {}
            })
        # ... rest of method
    
    def _generate_notebook(self):
        """Generate notebook from collected data."""
        from model_checker.output.notebook_generator import NotebookGenerator
        
        generator = NotebookGenerator()
        notebook_json = generator.generate_notebook(
            self.examples_data,
            self.semantic_theory
        )
        
        notebook_path = os.path.join(self.output_dir, 'EXAMPLES.ipynb')
        with open(notebook_path, 'w', encoding='utf-8') as f:
            f.write(notebook_json)
```

### Phase 5: Template Examples

Each theory provides a template in its notebooks/ directory:

**logos/notebooks/notebook_template.json**:
```json
{
  "title": "Logos Hyperintensional Logic Examples",
  "imports": [
    "import sys",
    "from model_checker.jupyter import create_build_example",
    "from model_checker.theory_lib.logos.semantic import LogosSemantics"
  ],
  "setup_code": "theory = {...}",
  "example_format": "standard"
}
```

Or use the existing Python template classes:
```python
# logos/notebook_template.py
class LogosNotebookTemplate(NotebookTemplate):
    def _setup_cell(self):
        return {
            'cell_type': 'code',
            'source': self.get_imports() + ['\n'] + self.get_theory_setup()
        }
```

3. **For Each Example**:

   a. **Header** (Markdown):
   ```markdown
   ## Example N: [Example Name]
   
   ### The Argument
   ```
   
   b. **Code Cell**:
   ```python
   # [Example Name]: [Test for countermodel/theorem]
   example_name = [
       [  # Premises
           '\\neg A',
           '(A \\boxright C)',
       ],
       [  # Conclusions
           '((A \\wedge B) \\boxright C)',
       ],
       {
           'N': 4,  # Number of atomic states
           'contingent': True,  # Force contingent propositions
           # ... other settings with comments
       }
   ]
   
   print('Running model checker...')
   model = create_build_example('[Example Name]', theory, example_name)
   
   # Display the result
   if model.model_structure.z3_model:
       model.model_structure.print_to(
           model.settings,
           '[Example Name]',
           '[Theory Display Name]',
           output=sys.stdout
       )
   else:
       print('=' * 70)
       print('THEOREM VALIDATED: [Example Name]')
       print('=' * 70)
       print('No countermodel found - the inference is VALID')
       print('=' * 70)
   ```
   
   c. **Interpretation Placeholder** (Markdown):
   ```markdown
   ### Result Interpretation
   
   [To be added after running the example]
   ```

## Testing Strategy

### Manual Testing Checklist

1. **Counterfactual Examples**:
```bash
./Code/dev_cli.py .../counterfactual/examples.py --save jupyter
# Check: Notebook has actual formulas from CF_CM_1, CF_TH_1, etc.
# Check: Operators properly escaped (\\boxright becomes \\\\boxright)
# Check: Settings have helpful comments
```

2. **Exclusion Examples**:
```bash
./Code/dev_cli.py .../exclusion/examples.py --save jupyter
# Check: Uses ExclusionNotebookTemplate
# Check: Witness predicates formatted correctly
```

3. **All Formats**:
```bash
./Code/dev_cli.py examples.py --save
# Check: Generates EXAMPLES.md, MODELS.json, EXAMPLES.ipynb
# Check: Notebook has actual formulas, not empty lists
```

### Validation Criteria

1. **Formulas Present**: Actual premises/conclusions from examples.py
2. **Proper Escaping**: LaTeX operators correctly escaped for Python strings
3. **Runnable**: Notebook executes without errors in Jupyter
4. **Correct Detection**: CM_ examples show "Test for countermodel"
5. **No --notebook flag**: Only --save jupyter or --save

## Success Metrics

The implementation succeeds when:

1. `--save jupyter` generates a notebook with:
   - Actual formulas from examples.py
   - Proper imports and theory setup
   - Runnable code cells
   - Minimal headers

2. `--save` (all formats) generates:
   - EXAMPLES.md with countermodel results
   - MODELS.json with countermodel data  
   - EXAMPLES.ipynb with runnable examples

3. NO --notebook flag exists (removed completely)

4. Example detection correctly identifies:
   - 'CM_' patterns as countermodel tests
   - 'TH_' patterns as theorem validity tests

## Files to Modify

### Core Framework
- `src/model_checker/builder/module.py` - Pass example definitions through pipeline
- `src/model_checker/output/manager.py` - Collect and pass example data
- `src/model_checker/output/notebook_generator.py` - Use templates, not file loading

### Template Base
- `src/model_checker/theory_lib/base_template.py` - Add complete notebook methods

### Theory Templates
- `src/model_checker/theory_lib/logos/notebook_template.py` - Implement full structure
- `src/model_checker/theory_lib/exclusion/notebook_template.py` - Implement full structure
- `src/model_checker/theory_lib/imposition/notebook_template.py` - Implement full structure
- `src/model_checker/theory_lib/bimodal/notebook_template.py` - Create if needed

## Current Status

### Completed ✅
- ✓ Removed --notebook flag 
- ✓ Fixed CM_/TH_ detection to use underscore patterns
- ✓ Refactored to template-based approach
- ✓ Eliminated module reloading
- ✓ Modified BuildModule to pass example definitions through pipeline
- ✓ Updated OutputManager to receive and use example data
- ✓ Added generate_from_data method to NotebookGenerator
- ✓ Enhanced NotebookTemplate base class with proper formatting
- ✓ All theory templates working (Logos, Exclusion, Imposition)
- ✓ Tested with all theory types - notebooks generate successfully

### Implementation Details
1. BuildModule now passes example_data dictionary to OutputManager
2. OutputManager uses example_data instead of reloading files
3. NotebookGenerator has new generate_from_data method
4. No more relative import errors
5. Notebooks contain actual formulas with proper escaping

## Benefits of New Approach

1. **Portability**: No absolute paths or complex import handling
2. **Reliability**: Data flows through normal pipeline, no reloading
3. **Flexibility**: Each theory controls its notebook format completely
4. **Maintainability**: Theory-agnostic output directory
5. **Simplicity**: Templates provide structure, framework just inserts data