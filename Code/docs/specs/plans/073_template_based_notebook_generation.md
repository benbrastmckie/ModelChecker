# Plan 073: Template-Based Notebook Generation from Reference Notebooks

## Status: PLANNING

## Executive Summary

Current notebook generation produces inadequate output that lacks proper imports, theory setup, and runnable examples. This plan specifies a complete refactor to use actual Jupyter notebook templates in each theory's notebooks/ directory, with simple field substitution to insert examples from examples.py files.

## Problem Analysis

### Current State Issues

1. **Missing Essential Setup**: Generated notebooks lack proper imports and theory initialization
2. **Wrong Theory Detection**: Using generic Logos setup instead of theory-specific (e.g., counterfactual)
3. **No Template Reference**: Not using the existing well-structured notebooks as templates
4. **Poor Structure**: Missing section headers, explanations, and proper cell organization
5. **Not Runnable**: Generated notebooks won't execute due to missing imports/setup

### Comparison

#### Target (counterfactual_examples.ipynb)
- Full imports with proper theory setup
- Clear section headers and structure
- Detailed setup cell with operator registry
- Examples with context (but no descriptions)
- Runnable code that produces output

#### Current Output
- Minimal imports, wrong theory setup
- No section structure
- Generic setup missing required operators
- Bare examples without context
- Would fail to run due to missing counterfactual operators

## Solution Design

### Core Concept

Use streaming template generation with decomposed JSON templates. Each template contains setup, example patterns, and conclusion sections that are assembled efficiently without memory limitations.

### Template Structure

```
notebooks/
├── template.json           # Self-contained template sections
├── <theory>_examples.ipynb # Reference notebook
└── README.md               # Documentation
```

### Variable Example Strategy

The template handles any number of examples (2, 15, 50, etc.) using a marker-based insertion system:

1. **Template has Fixed Structure**:
   - Title and introduction
   - Single import/setup cell (shared by all examples)
   - Example insertion markers
   - Summary/conclusion

2. **Example Insertion Points**:
   - `{{EXAMPLES_START}}` marker - where examples begin
   - `{{EXAMPLES_END}}` marker - where examples end
   - System inserts all examples from example_range between these markers

3. **Shared Imports**: One setup cell provides imports for all examples
   - No matter if 2 or 50 examples, same imports work
   - Examples reference same theory variable (e.g., `cf_theory`)

### Template Notebook Format

The template.ipynb will be a complete, runnable notebook with:

1. **Title Cell** (Markdown)
   - Theory name placeholder: `{{THEORY_NAME}}`
   - Generation date placeholder: `{{DATE}}`
   - Overview text (stays same regardless of example count)

2. **Setup Cell** (Code)
   - Complete imports
   - Theory initialization  
   - Operator registry setup
   - Print statements for confirmation
   - **This cell is used by ALL examples**

3. **Example Section Start** (Markdown)
   ```markdown
   ## Examples
   
   {{EXAMPLES_START}}
   ```

4. **Example Insertion Area**
   - System generates 3 cells per example here
   - Could be 6 cells (2 examples) or 45 cells (15 examples)
   - All reference the same theory variable from setup

5. **Example Section End** (Markdown)  
   ```markdown
   {{EXAMPLES_END}}
   
   ## Summary
   [Theory-specific summary content]
   ```

### Example Cell Template

Each example generates three cells:

1. **Header Cell** (Markdown)
```markdown
## Example {{INDEX}}: {{EXAMPLE_NAME}}

### The Argument
```

2. **Code Cell** (Code)
```python
# {{EXAMPLE_NAME}}: {{EXAMPLE_TYPE}}
{{EXAMPLE_VAR}} = [
    {{PREMISES}},
    {{CONCLUSIONS}},
    {{SETTINGS}}
]

print("Running model checker...")
model = create_build_example('{{EXAMPLE_NAME}}', theory, {{EXAMPLE_VAR}})

# Display the result
if model.model_structure.z3_model:
    model.model_structure.print_to(
        model.settings,
        '{{EXAMPLE_NAME}}',
        '{{THEORY_DISPLAY_NAME}}',
        output=sys.stdout
    )
else:
    print("=" * 70)
    print("THEOREM VALIDATED: {{EXAMPLE_NAME}}")
    print("=" * 70)
    print("No countermodel found - the inference is VALID")
    print("=" * 70)
```

3. **Interpretation Cell** (Markdown)
```markdown
### Result Interpretation

[To be added after running the example]

---
```

## Implementation Architecture

### Directory Structure

```
src/model_checker/
├── notebook/                       # Streaming notebook generation
│   ├── __init__.py
│   ├── streaming_generator.py      # Main streaming generator
│   ├── template_loader.py          # Template decomposition loader
│   ├── notebook_writer.py          # Memory-efficient file writer
│   └── utils.py                    # Helper functions
│
└── theory_lib/
    ├── logos/
    │   └── subtheories/
    │       ├── counterfactual/
    │       │   └── notebooks/
    │       │       ├── template.json                    # Self-contained template sections
    │       │       ├── counterfactual_examples.ipynb   # Reference notebook
    │       │       └── README.md                        # Documentation
    │       ├── modal/
    │       │   └── notebooks/
    │       │       ├── template.json                    # Self-contained template
    │       │       ├── modal_examples.ipynb             # Reference notebook  
    │       │       └── README.md                        # Documentation
    │       └── relevance/
    │           └── notebooks/
    │               ├── template.json                    # Self-contained template
    │               ├── relevance_examples.ipynb         # Reference notebook
    │               └── README.md                        # Documentation
    ├── exclusion/
    │   └── notebooks/
    │       ├── template.json           # Self-contained template (standalone theory)
    │       ├── exclusion_examples.ipynb # Reference notebook
    │       └── README.md               # Documentation
    └── imposition/
        └── notebooks/
            ├── template.json           # Self-contained template (standalone theory)
            ├── imposition_examples.ipynb # Reference notebook
            └── README.md               # Documentation
```

### Self-Contained Template Design

Templates are completely self-contained with all necessary setup code embedded directly in their `setup_cells` section. Theory-specific information (theory names, display names, variable prefixes) is extracted directly from module variables and semantic theory classes during generation, eliminating the need for external configuration files.

### Template Information Extraction

The streaming generator extracts necessary information from:
- **Module variables**: `semantic_theories`, `example_range` from loaded examples.py
- **Theory classes**: Class names and module paths for theory identification  
- **Template content**: Setup code and example patterns defined within template.json
- **File structure**: Theory/subtheory detection from template file location

### Variable Example Generation Algorithm

```python
class TemplateBasedNotebookGenerator:
    def generate(self, examples_file_path: str, output_path: str):
        # 1. Load examples.py to get example_range
        module = load_module(examples_file_path)
        example_range = module.example_range
        
        print(f"Generating notebook with {len(example_range)} examples")
        
        # 2. Detect which template to use
        template_path = find_template_for_module(examples_file_path, module)
        
        if not template_path or not os.path.exists(template_path):
            # Report missing template with helpful message
            expected_path = get_expected_template_path(examples_file_path)
            raise FileNotFoundError(
                f"No template found for notebook generation.\n"
                f"Expected template at: {expected_path}\n"
                f"Please create a template notebook at this location.\n"
                f"You can copy and modify an existing reference notebook."
            )
        
        # 3. Load template notebook
        template_nb = load_notebook(template_path)
        
        # 4. Find insertion points for examples
        start_marker_index, end_marker_index = find_example_markers(template_nb)
        
        # 5. Generate cells for ALL examples in example_range
        example_cells = []
        for i, (name, definition) in enumerate(example_range.items(), 1):
            # Each example creates 3 cells (header, code, interpretation)
            cells = generate_example_cells(i, name, definition, len(example_range))
            example_cells.extend(cells)
        
        print(f"Generated {len(example_cells)} cells for {len(example_range)} examples")
        
        # 6. Insert ALL example cells between the markers
        output_nb = insert_cells_between_markers(
            template_nb, 
            start_marker_index, 
            end_marker_index, 
            example_cells
        )
        
        # 7. Update metadata and placeholders
        output_nb = substitute_template_placeholders(output_nb, {
            'THEORY_NAME': get_theory_display_name(module),
            'DATE': datetime.now().strftime('%Y-%m-%d'),
            'EXAMPLE_COUNT': str(len(example_range))
        })
        
        # 8. Save notebook
        save_notebook(output_nb, output_path)
        print(f"Notebook saved with {len(example_range)} runnable examples")

def generate_example_cells(index: int, name: str, definition: tuple, total_count: int) -> List[Dict]:
    """Generate the 3 cells for a single example.
    
    Args:
        index: Example number (1, 2, 3...)
        name: Example name (CF_CM_1, etc.)
        definition: (premises, conclusions, settings) tuple
        total_count: Total number of examples (for progress indication)
        
    Returns:
        List of 3 cell dictionaries
    """
    cells = []
    
    # 1. Header cell (markdown)
    cells.append({
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            f"## Example {index}: {name}\n",
            "\n",
            "### The Argument"
        ]
    })
    
    # 2. Code cell with example execution
    var_name = name.lower().replace('_', '_')
    code_lines = [
        f"# {name}: {get_example_type(name)}\n",
        f"{var_name} = [\n",
        format_premises(definition[0]) + "\n",
        format_conclusions(definition[1]) + "\n", 
        format_settings(definition[2] if len(definition) > 2 else {}) + "\n",
        "]\n",
        "\n",
        f"print(f'Running example {index}/{total_count}: {name}...')\n",
        f"model = create_build_example('{name}', theory, {var_name})\n",
        "\n",
        "# Display the result\n",
        "if model.model_structure.z3_model:\n",
        "    model.model_structure.print_to(\n",
        "        model.settings,\n",
        f"        '{name}',\n",
        "        theory['semantics'].__name__,\n",
        "        output=sys.stdout\n",
        "    )\n",
        "else:\n",
        "    print('=' * 70)\n",
        f"    print('THEOREM VALIDATED: {name}')\n",
        "    print('=' * 70)\n",
        "    print('No countermodel found - the inference is VALID')\n",
        "    print('=' * 70)\n"
    ]
    
    cells.append({
        "cell_type": "code",
        "metadata": {},
        "source": code_lines,
        "outputs": [],
        "execution_count": None
    })
    
    # 3. Interpretation cell (markdown)
    cells.append({
        "cell_type": "markdown", 
        "metadata": {},
        "source": [
            "### Result Interpretation\n",
            "\n",
            "[To be added after running the example]\n",
            "\n",
            "---"
        ]
    })
    
    return cells
```

### Template Discovery

The system finds templates based on the theory structure:

1. **For Theories with Subtheories** (e.g., logos):
   - Template must exist in: `theory_lib/logos/subtheories/<subtheory>/notebooks/template.ipynb`
   - Example: `counterfactual/notebooks/template.ipynb`
   - No template at logos level (handled by subtheories)

2. **For Theories without Subtheories** (e.g., exclusion, imposition):
   - Template must exist in: `theory_lib/<theory>/notebooks/template.ipynb`
   - Example: `exclusion/notebooks/template.ipynb`

3. **No Fallbacks**: If template not found, report error with expected location:
   ```
   Error: No template found for theory.
   Expected template at: theory_lib/exclusion/notebooks/template.ipynb
   Please create a template notebook at this location.
   ```

## Creating Templates

### Step 1: Copy Reference Notebook

Start with the existing reference notebook (e.g., counterfactual_examples.ipynb)

### Step 2: Remove Specific Examples

Keep:
- Title and overview
- All imports and setup
- Summary/conclusion

Remove:
- Specific example cells
- Example-specific descriptions

### Step 3: Add Markers

Insert placeholder markers where examples should go:
```python
# Cell with marker comment
# {{EXAMPLES_START}}
# Examples will be inserted here
# {{EXAMPLES_END}}
```

### Step 4: Embed Setup Code

All theory-specific setup code is embedded directly in the template.json setup_cells section

### Memory-Efficient Writer Implementation

```python
class NotebookWriter:
    """Memory-efficient notebook writer that streams JSON directly to file."""
    
    def __init__(self, output_path: str):
        self.output_path = output_path
        self.cell_count = 0
        self.file = None
        
    def __enter__(self):
        self.file = open(self.output_path, 'w', encoding='utf-8')
        self._write_notebook_header()
        return self
        
    def write_cell(self, cell: Dict):
        """Write a single cell to the notebook JSON stream."""
        if self.cell_count > 0:
            self.file.write(',\\n')
        json.dump(cell, self.file, indent=1, ensure_ascii=False)
        self.cell_count += 1
        
    def __exit__(self, *args):
        self._write_notebook_footer()
        self.file.close()
        
    def _write_notebook_header(self):
        """Write the opening JSON structure."""
        header = {
            "cells": "[",  # Opening bracket for cells array
            "metadata": {},
            "nbformat": 4,
            "nbformat_minor": 4
        }
        # Write partial JSON structure
        self.file.write('{\\n "cells": [\\n')
        
    def _write_notebook_footer(self):
        """Write the closing JSON structure."""
        self.file.write('\\n ],\\n')
        self.file.write(' "metadata": {},\\n')
        self.file.write(' "nbformat": 4,\\n')
        self.file.write(' "nbformat_minor": 4\\n')
        self.file.write('}\\n')
```

### Streaming Performance Characteristics

#### Memory Usage Comparison

| Example Count | Marker-Based Memory | Streaming Memory | Memory Savings |
|---------------|--------------------|--------------------|----------------|
| 2 examples    | ~50KB              | ~5KB              | 90%            |
| 15 examples   | ~400KB             | ~5KB              | 98.7%          |
| 50 examples   | ~1.5MB             | ~5KB              | 99.7%          |
| 200 examples  | ~6MB               | ~5KB              | 99.9%          |

#### Processing Time

- **Constant time per example**: O(1) processing regardless of total count
- **No memory allocation spikes**: Steady, predictable resource usage
- **Immediate output**: Results written as soon as generated

### Simple User Experience

**Generated notebook structure is clean and user-friendly:**

1. **Setup Section**: Complete imports and theory configuration
2. **Per Example**: Header + runnable code + interpretation placeholder
3. **Conclusion Section**: Summary header + final evaluation placeholder

**User workflow:**
1. Run generated notebook to see model checking results
2. Add interpretations in the provided markdown cells
3. Add final evaluation in conclusion section
4. Notebook serves as complete documentation of the theory exploration

## Implementation Phases

### Phase 1: Create Template Infrastructure

1. Create notebook_v2 package
2. Implement notebook loading/saving utilities
3. Create template processor for marker substitution
4. Build example cell generator

### Phase 2: Create Theory Templates

1. **Counterfactual Template** (subtheory of logos)
   - Location: `theory_lib/logos/subtheories/counterfactual/notebooks/template.json`
   - Decompose counterfactual_examples.ipynb into sections
   - Embed all setup code in setup_cells
   - Create example_template pattern
   - Self-contained design

2. **Other Logos Subtheories**  
   - Each needs its own template.json in its notebooks/ directory
   - Modal: `theory_lib/logos/subtheories/modal/notebooks/template.json`
   - Relevance: `theory_lib/logos/subtheories/relevance/notebooks/template.json`
   - Consistent 3-file structure for all

3. **Exclusion Template** (standalone theory)
   - Location: `theory_lib/exclusion/notebooks/template.json`
   - Decompose exclusion theory setup
   - Embed witness semantics imports
   - Self-contained theory initialization

4. **Imposition Template** (standalone theory)
   - Location: `theory_lib/imposition/notebooks/template.json`
   - Embed imposition-specific imports
   - Self-contained theory setup

### Phase 3: Implement Generator

1. Module loader (reuse existing)
2. Template discovery logic
3. Cell generation from examples
4. Notebook assembly
5. CLI integration

### Phase 4: Testing

1. Test with counterfactual examples
2. Test with exclusion examples
3. Test with imposition examples
4. Verify notebooks are runnable
5. Compare output with reference notebooks

## File Structure Requirements

### Required Files

**For Theories without Subtheories** (exclusion, imposition):
```
theory_lib/<theory>/notebooks/
├── template.json           # REQUIRED: Self-contained template sections
├── <theory>_examples.ipynb # Reference notebook
└── README.md               # Documentation
```

**For Theories with Subtheories** (logos):
```
theory_lib/<theory>/subtheories/<subtheory>/notebooks/
├── template.json           # REQUIRED: Self-contained template sections
├── <subtheory>_examples.ipynb # Reference notebook
└── README.md               # Documentation
```

**Note**: No template is needed at the parent theory level (e.g., theory_lib/logos/notebooks/) as each subtheory handles its own templates.

### Template Notebook Structure

```json
{
  "cells": [
    {
      "cell_type": "markdown",
      "source": ["# {{THEORY_NAME}} Examples\n", "..."]
    },
    {
      "cell_type": "code", 
      "source": ["import sys\n", "..."],
      "metadata": {"tags": ["setup"]}
    },
    {
      "cell_type": "markdown",
      "source": ["## Examples\n", "{{EXAMPLES_START}}"]
    },
    {
      "cell_type": "markdown",
      "source": ["{{EXAMPLES_END}}\n", "## Summary"]
    }
  ]
}
```

## Success Criteria

1. **Runnable Notebooks**: All generated notebooks execute without errors
2. **Proper Theory Setup**: Correct imports and theory initialization for each type
3. **Example Fidelity**: Examples transferred accurately with proper escaping
4. **Structure Match**: Output structure matches reference notebooks
5. **No Model Output**: Templates don't include pre-computed results
6. **Field Substitution Only**: Simple template field replacement, no complex logic

## Benefits

1. **Simplicity**: Templates are just notebooks with markers
2. **Maintainability**: Theory experts can update templates directly
3. **Consistency**: All notebooks follow theory-specific patterns
4. **Flexibility**: Each theory/subtheory can have custom templates
5. **Reliability**: No complex code generation or AST manipulation

## Migration Path

1. Keep existing notebook generation as fallback
2. Implement new system in parallel
3. Gradually create templates for each theory
4. Switch over once all templates exist
5. Remove old generation code

## Testing Strategy

### Unit Tests

```python
def test_template_loading():
    """Test loading notebook templates."""
    template = load_template("path/to/template.ipynb")
    assert template is not None
    assert find_marker(template, "{{EXAMPLES_START}}")

def test_example_cell_generation():
    """Test generating cells from example definition."""
    cells = generate_example_cells("CF_CM_1", example_def)
    assert len(cells) == 3  # header, code, interpretation
    assert cells[0]["cell_type"] == "markdown"
    assert cells[1]["cell_type"] == "code"

def test_template_substitution():
    """Test substituting examples into template."""
    output = substitute_examples(template, examples)
    assert "CF_CM_1" in output
```

### Integration Tests

```python
def test_full_generation():
    """Test complete notebook generation."""
    generate_notebook("examples.py", "output.ipynb")
    
    # Load and validate
    nb = load_notebook("output.ipynb")
    assert nb is not None
    
    # Check it's runnable
    exec_results = execute_notebook(nb)
    assert all(r.success for r in exec_results)
```

## Maintenance Standards Compliance

Per Code/maintenance/README.md:

1. **No Emojis**: No emojis in code or documentation
2. **Unicode Math**: Use verified Unicode for logical operators
3. **UTF-8 Encoding**: All files use UTF-8 without BOM
4. **No Decorators**: Avoid decorators without good reason
5. **Break Compatibility**: No backward compatibility layers
6. **Test-Driven**: Write tests before implementation
7. **Documentation**: Comprehensive README in each directory

## Related Specifications

- Plan 071: Initial notebook generation fix
- Plan 072: Separation from output pipeline
- This plan (073): Complete template-based refactor

## Conclusion

This plan provides a complete refactor of notebook generation to use actual notebook templates with simple field substitution. The approach is simpler, more maintainable, and produces notebooks that match the quality and structure of hand-crafted reference notebooks.