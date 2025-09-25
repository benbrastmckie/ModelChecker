# Output Formats and Saving Guide

[← Back to Usage](README.md) | [Workflow →](WORKFLOW.md) | [Examples →](EXAMPLES.md)

## Table of Contents

1. [Overview](#overview)
2. [Output Formats](#output-formats)
   - [Terminal Output](#terminal-output)
   - [JSON Format](#json-format)
   - [Markdown Format](#markdown-format)
   - [Jupyter Notebook Format](#jupyter-notebook-format)
3. [Saving Output](#saving-output)
   - [Command-line Options](#command-line-options)
   - [Interactive Save Mode](#interactive-save-mode)
   - [Batch Saving](#batch-saving)
4. [Output Directory Structure](#output-directory-structure)
5. [Format Selection Guide](#format-selection-guide)
6. [Practical Examples](#practical-examples)
7. [Troubleshooting](#troubleshooting)

## Overview

The ModelChecker provides flexible output options to suit different workflows, from quick terminal checks to comprehensive documentation generation. Output can be displayed in the terminal or saved in multiple formats for further analysis, reporting, or interactive exploration.

**Architecture Context**: For the complete output generation system design, see [Output Architecture](../architecture/OUTPUT.md). For how outputs fit into the overall pipeline, see [Pipeline Architecture](../architecture/PIPELINE.md).

## Output Formats

### Terminal Output

Default output displayed in the console with color-coding and formatting:

```bash
# Basic terminal output
model-checker examples/test.py

# Standard output
model-checker examples/test.py
```

**Terminal Output Features**:
- Color-coded results (VALID/INVALID indicators)
- Formatted model displays with truth tables
- Progress indicators for long-running operations
- Inline countermodel presentation

### JSON Format

Machine-readable format for programmatic processing:

```bash
# Save as JSON
model-checker examples/test.py --save json
```

**JSON Structure**:
```json
{
  "example": "MODUS_PONENS",
  "theory": "logos",
  "has_model": false,
  "evaluation_world": "w0",
  "states": [
    {"state": "s0", "possible": true, "world": true}
  ],
  "relations": {
    "part_of": [["s0", "s1"]],
    "fusion": [["s0", "s1", "s2"]]
  },
  "propositions": {
    "A": {"verifiers": ["s0"], "falsifiers": []},
    "B": {"verifiers": ["s1"], "falsifiers": []}
  },
  "output": "Example MODUS_PONENS: there is no countermodel"
}
```

**Use Cases**:
- Automated testing and CI/CD pipelines
- Data analysis and visualization
- Integration with other tools
- Archival and version control

### Markdown Format

Human-readable documentation format:

```bash
# Save as Markdown
model-checker examples/test.py --save markdown
```

**Markdown Output Example**:
```markdown
# Example: MODUS_PONENS

## Settings
- Theory: logos
- N: 3
- Max Time: 30s

## Premises
1. A
2. A → B

## Conclusions
1. B

## Result: VALID

The inference is valid. No countermodel exists.
```

**Use Cases**:
- Documentation and reports
- GitHub/GitLab integration
- Academic papers and presentations
- Team communication

### Jupyter Notebook Format

Interactive notebook for exploration and teaching:

```bash
# Generate Jupyter notebook
model-checker examples/test.py --save notebook
```

**Notebook Features**:
- Re-runnable code cells

**Architecture Reference**: For the complete Jupyter integration design, see [Jupyter Architecture](../architecture/JUPYTER.md).
- Inline explanations and markdown
- Interactive model exploration
- Visualization capabilities

**Generated Notebook Structure**:
1. Setup and imports
2. Theory configuration
3. Example definitions
4. Execution and results
5. Analysis and exploration cells

## Saving Output

### Command-line Options

```bash
# Core save options
--save                    # Interactive mode - prompts for format
--save json              # Save as JSON
--save markdown          # Save as Markdown
--save notebook          # Generate Jupyter notebook
--save all               # Save in all formats

# Additional options
--output-dir=<path>      # Custom output directory (default: output/)
--no-terminal           # Suppress terminal output when saving
--overwrite            # Overwrite existing files without prompting
```

### Interactive Save Mode

The **Interactive Save Mode** provides fine-grained control over which model checking results are saved, allowing users to selectively save models and iterate through additional solutions interactively.

#### Enabling Interactive Mode

```bash
# Sequential save mode - prompts after each model
model-checker --save --sequential examples/my_logic.py
model-checker --save -q examples/my_logic.py  # Short form

# Save specific formats sequentially
model-checker --save markdown json --sequential examples/my_logic.py
```

#### Interactive Workflow

1. **Mode Selection** (if `-q` not specified):
   ```
   Select save mode:
   1) batch - Save all at end
   2) sequential - Prompt after each model
   ```

2. **Model Save Prompt** (after each model):
   ```
   Save model for EXAMPLE_NAME? (Y/n):
   ```

3. **Iteration Prompt** (after saving decision):
   ```
   Find additional models? (y/N):
   ```

4. **Directory Navigation** (at completion):
   ```
   All models saved to: /path/to/output_20250804_123456
   Change to output directory? (y/N):
   ```

#### Interactive Output Structure

In interactive mode, outputs are organized by example:

```
output_YYYYMMDD_HHMMSS/
├── EXAMPLE_1/
│   ├── MODEL_1.md      # Formatted model with colors
│   ├── MODEL_1.json    # Structured data
│   ├── MODEL_2.md      # Second model (if saved)
│   └── MODEL_2.json
├── EXAMPLE_2/
│   ├── MODEL_1.md
│   └── MODEL_1.json
├── summary.json        # Interactive session summary
└── MODELS.json         # All models in single file
```

### Batch Saving

Save results from multiple examples efficiently:

```bash
# Save all theory examples
model-checker theory_lib/logos/examples.py --save markdown

# Process multiple files
for file in examples/*.py; do
    model-checker "$file" --save json
done

# Save with pattern matching
model-checker examples/*_test.py --save all --output-dir results/
```

## Output Directory Structure

### Standard Batch Mode

The ModelChecker organizes saved output hierarchically:

```
output/                           # Default output directory
├── [theory]_[module]/           # Theory and module name
│   ├── [EXAMPLE_NAME]/          # Individual example directory
│   │   ├── summary.md          # Markdown summary
│   │   ├── result.json         # JSON data
│   │   ├── MODEL_1.json        # First model (if multiple)
│   │   ├── MODEL_2.json        # Second model
│   │   └── countermodel.json   # Countermodel (if invalid)
│   └── README.md                # Summary of all examples
├── notebooks/                   # Generated notebooks
│   └── [module]_notebook.ipynb # Interactive notebook
└── reports/                     # Custom reports
    └── comparison_report.md    # Theory comparison results
```

### Sequential Mode Structure

See [Interactive Save Mode](#interactive-save-mode) section above for the specialized directory structure used in sequential save mode.

### Customizing Output Structure

```python
# In your example file, define custom output settings
OUTPUT_SETTINGS = {
    "output_dir": "my_results",
    "organize_by": "date",  # or "theory", "validity"
    "include_metadata": True,
    "compress": True  # Create .zip archive
}
```

## Format Selection Guide

Choose the appropriate format based on your use case:

| Use Case | Recommended Format | Command |
|----------|-------------------|---------|
| Quick validation check | Terminal | `model-checker file.py` |
| Automated testing | JSON | `--save json` |
| Documentation | Markdown | `--save markdown` |
| Interactive exploration | Notebook | `--save notebook` |
| Complete archive | All | `--save all` |
| CI/CD pipeline | JSON | `--save json` |
| Academic paper | Markdown + JSON | `--save markdown json` |

## Practical Examples

### Example 1: Document Theory Validation

```bash
# Generate comprehensive documentation
model-checker theory_lib/logos/examples.py \
    --save markdown \
    --verbose \
    --output-dir docs/validation/

# Results in:
# docs/validation/logos_examples/
#   ├── EXT_TH_1/summary.md
#   ├── MODAL_TH_1/summary.md
#   └── README.md
```

### Example 2: Automated Testing Pipeline

```bash
#!/bin/bash
# test_pipeline.sh

OUTPUT_DIR="test_results/$(date +%Y%m%d_%H%M%S)"
mkdir -p "$OUTPUT_DIR"

# Run tests and save JSON results
for theory in logos exclusion imposition; do
    model-checker "theory_lib/$theory/examples.py" \
        --save json \
        --output-dir "$OUTPUT_DIR/$theory" \
        # No quiet flag needed
done

# Generate summary report
python analyze_results.py "$OUTPUT_DIR" > "$OUTPUT_DIR/summary.md"
```

### Example 3: Interactive Workshop Materials

```bash
# Generate notebook for teaching
model-checker examples/logic_basics.py \
    --save notebook \
    --output-dir workshop_materials/

# Launch Jupyter
jupyter notebook workshop_materials/notebooks/logic_basics_notebook.ipynb
```

### Example 4: Debugging with Multiple Outputs

```bash
# Save everything for detailed analysis
model-checker problematic_example.py \
    --save all \
    --print-constraints \
    --print-z3 \
    --iterate=5 \
    --verbose

# Examine results
ls -la output/problematic_example/
cat output/problematic_example/combined_output.md
```

## Troubleshooting

### Common Issues and Solutions

**Issue**: Output directory permission denied
```bash
# Solution: Use a different directory or fix permissions
model-checker file.py --save json --output-dir ~/Documents/results/
# OR
sudo chmod 755 output/
```

**Issue**: Large output files
```bash
# Solution: Use JSON for large datasets, compress output
model-checker large_test.py --save json
gzip output/theory_module/*.json
```

**Issue**: Overwriting existing files
```bash
# Solution: Use --overwrite flag or unique directories
model-checker file.py --save all --overwrite
# OR with timestamp
model-checker file.py --save all --output-dir "output/$(date +%s)"
```

**Issue**: Notebook generation fails
```bash
# Solution: Ensure Jupyter is installed
pip install jupyter ipywidgets
model-checker file.py --save notebook
```

### Performance Tips

1. **Use JSON for large datasets** - Most efficient format
2. **Batch similar operations** - Process multiple files together
3. **Disable terminal output when saving** - Use `--no-terminal`
4. **Compress archived results** - Use `gzip` or `zip` for storage

## See Also

- [Workflow Guide](WORKFLOW.md) - Complete ModelChecker workflows
- [Examples Guide](EXAMPLES.md) - Writing example files
- [Architecture Documentation](../architecture/OUTPUT.md) - Output system design
- [API Reference](../../Code/src/model_checker/output/README.md) - Output module API

---

[← Back to Usage](README.md) | [Workflow →](WORKFLOW.md) | [Examples →](EXAMPLES.md)