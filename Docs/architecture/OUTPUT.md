# Output Management: Multi-Format Result Generation

[← Back to Methodology](README.md) | [Pipeline →](PIPELINE.md)

## Table of Contents

1. [Introduction](#introduction)
2. [Architecture Overview](#architecture-overview)
3. [Core Components](#core-components)
   - [OutputManager](#outputmanager)
   - [OutputConfig](#outputconfig)
   - [SequentialSaveManager](#sequentialsavemanager)
4. [Output Formats](#output-formats)
   - [Markdown Documentation](#markdown-documentation)
   - [JSON Data Export](#json-data-export)
   - [Jupyter Notebooks](#jupyter-notebooks)
5. [Save Behaviors](#save-behaviors)
   - [Batch Mode](#batch-mode)
   - [Sequential Mode](#sequential-mode)
6. [Directory Structure](#directory-structure)
7. [Integration](#integration)
8. [Usage Examples](#usage-examples)

## Introduction

The Output Management subsystem provides a clean, simple framework for generating model checking results in multiple formats. The architecture uses a single boolean flag to control whether results are saved in batch mode (all at once) or sequential mode (with user prompts).

Key capabilities:
- **Multiple Formats**: Generate markdown documentation, JSON data, and Jupyter notebooks
- **Simple Control**: One boolean flag controls save behavior
- **Directory Management**: Automatic timestamped output directories
- **User Interaction**: Optional prompting for selective saves

## Architecture Overview

The output system follows a simple data flow with one key decision point:

```
┌──────────────┐     ┌──────────────┐     ┌──────────────┐
│Model Results │────▶│OutputConfig  │────▶│OutputManager │
└──────────────┘     │• formats[]   │     │              │
                     │• sequential  │     │ sequential?  │
                     │• save_output │     └──────┬───────┘
                     └──────────────┘            │
                                          ┌──────┴──────┐
                                          │             │
                                          ▼             ▼
                              ┌──────────────┐   ┌─────────────────┐
                              │  Batch Mode  │   │Sequential Mode  │
                              │(accumulate)  │   │   ┌─────────┐   │◄─┐
                              └──────┬───────┘   │   │For Each │   │  │
                                     │           │   │ Model:  │   │  │
                                     │           │   └────┬────┘   │  │
                                     │           └────────┼────────┘  │
                                     │                    ▼           │
                                     │           ┌─────────────────┐  │
                                     │           │SequentialSave-  │  │
                                     │           │Manager prompts  │  │
                                     │           │"Save model?"    │  │
                                     │           └────────┬────────┘  │
                                     │                    ▼           │
                                     │            ┌──────────────┐    │
                                     │            │ User Choice  │    │
                                     │            └──┬────────┬──┘    │
                                     │               ▼        ▼       │
                                     │          ┌──────┐   ┌──────┐   │
                                     │          │ Save │   │ Skip │   │
                                     │          └──────┘   └──────┘   │
                                     │               │        │       │
                                     │               └────┬───┘       │
                                     │                    ▼           │
                                     │           ┌─────────────────┐  │
                                     │           │ More models?    │──┘
                                     │           └─────────┬───────┘
                                     ▼                     ▼
                            ┌───────────────┐    ┌────────────────┐
                            │Store Results  │    │Individual Saves│
                            │               │    │                │
                            │finalize() call│    │                │
                            └───────┬───────┘    └────────┬───────┘
                                    │                     │
                                    └──────────┬──────────┘
                                               ▼
                                    ┌─────────────────────┐
                                    │ Output File Formats │
                                    │┌────┐┌────┐┌──────┐ │
                                    ││ MD ││JSON││ NB   │ │
                                    │└────┘└────┘└──────┘ │
                                    └─────────────────────┘
```

### Component Responsibilities:

**Configuration Layer:**
- **OutputConfig**: Holds three simple settings that control all behavior
  - `formats`: List of output formats to generate (`['markdown', 'json', 'notebook']`)
  - `sequential`: Boolean flag controlling save timing (batch vs sequential)
  - `save_output`: Master enable/disable flag for all output operations

**Management Layer:**
- **OutputManager**: Central orchestrator with direct conditional logic
  - Routes to batch mode (accumulate) or sequential mode (immediate save)
  - Manages directory creation and file organization
  - Coordinates formatter pipeline and handles errors
  - No complex strategy patterns - just simple if/else logic

**Interaction Layer:**
- **SequentialSaveManager**: User interaction handler (only used when `sequential=True`)
  - Prompts user for save decisions with sensible defaults
  - Tracks model numbering for sequential saves
  - Manages directory change prompts at completion

**Format Layer:**
- **Formatters**: Independent format generators that operate in parallel
  - MarkdownFormatter: Human-readable docs with ANSI color conversion
  - JSONFormatter: Structured data with metadata and timestamps
  - NotebookFormatter: Interactive Jupyter notebooks with theory integration

## Core Components

### OutputManager

The OutputManager is the central coordinator for all output operations:

```python
from model_checker.output import OutputManager, OutputConfig

config = OutputConfig(
    formats=['markdown', 'json'],
    sequential=False,  # Batch mode
    save_output=True
)

manager = OutputManager(config)
manager.create_output_directory()
manager.save_example("EXAMPLE_1", model_data, formatted_output)
manager.finalize()  # Saves all accumulated outputs
```

**Key Responsibilities:**
- Format coordination and management
- Save timing control (batch vs sequential)
- Directory creation and file organization
- Progress tracking and error handling

### OutputConfig

Simple configuration class with three key settings:

```python
class OutputConfig:
    def __init__(self,
                 formats: List[str] = None,      # ['markdown', 'json']
                 sequential: bool = False,       # Save immediately with prompts
                 save_output: bool = True):      # Enable/disable saving
```

**Configuration Sources:**
1. CLI flags (highest priority)
2. Settings files
3. Defaults

**CLI Integration:**
```bash
# Batch mode (default)
python -m model_checker --save

# Sequential mode with prompts
python -m model_checker --save --sequential
python -m model_checker -s -q  # Short form

# Specific formats
python -m model_checker --save markdown json
```

### SequentialSaveManager

Handles user interaction when sequential mode is enabled:

```python
class SequentialSaveManager:
    def should_save(self, example_name: str) -> bool
    def should_find_more(self) -> bool
    def get_next_model_number(self, example_name: str) -> int
    def prompt_directory_change(self, output_dir: str) -> bool
```

**User Prompts:**
- "Save model for EXAMPLE_NAME?" (with default: Yes)
- "Find additional models?" (with default: No)
- "Change to output directory?" (with default: No)

## Output Formats

### Markdown Documentation

Human-readable documentation with formatted model structures:

```markdown
# Model Checking Results

## EXAMPLE_1: there is a countermodel

**Premises:**
1. ¬A
2. (A ⊃ B)

**Conclusion:**
3. B

**State Space:**
- #b000 = □
- #b001 = a (world)
- #b010 = b 
```

### JSON Data Export

Machine-readable structured data:

```json
{
  "metadata": {
    "timestamp": "2024-01-15T12:34:56",
    "version": "1.0"
  },
  "models": [
    {
      "example_name": "EXAMPLE_1",
      "has_countermodel": true,
      "worlds": ["a", "b"],
      "verification": {
        "A": {"verifies": ["a"], "falsifies": ["b"]}
      }
    }
  ]
}
```

### Jupyter Notebooks

Interactive notebooks with executable theory code:

```python
# Generated notebook cells:
# 1. Theory imports and setup
# 2. Example definitions
# 3. Model execution
# 4. Result visualization
```

## Save Behaviors

### Batch Mode

**Default behavior** - accumulates all results and saves at the end:

```python
config = OutputConfig(sequential=False)  # Default
manager = OutputManager(config)

# Examples accumulate in memory
manager.save_example("EX1", data1, output1)
manager.save_example("EX2", data2, output2)

# All saved together when finalized
manager.finalize()
```

**Output Structure:**
```
output_20240115_123456/
├── EXAMPLES.md      # All examples combined
├── MODELS.json      # All model data
└── NOTEBOOK.ipynb   # Generated notebook
```

### Sequential Mode

**User-controlled** - prompts before each save:

```python
config = OutputConfig(sequential=True)
sequential_manager = SequentialSaveManager()
manager = OutputManager(config, sequential_manager)

# User prompted for each example
manager.save_example("EX1", data1, output1)  # → "Save model for EX1? [Y/n]"
```

**Output Structure:**
```
output_20240115_123456/
├── EXAMPLE_1/
│   ├── MODEL_1.md
│   └── MODEL_1.json
├── EXAMPLE_2/
│   ├── MODEL_1.md
│   ├── MODEL_2.md
│   └── MODEL_2.json
└── summary.json     # Metadata about saves
```

## Directory Structure

**Automatic Directory Creation:**
- Timestamped directories: `output_YYYYMMDD_HHMMSS/`
- Custom names supported: `manager.create_output_directory("custom_name")`

**File Naming Conventions:**
- Batch mode: `EXAMPLES.md`, `MODELS.json`, `NOTEBOOK.ipynb`
- Sequential mode: `EXAMPLE_NAME/MODEL_N.ext`

## Integration

### Builder Integration

The output system integrates with the builder module:

```python
class BuildModule:
    def _initialize_output_management(self):
        config = create_output_config(self.module_flags, self.general_settings)
        
        if config.sequential:
            input_provider = ConsoleInputProvider()
            self.prompt_manager = SequentialSaveManager(input_provider)
        
        self.output_manager = OutputManager(config, self.prompt_manager)
```

### Settings Integration

Theory files include output settings:

```python
DEFAULT_GENERAL_SETTINGS = {
    "save_output": False,
    "sequential": False,  # Set to True for sequential mode
    # ... other settings
}
```

## Usage Examples

### Basic Usage

```python
from model_checker.output import OutputManager, OutputConfig

# Simple batch save
config = OutputConfig(formats=['markdown'])
manager = OutputManager(config)
manager.create_output_directory()
manager.save_example("TEST", {"model": 1}, "Test output")
manager.finalize()
```

### Sequential Mode

```python
from model_checker.output import SequentialSaveManager

# Sequential with user prompts
config = OutputConfig(sequential=True)
sequential_manager = SequentialSaveManager()
manager = OutputManager(config, sequential_manager)

# User will be prompted for each save
manager.save_example("TEST", {"model": 1}, "Test output")
```

### CLI Usage

```bash
# Generate all formats in batch mode
python -m model_checker examples.py --save

# Sequential mode with markdown only
python -m model_checker examples.py --save markdown --sequential

# Short form
python -m model_checker examples.py -s md -q
```

### Settings Configuration

```python
# In theory semantic files
DEFAULT_GENERAL_SETTINGS = {
    "sequential": True,  # Enable sequential mode by default
    "save_output": True  # Enable output saving
}
```

---

*For more details on the ModelChecker framework, see the [main documentation](README.md).*
