# Output Management: Multi-Format Result Generation Architecture

[← Back to Methodology](README.md) | [Pipeline →](PIPELINE.md)

## Table of Contents

1. [Introduction](#introduction)
2. [OutputManager Architecture](#outputmanager-architecture)
   - [Central Orchestration](#central-orchestration)
   - [Configuration Management](#configuration-management)
   - [Module Context](#module-context)
   - [Directory Management](#directory-management)
3. [Formatter System](#formatter-system)
   - [Protocol-Based Design](#protocol-based-design)
   - [Markdown Generation](#markdown-generation)
   - [JSON Serialization](#json-serialization)
   - [Notebook Integration](#notebook-integration)
4. [Strategy Pattern](#strategy-pattern)
   - [Save Timing Control](#save-timing-control)
   - [Batch Strategy](#batch-strategy)
   - [Sequential Strategy](#sequential-strategy)
   - [Interactive Strategy](#interactive-strategy)
5. [Progress Tracking](#progress-tracking)
   - [Unified Progress System](#unified-progress-system)
   - [Time-Based Animation](#time-based-animation)
   - [Display Adapters](#display-adapters)
   - [Threading Model](#threading-model)
6. [Notebook Generation](#notebook-generation)
   - [Streaming Architecture](#streaming-architecture)
   - [Template System](#template-system)
   - [Memory Efficiency](#memory-efficiency)
   - [Theory Integration](#theory-integration)
7. [Integration Points](#integration-points)
   - [Builder Connection](#builder-connection)
   - [Format Pipeline](#format-pipeline)
   - [Error Handling](#error-handling)
   - [Performance Optimization](#performance-optimization)
8. [Code Examples](#code-examples)
9. [References](#references)

## Introduction

The Output Management subsystem orchestrates the transformation of model checking results into multiple consumable formats through a unified, extensible architecture that separates concerns between format generation, save timing, and overall coordination. The architecture provides a clean separation between the *what* (formats), the *when* (strategies), and the *how* (manager orchestration). This design enables researchers to generate documentation, data exports, and interactive notebooks from the same model checking results without duplicating logic or modifying core algorithms.

Key capabilities this architecture enables:
- **Format Independence**: Each formatter operates independently, allowing new formats without affecting others
- **Flexible Timing**: Save immediately, accumulate for batch processing, or let users control
- **Memory Efficiency**: Stream large outputs without loading everything into memory
- **Interactive Exploration**: User-controlled saving for selective output generation
- **Progress Feedback**: Real-time visual indicators during long-running operations

For the theoretical foundations behind the model structures being output, see [Hyperintensional Semantics](../theory/HYPERINTENSIONAL.md). For how models are generated, see [Builder Pattern](BUILDER.md).

## OutputManager Architecture

### Central Orchestration

OutputManager serves as the single point of coordination for all output operations, implementing a facade pattern that shields complexity from the calling code:

```python
# OutputManager coordinates all output operations
manager = OutputManager(config, interactive_manager)
# Handles:
# 1. Format selection based on configuration
# 2. Strategy selection for save timing
# 3. Directory creation and management
# 4. Error handling and recovery
# 5. Progress tracking integration
```

The manager maintains several key responsibilities:

- **Format Coordination**: Instantiates and manages formatters based on configuration
- **Strategy Delegation**: Uses the selected strategy to determine save timing
- **State Management**: Tracks accumulated results and interactive saves
- **Resource Cleanup**: Ensures proper finalization of all outputs

**Why Central Orchestration?** This approach prevents output logic from spreading throughout the codebase. Without OutputManager, each component would need to understand formats, timing, and file organization. The manager encapsulates these concerns, providing a clean interface that other components can use without understanding output internals.

### Configuration Management

OutputConfig provides centralized configuration that flows through the entire output pipeline:

```python
from model_checker.output.config import OutputConfig

# Configuration hierarchy
config = OutputConfig(
    formats=['markdown', 'json', 'notebook'],  # What to generate
    mode='batch',                              # When to save
    sequential_files='multiple',               # How to organize
    save_output=True                           # Whether to save
)

# CLI integration
config = OutputConfig.from_cli_args(args)
# Parses --save flags:
# --save              → All formats
# --save markdown     → Only markdown
# --save json notebook → Specific formats
```

Configuration options control behavior at multiple levels:
- `formats`: Which output formats to generate (markdown, json, notebook)
- `mode`: Save timing strategy (batch, sequential, interactive)
- `sequential_files`: File organization for sequential mode
- `save_output`: Master switch for output generation

The configuration object serves as the single source of truth, eliminating configuration drift between components.

### Module Context

OutputManager requires module context for proper notebook generation:

```python
# Module context provides semantic theories and examples
manager.set_module_context(
    module_vars={
        'semantic_theories': {
            'Logos': {...},
            'Exclusion': {...}
        },
        'example_range': {
            'EX_1': [premises, conclusions, settings],
            'EX_2': [...]
        }
    },
    source_path='theory_lib/logos/examples.py'
)
```

The module context bridges between the execution environment and output generation:
- **Semantic Theories**: Required for notebook template selection
- **Example Range**: Provides the complete set of examples for batch processing
- **Source Path**: Used for determining theory type and locating templates

This context separation ensures OutputManager doesn't need direct knowledge of model checking internals while still having access to necessary metadata.

### Directory Management

OutputManager implements intelligent directory organization with timestamp-based naming:

```python
# Directory structure created by OutputManager
ModelChecker_Outputs_20250115_143052/
├── EXAMPLES.md        # Combined markdown documentation
├── MODELS.json        # Structured data export
├── NOTEBOOK.ipynb     # Interactive Jupyter notebook
└── summary.json       # Metadata (interactive mode)
```

Directory management features:
- **Timestamp Naming**: Prevents overwrites and enables chronological organization
- **Lazy Creation**: Directories created only when first output is saved
- **Mode-Aware Structure**: Different structures for batch vs sequential modes
- **Atomic Operations**: Uses temporary files with rename for consistency

## Formatter System

The formatter system transforms internal model representations into consumable output formats. Each formatter implements a protocol-based interface, enabling clean extension and testing:

```
┌────────────────────────────────────────────────────────────────┐
│                        IOutputFormatter                        │
│                          (Protocol)                            │
│                                                                │
│  ┌────────────────────────────────────────────────────────┐    │
│  │ format_example(data, output) → str                     │    │
│  │ • Transform single example to format                   │    │
│  │ • Handle model data and raw output                     │    │
│  └────────────────────────────────────────────────────────┘    │
│                                                                │
│  ┌────────────────────────────────────────────────────────┐    │
│  │ format_batch(examples) → str                           │    │
│  │ • Combine multiple examples                            │    │
│  │ • Format-specific aggregation                          │    │
│  └────────────────────────────────────────────────────────┘    │
│                                                                │
│  ┌────────────────────────────────────────────────────────┐    │
│  │ get_file_extension() → str                             │    │
│  │ • Return appropriate extension                         │    │
│  │ • Used for file naming                                 │    │
│  └────────────────────────────────────────────────────────┘    │
└────────────────────────────────────────────────────────────────┘
                                │
                ┌───────────────┼───────────────┐
                │               │               │
                ▼               ▼               ▼
    ┌──────────────────┐ ┌──────────────┐ ┌───────────────────┐
    │MarkdownFormatter │ │JSONFormatter │ │NotebookFormatter  │
    │ • Human readable │ │ • Data export│ │ • Interactive     │
    │ • LaTeX support  │ │ • Structured │ │ • Adapter pattern │
    │ • GitHub flavor  │ │ • Complete   │ │ • Streaming gen   │
    └──────────────────┘ └──────────────┘ └───────────────────┘
```

### Protocol-Based Design

The formatter system uses Python protocols (structural subtyping) rather than inheritance:

```python
from typing import Protocol

class IOutputFormatter(Protocol):
    """Protocol defining formatter interface."""
    
    def format_example(self, example_data: Dict[str, Any], 
                      model_output: str) -> str:
        """Format single example."""
        ...
    
    def format_batch(self, examples: list) -> str:
        """Format multiple examples."""
        ...
```

**Why Protocols?** Protocols provide interface contracts without forcing inheritance hierarchies. This allows formatters to evolve independently while maintaining compatibility. Testing becomes simpler since mock formatters don't need to inherit from a base class. The protocol serves as documentation of the expected interface.

### Markdown Generation

MarkdownFormatter produces human-readable documentation with mathematical notation:

```python
# Markdown output structure
## Example: MODAL_TH_1
### Theory: Brast-McKie

**Premises:**
- □(p → q)
- □p

**Conclusions:**
- □q

**Result:** ✓ Valid (No countermodel found)

### Model Structure
States: {s0, s1, s2}
Relations: R(s0, s1), R(s1, s2)
Valuations: p(s0, s1), q(s1, s2)
```

The formatter handles:
- **Mathematical Symbols**: Converts LaTeX to Unicode for readability
- **Structured Sections**: Consistent organization across examples
- **GitHub Compatibility**: Renders correctly on GitHub and other platforms
- **Model Visualization**: Clear presentation of states and relations

### JSON Serialization

JSONFormatter provides complete data serialization for programmatic analysis:

```python
# JSON output structure
{
    "example": "MODAL_TH_1",
    "theory": "Brast-McKie",
    "premises": ["□(p → q)", "□p"],
    "conclusions": ["□q"],
    "has_model": false,
    "settings": {
        "N": 4,
        "contingent": true
    },
    "states": [...],
    "relations": {...},
    "propositions": {...}
}
```

Serialization features:
- **Complete Data**: All model information preserved
- **Nested Structures**: Maintains hierarchical relationships
- **Type Preservation**: Numbers, strings, booleans maintained
- **Compact Option**: Minified output for size optimization

### Notebook Integration

NotebookFormatter acts as an adapter between the formatter protocol and streaming notebook generation:

```python
class NotebookFormatter:
    """Adapter for notebook generation in unified pipeline."""
    
    def set_context(self, module_vars, source_path):
        """Receive module context from OutputManager."""
        self.generator = StreamingNotebookGenerator()
        self.module_vars = module_vars
        self.source_path = source_path
    
    def format_for_streaming(self, output_path):
        """Generate notebook using streaming approach."""
        self.generator.generate_notebook_stream(
            self.module_vars,
            self.source_path,
            output_path
        )
```

**Adapter Pattern Benefits**: The adapter pattern allows the streaming notebook generator to work within the formatter framework without modifying either side. The generator maintains its efficient streaming approach while the formatter system sees a consistent interface. This separation enables independent evolution of both components.

## Strategy Pattern

The strategy pattern controls when outputs are saved, decoupling save timing from format generation:

```
┌─────────────────────────────────────────────────────────────────┐
│                        OutputStrategy                           │
│                      (Abstract Interface)                       │
│                                                                 │
│  ┌──────────────────────────────────────────────────────────┐   │
│  │ should_save_immediately() → bool                         │   │
│  │ • Determines if outputs should be saved now              │   │
│  └──────────────────────────────────────────────────────────┘   │
│                                                                 │
│  ┌──────────────────────────────────────────────────────────┐   │
│  │ accumulate(name, outputs)                                │   │
│  │ • Store results for later saving                         │   │
│  └──────────────────────────────────────────────────────────┘   │
│                                                                 │
│  ┌──────────────────────────────────────────────────────────┐   │
│  │ finalize(save_callback)                                  │   │
│  │ • Process accumulated results                            │   │
│  └──────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────┘
                                │
                ┌───────────────┼───────────────┐
                │               │               │
                ▼               ▼               ▼
  ┌──────────────────┐ ┌──────────────────┐ ┌───────────────────┐
  │ BatchStrategy    │ │SequentialStrategy│ │InteractiveStrategy│
  │ • Accumulate all │ │ • Save immediate │ │ • User controlled │
  │ • Save at end    │ │ • Constant memory│ │ • Selective save  │
  │ • Min I/O ops    │ │ • Real-time out  │ │ • Manual control  │
  └──────────────────┘ └──────────────────┘ └───────────────────┘
```

### Save Timing Control

Strategies encapsulate different approaches to output timing:

```python
# Strategy determines when to save
if strategy.should_save_immediately():
    save_to_disk(formatted_outputs)
else:
    strategy.accumulate(example_name, formatted_outputs)

# At completion
strategy.finalize(lambda name, outputs: save_to_disk(outputs))
```

Each strategy implements a specific timing policy:
- **Immediate vs Deferred**: Save now or accumulate for later
- **Memory vs I/O Tradeoff**: Balance memory usage against disk operations
- **User Control**: Allow manual intervention in save decisions

### Batch Strategy

BatchStrategy accumulates all results and saves at the end:

```python
class BatchStrategy(OutputStrategy):
    def __init__(self):
        self.accumulated = {}
    
    def should_save_immediately(self) -> bool:
        return False  # Never save immediately
    
    def accumulate(self, name: str, outputs: Dict[str, str]):
        self.accumulated[name] = outputs
    
    def finalize(self, save_callback):
        # Save all accumulated results
        for name, outputs in self.accumulated.items():
            save_callback(name, outputs)
```

Batch processing benefits:
- **Minimal I/O**: Single write operation per format
- **Atomic Output**: All or nothing result generation
- **Efficient Aggregation**: Can optimize combined output
- **Simplified Recovery**: Easy rollback on failure

### Sequential Strategy

SequentialStrategy saves each result immediately:

```python
class SequentialStrategy(OutputStrategy):
    def __init__(self, sequential_files='multiple'):
        self.sequential_files = sequential_files
    
    def should_save_immediately(self) -> bool:
        return True  # Always save immediately
    
    def get_file_path(self, output_dir, example_name, format_name, ext):
        if self.sequential_files == 'multiple':
            # Separate file per example
            return f"{output_dir}/{example_name}.{ext}"
        else:
            # Append to single file
            return f"{output_dir}/RESULTS.{ext}"
```

Sequential processing benefits:
- **Constant Memory**: No accumulation of results
- **Partial Results**: See output as computation progresses
- **Crash Recovery**: Completed examples preserved on failure
- **Real-time Monitoring**: Watch results appear during execution

### Interactive Strategy

InteractiveStrategy puts users in control of saving:

```python
class InteractiveStrategy(OutputStrategy):
    def __init__(self):
        self.accumulated = {}
        self.save_decision = None
    
    def should_save_immediately(self) -> bool:
        # Based on user interaction
        return self.save_decision == 'y'
    
    def prompt_user(self, example_name):
        response = input(f"Save {example_name}? [y/n/a/s]: ")
        # y: yes, n: no, a: all, s: stop
        return response
```

Interactive features:
- **Selective Saving**: Choose which examples to keep
- **Exploration Mode**: Try different settings without saving everything
- **User Control**: Stop processing when desired results found
- **Space Efficiency**: Save only interesting countermodels

Interactive mode activation has clear priority:
1. **CLI Flag**: `--interactive` always enables interactive mode (highest priority)
2. **Output Mode**: `--output-mode` flag can set mode but is overridden by `--interactive`
3. **Settings**: `interactive: True` in general_settings enables by default
4. **Default**: Batch mode if no configuration specified

## Progress Tracking

The progress tracking system provides real-time feedback during model checking operations, particularly valuable during iterative searches for multiple non-isomorphic models:

```
┌─────────────────────────────────────────────────────────────────┐
│                        UnifiedProgress                          │
│                    (Central Coordinator)                        │
│                                                                 │
│  ┌──────────────────────────────────────────────────────────┐   │
│  │ • Manages multiple progress bars                         │   │
│  │ • Tracks cumulative statistics                           │   │
│  │ • Coordinates display updates                            │   │
│  │ • Handles iteration reporting                            │   │
│  └──────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────┘
                                │
                                ▼
┌─────────────────────────────────────────────────────────────────┐
│                      TimeBasedProgress                          │
│                   (Animated Progress Bar)                       │
│                                                                 │
│  ┌──────────────────────────────────────────────────────────┐   │
│  │ • Time-based animation (fills over timeout duration)     │   │
│  │ • Background thread for smooth updates                   │   │
│  │ • Immediate completion on model found                    │   │
│  │ • Shows model count and skip statistics                  │   │
│  └──────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────┘
                                │
                                ▼
┌─────────────────────────────────────────────────────────────────┐
│                       ProgressDisplay                           │
│                      (Display Adapters)                         │
│                                                                 │
│  ┌──────────────────┐        ┌──────────────────────────────┐   │
│  │ TerminalDisplay  │        │ BatchDisplay                 │   │
│  │ • Interactive    │        │ • Non-interactive            │   │
│  │ • Carriage return│        │ • No-op operations           │   │
│  │ • Color support  │        │ • Silent mode                │   │
│  └──────────────────┘        └──────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────┘
```

### Unified Progress System

UnifiedProgress coordinates all progress tracking across the framework:

```python
# Created when iteration requested
if settings.get('iterate', 1) > 1:
    progress = UnifiedProgress(
        total_models=settings['iterate'],
        timeout=settings['max_time']
    )
    
    # Track each model search
    progress.start_search(model_number=1)
    # ... search executes ...
    progress.complete_search(found=True, skipped=2)
```

The unified system provides:
- **Multi-Model Tracking**: Separate progress for each model search
- **Statistics Collection**: Models found, skipped, time elapsed
- **Report Generation**: Summary of iteration results
- **Clean Integration**: Hooks into iterator without coupling

### Time-Based Animation

TimeBasedProgress implements smooth animated progress bars:

```python
# Progress bar fills based on elapsed time
Finding non-isomorphic models: [████████░░░░░░░░░░░░] 2/4 (3 skipped) 2.5s

# Animation calculation
elapsed = time.time() - start_time
progress = min(1.0, elapsed / timeout)
filled = int(bar_width * progress)
```

Animation features:
- **Smooth Updates**: 100ms refresh rate for fluid animation
- **Time-Based Filling**: Progress correlates with timeout duration
- **Immediate Completion**: Jumps to 100% when model found
- **Skip Statistics**: Shows isomorphic models skipped

### Display Adapters

Display adapters handle environment-specific output:

```python
class TerminalDisplay(ProgressDisplay):
    """Interactive terminal display."""
    
    def update(self, message: str):
        # Use carriage return for in-place update
        terminal_width = shutil.get_terminal_size().columns
        self.stream.write(f"\r{message.ljust(terminal_width)}")
        self.stream.flush()

class BatchDisplay(ProgressDisplay):
    """Non-interactive batch display."""
    
    def update(self, message: str):
        pass  # Silent in batch mode
```

Display adaptation ensures:
- **Terminal Detection**: Automatic enable/disable based on environment
- **Width Management**: Prevents line wrapping in narrow terminals
- **Clean Updates**: Proper line clearing and cursor positioning
- **Color Support**: Orange/amber bars when terminal supports color

### Threading Model

Progress animation runs in background threads for non-blocking updates:

```python
class TimeBasedProgress:
    def start(self):
        self.thread = threading.Thread(target=self._animate)
        self.thread.daemon = True  # Won't block program exit
        self.thread.start()
    
    def _animate(self):
        while not self.stop_event.is_set():
            # Update progress bar
            self._update_display()
            time.sleep(0.1)  # 100ms refresh
```

Threading considerations:
- **Daemon Threads**: Don't prevent program termination
- **Thread Safety**: Minimal shared state, atomic operations
- **Resource Cleanup**: Proper thread termination on completion
- **CPU Efficiency**: Low overhead with sleep-based updates

## Notebook Generation

The notebook generation subsystem creates interactive Jupyter notebooks through an efficient streaming architecture that processes examples without loading everything into memory:

```
┌─────────────────────────────────────────────────────────────────┐
│                   StreamingNotebookGenerator                    │
│                     (Main Coordinator)                          │
│                                                                 │
│  ┌──────────────────────────────────────────────────────────┐   │
│  │ • Loads template sections for theory                     │   │
│  │ • Streams examples one at a time                         │   │
│  │ • Substitutes placeholders dynamically                   │   │
│  │ • Maintains constant memory usage                        │   │
│  └──────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────┘
                                │
                ┌───────────────┼───────────────┐
                │               │               │
                ▼               ▼               ▼
  ┌──────────────────┐ ┌──────────────────┐ ┌──────────────────┐
  │ NotebookWriter   │ │ TemplateLoader   │ │ TheoryTemplates  │
  │ • Stream JSON    │ │ • Find templates │ │ • Setup cells    │
  │ • Write cells    │ │ • Load sections  │ │ • Example cells  │
  │ • Valid .ipynb   │ │ • Cache loaded   │ │ • Result format  │
  └──────────────────┘ └──────────────────┘ └──────────────────┘
```

### Streaming Architecture

The streaming approach ensures constant memory usage regardless of example count:

```python
with NotebookWriter(output_path) as writer:
    # Write setup section
    for cell in template_sections['setup_cells']:
        writer.write_cell(cell)  # Written immediately to disk
    
    # Stream examples one at a time
    for name, definition in example_range.items():
        cells = generate_example_cells(name, definition)
        for cell in cells:
            writer.write_cell(cell)
        # Memory for this example freed here
    
    # Write conclusion
    for cell in template_sections['conclusion_cells']:
        writer.write_cell(cell)
```

**Why Streaming?** Traditional notebook generation loads all cells into memory before writing. With hundreds of examples, this creates significant memory pressure. Streaming writes each cell immediately, maintaining constant memory usage regardless of notebook size. This enables generation of arbitrarily large notebooks without memory concerns.

### Template System

Templates define theory-specific notebook structure:

```python
# Theory template structure
{
    "setup_cells": [
        {
            "cell_type": "markdown",
            "source": ["# {{THEORY_NAME}} Model Checking"]
        },
        {
            "cell_type": "code",
            "source": [
                "from model_checker.jupyter import create_build_example",
                "from {{THEORY_MODULE}} import {{THEORY_CLASS}}"
            ]
        }
    ],
    "example_template": {
        "cell_type": "code",
        "source": [
            "# Example: {{EXAMPLE_NAME}}",
            "example = create_build_example(",
            "    '{{EXAMPLE_NAME}}',",
            "    {{EXAMPLE_DEFINITION}}",
            ")"
        ]
    }
}
```

Template features:
- **Theory-Specific**: Each theory provides custom setup
- **Placeholder Substitution**: Dynamic content injection
- **Section Organization**: Setup, examples, conclusion
- **Discovery Mechanism**: Automatic template location

### Memory Efficiency

The streaming architecture maintains constant memory usage:

```python
class NotebookWriter:
    def write_cell(self, cell: Dict[str, Any]):
        """Write single cell to output file."""
        if self.first_cell:
            self.file.write('{"cells": [')
            self.first_cell = False
        else:
            self.file.write(',')
        
        # Write cell JSON directly to file
        json.dump(cell, self.file)
        # Cell object can be garbage collected immediately
```

Memory optimizations:
- **No Full Notebook in Memory**: Only current cell held
- **Direct File Writing**: JSON streamed to disk
- **Lazy Template Loading**: Templates loaded only when needed
- **Incremental Processing**: Examples processed individually

### Theory Integration

Notebook generation integrates with semantic theories through template discovery:

```python
class TemplateLoader:
    def get_template_for_class(self, semantics_class):
        """Find appropriate template for theory."""
        
        # Check for class-based template
        class_name = semantics_class.__name__
        if hasattr(templates, class_name + 'Template'):
            return getattr(templates, class_name + 'Template')()
        
        # Check for JSON template in theory directory
        theory_path = Path(semantics_class.__module__).parent
        template_path = theory_path / 'notebooks' / 'template.json'
        if template_path.exists():
            return JSONTemplate(template_path)
        
        # Fall back to base template
        return BaseNotebookTemplate()
```

Integration features:
- **Automatic Discovery**: Templates found by convention
- **Multiple Formats**: Support class-based and JSON templates
- **Fallback Mechanism**: Base template for unknown theories
- **Theory Independence**: Templates isolated from core logic

## Integration Points

The output subsystem integrates cleanly with other ModelChecker components while maintaining clear boundaries and minimal coupling:

### Builder Connection

BuildModule creates and configures OutputManager with proper context:

```
┌─────────────────────────────────────────────────────────────────┐
│                          BuildModule                            │
│                                                                 │
│  ┌──────────────────────────────────────────────────────────┐   │
│  │ 1. Creates OutputConfig from CLI args                    │   │
│  │ 2. Instantiates OutputManager with config                │   │
│  │ 3. Sets module context (theories, examples)              │   │
│  │ 4. Passes example results to manager                     │   │
│  │ 5. Calls finalize() at completion                        │   │
│  └──────────────────────────────────────────────────────────┘   │
└──────────────────────────────┬──────────────────────────────────┘
                                │
                                ▼
┌─────────────────────────────────────────────────────────────────┐
│                         OutputManager                           │
│                                                                 │
│  ┌──────────────────────────────────────────────────────────┐   │
│  │ • Receives example data and formatted output             │   │
│  │ • Delegates to formatters for transformation             │   │
│  │ • Uses strategy for save timing decisions                │   │
│  │ • Manages output directory and files                     │   │
│  │ • Coordinates notebook generation                        │   │
│  └──────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────┘
```

The integration ensures:
- **Clean Handoff**: BuildModule passes data without knowing output details
- **Context Preservation**: Module information flows to notebook generation
- **Error Isolation**: Output failures don't crash model checking
- **Progress Integration**: Automatic progress tracking when iterate > 1

### Format Pipeline

All formats flow through a unified pipeline ensuring consistency and enabling parallel generation:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           Format Generation Pipeline                        │
│                                                                             │
│  INPUT SOURCES                       OUTPUT MANAGER                         │
│  ─────────────                       ─────────────                          │
│                                                                             │
│  ┌──────────────┐                 ┌──────────────────┐                      │
│  │ Example Data │────────┐        │                  │                      │
│  │ • Name       │        │        │   Orchestrator   │                      │
│  │ • Theory     │        │        │                  │                      │
│  │ • Settings   │        ├───────▶│  • Routes data   │                      │
│  └──────────────┘        │        │  • Manages state │                      │
│                          │        │  • Handles errors│                      │
│  ┌──────────────┐        │        │  • Controls flow │                      │
│  │ Model Output │────────┤        │                  │                      │
│  │ • States     │        │        └────────┬─────────┘                      │
│  │ • Relations  │        │                 │                                │
│  │ • Valuations │        │     ┌───────────┼───────────┐                    │
│  └──────────────┘        │     │           │           │                    │
│                          │     ▼           ▼           ▼                    │
│  ┌──────────────┐        │  ┌──────────────────────────────────┐            │
│  │Module Context│────────┘  │      Formatter Delegation        │            │
│  │ • Theories   │           └──────────────────────────────────┘            │
│  │ • Examples   │                │           │           │                  │
│  │ • Source Path│                ▼           ▼           ▼                  │
│  └──────────────┘          ┌─────────┐ ┌─────────┐ ┌───────────┐            │
│                            │Markdown │ │  JSON   │ │ Notebook  │            │
│                            │Formatter│ │Formatter│ │Formatter  │            │
│                            ├─────────┤ ├─────────┤ ├───────────┤            │
│                            │• Headers│ │• Nested │ │• Adapter  │            │
│                            │• LaTeX  │ │• Arrays │ │• Streaming│            │
│                            │• Tables │ │• Objects│ │• Templates│            │
│                            │• Unicode│ │• Compact│ │• Cells    │            │
│                            └────┬────┘ └────┬────┘ └────┬──────┘            │
│                                 │           │           │                   │
│                                 ▼           ▼           ▼                   │
│                          Strategy Layer (Save Timing Control)               │
│                          ┌──────────────────────────────────────┐           │
│                          │  ┌────────┐  ┌────────┐  ┌────────┐  │           │
│                          │  │ Batch  │  │  Seq.  │  │ Inter. │  │           │
│                          │  │Strategy│  │Strategy│  │Strategy│  │           │
│                          │  └────────┘  └────────┘  └────────┘  │           │
│                          └─────────┬──────────┬──────────┬──────┘           │
│                                    │          │          │                  │
│                                    ▼          ▼          ▼                  │
│                                   File System Output Layer                  │
│                            ┌──────────────────────────────────┐             │
│                            │   ModelChecker_Outputs_[TIME]/   │             │
│                            ├──────────────────────────────────┤             │
│                            │    EXAMPLES.md   (Human-readable)│             │
│                            │    MODELS.json   (Data export)   │             │
│                            │    NOTEBOOK.ipynb (Interactive)  │             │
│                            │    summary.json  (Metadata)      │             │
│                            └──────────────────────────────────┘             │
└─────────────────────────────────────────────────────────────────────────────┘
```

Pipeline characteristics:
- **Single Entry Point**: All formats initiated through OutputManager orchestration
- **Parallel Processing**: Formatters operate independently on same source data
- **Consistent Data**: Each formatter receives identical input ensuring uniformity
- **Error Recovery**: Format failures isolated preventing cascade failures
- **Strategy Delegation**: Save timing controlled independently of format generation
- **Atomic Operations**: File writes use temporary files with rename for consistency

### Error Handling

The output subsystem implements comprehensive error handling:

```python
# Custom exception hierarchy
class OutputError(Exception):
    """Base exception for output operations."""

class OutputDirectoryError(OutputError):
    """Directory creation or access errors."""

class FormatterError(OutputError):
    """Format generation errors."""

class StrategyError(OutputError):
    """Strategy operation errors."""

# Error handling in OutputManager
try:
    formatted = formatter.format(example_data)
except FormatterError as e:
    logger.error(f"Format generation failed: {e}")
    # Continue with other formats
```

Error handling principles:
- **Graceful Degradation**: Continue with working formats
- **Clear Messages**: Specific exceptions with context
- **Recovery Options**: Retry or skip based on error type
- **Logging Integration**: All errors logged for debugging

### Performance Optimization

The output subsystem implements several performance optimizations:

```python
# Lazy directory creation
if not self.output_dir and self.save_output:
    self.output_dir = create_timestamped_directory()

# Streaming for large outputs
with open(output_path, 'w') as f:
    for chunk in generate_chunks():
        f.write(chunk)

# Parallel format generation
formatters_tasks = [
    (fmt_name, formatter.format(data))
    for fmt_name, formatter in self.formatters.items()
]

# Efficient JSON serialization
json.dump(data, file, separators=(',', ':'))  # Compact
```

Optimization strategies:
- **Lazy Evaluation**: Defer work until necessary
- **Streaming I/O**: Avoid loading large data into memory
- **Parallel Processing**: Format generation can parallelize
- **Minimal Allocations**: Reuse objects where possible

## Code Examples

### Complete Output Pipeline

```python
# Example: Full output generation pipeline
from model_checker.builder import BuildModule
from model_checker.output import OutputManager
from model_checker.output.config import OutputConfig

# 1. Load module with examples
module_flags = type('Flags', (), {
    'file_path': 'theory_lib/logos/examples.py',
    'save': ['markdown', 'json', 'notebook'],  # Formats to generate
    'output_mode': 'batch',  # Save all at end
    'verbose': True
})()

# 2. BuildModule creates OutputManager automatically
build_module = BuildModule(module_flags)
# Internally:
# - Creates OutputConfig from flags
# - Instantiates OutputManager
# - Sets module context for notebooks

# 3. Process examples (output managed automatically)
for example_name, example_case in build_module.example_range.items():
    # BuildExample processes
    result = build_module.process_example(example_name, example_case)
    
    # OutputManager.save_example() called internally
    # - Formats generated based on config
    # - Strategy determines save timing
    # - Progress shown if iterate > 1

# 4. Finalization happens automatically
# - Batch strategy saves all accumulated results
# - Notebook generated with streaming approach
# - Directory structure organized
```

This pipeline demonstrates the seamless integration where BuildModule handles all output coordination without the user needing to understand output internals.

### Custom Formatter Implementation

```python
from model_checker.output.formatters.base import IOutputFormatter

class HTMLFormatter:
    """Generate HTML reports from model checking results."""
    
    def format_example(self, example_data: Dict[str, Any], 
                      model_output: str) -> str:
        """Format as HTML with styling."""
        html = f"""
        <div class="example">
            <h2>{example_data['example_name']}</h2>
            <div class="theory">{example_data['theory_name']}</div>
            
            <div class="formulas">
                <h3>Premises</h3>
                <ul>
                    {''.join(f'<li>{p}</li>' for p in example_data['premises'])}
                </ul>
                
                <h3>Conclusions</h3>
                <ul>
                    {''.join(f'<li>{c}</li>' for c in example_data['conclusions'])}
                </ul>
            </div>
            
            <div class="result">
                <strong>Result:</strong> 
                {'✓ Valid' if not example_data['has_model'] else '✗ Invalid'}
            </div>
            
            <pre class="model">{model_output}</pre>
        </div>
        """
        return html
    
    def format_batch(self, examples: list) -> str:
        """Wrap examples in HTML document."""
        return f"""
        <!DOCTYPE html>
        <html>
        <head>
            <title>Model Checking Results</title>
            <style>
                .example {{ margin: 20px; padding: 20px; border: 1px solid #ccc; }}
                .theory {{ color: #666; font-style: italic; }}
                .result {{ margin: 20px 0; font-size: 1.2em; }}
                pre.model {{ background: #f5f5f5; padding: 10px; }}
            </style>
        </head>
        <body>
            <h1>Model Checking Results</h1>
            {''.join(examples)}
        </body>
        </html>
        """
    
    def get_file_extension(self) -> str:
        return 'html'

# Register formatter
OutputManager.register_formatter('html', HTMLFormatter())
```

This example shows how new formats integrate cleanly through the protocol interface without modifying existing code.

### Interactive Mode Usage

```python
from model_checker.output.interactive import InteractiveSaveManager
from model_checker.output.input_provider import ConsoleInputProvider

# Create interactive manager
input_provider = ConsoleInputProvider()
interactive_manager = InteractiveSaveManager(input_provider)

# Process examples with user control
for example_name, example_data in examples.items():
    # Process example
    result = process_example(example_data)
    
    # Prompt user
    response = interactive_manager.prompt_for_save(example_name)
    
    if response == 'y':  # Save this one
        output_manager.save_example(example_name, result)
    elif response == 'n':  # Skip this one
        continue
    elif response == 'a':  # Save all remaining
        interactive_manager.save_all_remaining = True
        output_manager.save_example(example_name, result)
    elif response == 's':  # Stop processing
        break

# Generate summary
summary = interactive_manager.get_summary()
# Shows which examples were saved, skipped, etc.
```

Interactive mode provides fine-grained control over what gets saved, useful for exploring different configurations and theories.

### Progress Integration Example

```python
# Progress tracking activates automatically with iteration
EXAMPLE_settings = {
    'N': 4,
    'iterate': 5,  # Find 5 non-isomorphic models
    'max_time': 10  # 10 second timeout
}

# BuildModule detects iterate > 1 and creates UnifiedProgress
# User sees animated progress bars:
# Finding non-isomorphic models: [████████░░░░░░░░] 3/5 (7 skipped) 5.2s

# After completion, iteration report shows:
"""
ITERATION REPORT
    Model 1: Initial model (0.02s)
    Model 2: Found after skipping 3 isomorphic models (1.34s)
    Model 3: Found after skipping 4 isomorphic models (2.11s)
    Model 4: Found after skipping 0 isomorphic models (0.43s)
    Model 5: Not found - timeout after 10s after checking 89 models

Total: 4/5 models found, 7 isomorphic models skipped, 10.00s elapsed
"""
```

Progress tracking provides valuable feedback during long-running searches, showing both progress and efficiency metrics.

## References

### Implementation Files

- `model_checker/output/manager.py` - OutputManager implementation
- `model_checker/output/config.py` - Configuration management
- `model_checker/output/formatters/` - Format generators
- `model_checker/output/strategies/` - Save timing strategies
- `model_checker/output/progress/` - Progress tracking system
- `model_checker/output/notebook/` - Notebook generation

### Related Documentation

- [Builder Pattern](BUILDER.md) - How models are generated
- [Pipeline Overview](PIPELINE.md) - Overall system architecture
- [Settings Management](SETTINGS.md) - Configuration system
- [Iterator System](ITERATE.md) - Multiple model generation

---

[← Back to Methodology](README.md) | [Pipeline →](PIPELINE.md)
