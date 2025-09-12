# Output Integration Tests

## Overview

This directory contains integration tests for the output package, validating the complete output pipeline from build results to final formatted output. These tests ensure that all output strategies, formatters, and interactive features work correctly together.

## Modules

### test_build_integration.py
**Purpose**: Tests integration with builder package for output generation
**Key Classes**: Tests for receiving and processing build results
**Key Functions**: Tests result collection, formatting, file generation
**Dependencies**: `pytest`, `output`, `builder`
**Used By**: Build output validation

### test_cli_arguments.py
**Purpose**: Tests CLI argument parsing and output configuration
**Key Classes**: Tests for command-line output options
**Key Functions**: Tests argument parsing, format selection, output paths
**Dependencies**: `pytest`, `output.cli`, `argparse`
**Used By**: CLI integration validation

### test_collector_integration.py
**Purpose**: Tests data collection from various sources
**Key Classes**: Tests for collecting model data, results, metadata
**Key Functions**: Tests data aggregation, transformation, validation
**Dependencies**: `pytest`, `output.collector`
**Used By**: Data collection validation

### test_interactive.py
**Purpose**: Tests interactive output features and user interaction
**Key Classes**: Tests for interactive displays and prompts
**Key Functions**: Tests user interaction, dynamic updates, progress displays
**Dependencies**: `pytest`, `output.interactive`
**Used By**: Interactive feature validation

### test_markdown_relations.py
**Purpose**: Tests Markdown formatting of model relations
**Key Classes**: Tests for relation table generation
**Key Functions**: Tests relation formatting, table layout, edge cases
**Dependencies**: `pytest`, `output.markdown_formatter`
**Used By**: Markdown output validation

### test_model_data_collection.py
**Purpose**: Tests collection and organization of model data
**Key Classes**: Tests for model data extraction and structuring
**Key Functions**: Tests state extraction, relation mapping, valuation collection
**Dependencies**: `pytest`, `output.model_data`
**Used By**: Model data validation

### test_output_directory.py
**Purpose**: Tests output directory management and organization
**Key Classes**: Tests for directory creation and file organization
**Key Functions**: Tests directory structure, file naming, cleanup
**Dependencies**: `pytest`, `output.directory`, `pathlib`
**Used By**: Directory management validation

### test_output_integration.py
**Purpose**: Tests overall output system integration
**Key Classes**: Tests for complete output pipeline
**Key Functions**: Tests end-to-end output generation, format coordination
**Dependencies**: `pytest`, all output modules
**Used By**: System integration validation

### test_output_manager_interactive.py
**Purpose**: Tests OutputManager with interactive features
**Key Classes**: Tests for output management with user interaction
**Key Functions**: Tests interactive mode, user choices, dynamic formatting
**Dependencies**: `pytest`, `output.manager`
**Used By**: Manager validation

### test_output_modes.py
**Purpose**: Tests different output modes and strategies
**Key Classes**: Tests for various output strategies
**Key Functions**: Tests mode selection, strategy execution, result formatting
**Dependencies**: `pytest`, `output.strategies`
**Used By**: Strategy validation

## Usage

### Running All Integration Tests
```bash
# From project root
./run_tests.py --integration output

# Or directly with pytest
pytest src/model_checker/output/tests/integration/ -v
```

## Test Coverage

These integration tests validate:
- Complete output pipelines
- Format coordination and selection
- Interactive features and user interaction
- Directory and file management
- Integration with builder results
- CLI argument processing

## See Also

- [Unit Tests](../unit/README.md)
- [Output Package](../../README.md)
- [Strategies](../../strategies/README.md)