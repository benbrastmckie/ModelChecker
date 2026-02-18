# Implementation Plan: Builder Package v1 Modular Refactor

**Date**: 2025-01-11 (Updated 2025-09-04)  
**Author**: AI Assistant  
**Status**: Not Started - READY FOR IMPLEMENTATION  
**Priority**: HIGHEST - Sole major blocker for v1 release  
**Focus**: Refactor builder package for v1 release with improved modularity

## Specification Validation

**Verification Checklist**:
- ✅ Clear phase breakdown (7 phases with specific tasks)
- ✅ Test requirements for each phase (dual testing methodology)
- ✅ Success criteria (line count targets, test passing)
- ✅ Implementation tasks (detailed per phase)

## Executive Summary

This plan refactors the builder package from its current monolithic structure (module.py: 1267 lines) into a well-organized modular architecture. Learning from the successful iterate refactoring, this plan emphasizes **breaking compatibility for cleaner architecture**, **module consolidation to avoid fragmentation**, and **comprehensive testing at each phase**.

## Current State Analysis (Updated 2025-09-04)

### Module Overview
```
builder/
├── module.py (1267 lines) - MONOLITHIC: Running, comparison, translation, I/O [DEGRADED]
├── project.py (526 lines) - Mixed project management and execution
├── example.py (320 lines) - Core BuildExample class
├── graph_utils.py (315 lines) - DUPLICATE of iterate functionality
├── maximize_optimizer.py (249 lines) - Optimizer utilities
├── serialize.py (170 lines) - Serialization utilities
├── z3_utils.py (114 lines) - Z3 model utilities
├── validation.py (105 lines) - Parameter validation
└── tests/ - Comprehensive test suite (2764 lines across 11 test files)
```

**Key Changes Since Original Analysis**:
- module.py has grown from 1063 to 1267 lines (+19%)
- Added maximize_optimizer.py and serialize.py modules
- Extensive test suite developed (11 test files, 2764 lines)
- No progress made on refactoring monolithic structure

### Key Issues

1. **Mixed Responsibilities in module.py** (1267 lines):
   - Model checking execution
   - Theory comparison logic  
   - Theory translation
   - File I/O operations
   - Result formatting
   - Progress bar management
   - Interactive mode handling

2. **Duplication**:
   - graph_utils.py duplicates iterate/graph.py functionality
   - Validation logic scattered across modules

3. **Circular Dependencies**:
   - Late imports throughout to avoid circular references
   - Complex dependency on models and syntactic packages

4. **Large Methods**:
   - Several methods exceed 100 lines
   - Complex nested logic in run_comparison()
   - Growing complexity in run_model_check()

5. **Technical Debt Accumulation**:
   - Module has grown 19% since initial analysis
   - New features added without refactoring
   - Now the largest module in the entire codebase

## Design Philosophy

Following successful patterns from iterate refactoring and lessons learned:

1. **NO BACKWARDS COMPATIBILITY**: Break interfaces freely for cleaner architecture
2. **Module Consolidation**: Combine related functionality to avoid too many small files
3. **Clear Separation**: Each module has a single, well-defined responsibility
4. **Test-Driven Development**: Write tests before refactoring each component
5. **Unified Interfaces**: Ensure consistent patterns across all modules
6. **Pragmatic Decisions**: Accept working solutions when refactoring risk is high

**Note**: Unlike iterate (which was accepted at 729 lines due to fragility), builder has no such constraints and can be safely refactored.

## Target Architecture

```
builder/
├── __init__.py          # Clean exports
├── core.py              # BuildModule orchestration (300 lines)
├── runner.py            # Model checking execution (400 lines)
├── comparison.py        # Theory comparison logic (350 lines)
├── translation.py       # Theory operator translation (250 lines)
├── project.py           # Project generation (existing, cleaned)
├── example.py           # BuildExample (existing, maintained)
├── z3_utils.py          # Z3 utilities (existing, enhanced)
├── progress.py          # Progress tracking (existing)
└── tests/               # Comprehensive test coverage
```

**Module Count**: 10 core modules (removing graph_utils.py duplicate, keeping serialize.py and maximize_optimizer.py)

## Implementation Phases

### Phase 0: Research and Design (REQUIRED FIRST) - COMPLETED IN SPEC

**Objective**: Analyze current implementation and finalize design

**Research Findings**:

1. **Module Structure Analysis**:
   - BuildModule is the only class in module.py
   - 23 methods total in BuildModule
   - Key method groups identified:
     - Model execution: `run_model_check`, `try_single_N`, `process_example`, `process_iterations`
     - Theory comparison: `run_comparison`, `compare_semantics`
     - Translation: `translate`, `translate_example`
     - Orchestration: `run_examples`, `__init__`
     - File I/O: `_load_module`, `_find_project_directory`, `_capture_and_save_output`

2. **Dependency Analysis**:
   - **Late imports to avoid circular dependencies**:
     - `from model_checker.settings import SettingsManager` (line 99)
     - `from model_checker.output import OutputManager` (line 134)
     - `from model_checker.builder.example import BuildExample` (lines 400, 720, 1204)
     - `from model_checker.models.constraints import ModelConstraints` (lines 433, 483, 648)
     - `from model_checker.utils import Z3ContextManager` (line 701)
     - `from model_checker.iterate.metrics import ResultFormatter` (line 1001)
   - **Progress tracking**: Uses `model_checker.output.progress` (UnifiedProgress, Spinner)
   - **No direct iterate package imports** in main module (good separation)

3. **Extraction Boundaries Identified**:
   - **Runner Module** (~400 lines):
     - Methods: `run_model_check`, `try_single_N`, `try_single_N_static`, `try_single_N_serialized`, `process_example`
     - Dependencies: BuildExample, ModelConstraints, Z3ContextManager
   - **Comparison Module** (~350 lines):
     - Methods: `run_comparison`, `compare_semantics`, comparison formatting logic
     - Dependencies: ModelConstraints, output formatting
   - **Translation Module** (~250 lines):
     - Methods: `translate`, `translate_example`, operator mapping logic
     - Dependencies: Syntax, theory dictionaries
   - **Core Module** (~300 lines):
     - Remaining orchestration, initialization, file loading, output capture

4. **Risk Areas Identified**:
   - **Shared state**: OutputManager, settings are instance variables used across modules
   - **Progress tracking**: UnifiedProgress used in iterations, needs careful extraction
   - **Z3 context management**: Critical for avoiding "cannot cast to concrete Boolean" errors
   - **Theory loading**: Complex discovery and loading logic needs preservation

**Analysis Commands Executed**:
```bash
# Structure analysis
grep -n "class " src/model_checker/builder/module.py  # 1 class: BuildModule
grep -n "def " src/model_checker/builder/module.py | wc -l  # 23 methods
wc -l src/model_checker/builder/*.py  # Confirmed line counts

# Dependency analysis
grep -n "from model_checker" src/model_checker/builder/module.py
# Found 11 late imports to avoid circular dependencies

# Test structure
find src/model_checker/builder/tests -name "*.py" -exec wc -l {} \; | sort -n
# Total: 2621 lines across 15 test files
```

**Success Criteria**:
- [x] Complete dependency map created
- [x] Extraction boundaries clearly defined
- [x] Risk areas identified and mitigation planned

**Implementation Status**: Phase 0 research completed in spec. Ready for implementation.

### Phase 1: Test Infrastructure and Baseline

**Objective**: Establish comprehensive test baseline before refactoring

**Tasks**:
1. Create baseline captures of current behavior
2. Write comprehensive tests for module.py components
3. Document all implicit contracts and dependencies
4. Set up test infrastructure for phased refactoring

**Explicit Implementation Details**:

1. **Create Integration Test Fixtures**:
```python
# tests/test_refactor_baseline.py
class RefactorBaselineTests(unittest.TestCase):
    """Capture current behavior before refactoring."""
    
    def setUp(self):
        # Create test modules for each theory
        self.test_modules = {
            'logos': create_logos_test_module(),
            'exclusion': create_exclusion_test_module(),
            'bimodal': create_bimodal_test_module(),
            'imposition': create_imposition_test_module()
        }
    
    def test_module_loading_behavior(self):
        """Document current module loading patterns."""
        # Test _load_module with generated projects
        # Test _is_generated_project detection
        # Test package path construction
    
    def test_settings_validation_flow(self):
        """Capture settings validation behavior."""
        # Test raw_general_settings processing
        # Test per-theory settings validation
        # Test flag override behavior
    
    def test_output_manager_initialization(self):
        """Document output manager creation."""
        # Test interactive mode detection
        # Test save mode prompting
        # Test output directory creation
```

2. **Document Implicit Contracts**:
```python
# docs/refactor_contracts.md
## BuildModule Implicit Contracts

### Theory Loading Contract
- Theories must have 'semantics', 'proposition', 'model', 'operators'
- Theory discovery uses __module__ attribute for package detection
- Generated projects use 'project_' prefix for identification

### Settings Processing Contract
- general_settings validated per-theory via SettingsManager
- First theory's defaults used as baseline
- Flag overrides applied after validation

### Late Import Contract
- BuildExample imported in 3 locations to avoid circular imports
- ModelConstraints imported in 4 locations
- Z3ContextManager imported once for context isolation
```

**Dual Testing Protocol**:

**Method 1 - TDD with Test Runner**:
```bash
# Create tests BEFORE moving code
src/model_checker/builder/tests/test_baseline.py
src/model_checker/builder/tests/test_runner_extraction.py
src/model_checker/builder/tests/test_comparison_extraction.py
src/model_checker/builder/tests/test_translation_extraction.py

# Run to ensure tests fail appropriately
./run_tests.py --package --components builder -v
```

**Method 2 - Direct CLI Testing**:
```bash
# Capture baseline behavior
./dev_cli.py src/model_checker/theory_lib/logos/examples.py > baseline_logos.txt
./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py > baseline_bimodal.txt
./dev_cli.py src/model_checker/theory_lib/exclusion/examples.py > baseline_exclusion.txt
./dev_cli.py src/model_checker/theory_lib/imposition/examples.py > baseline_imposition.txt
```

**Success Criteria**:
- [ ] 100% test coverage for public interfaces
- [ ] Baseline behavior documented
- [ ] All existing tests passing (2764 lines across 11 files)
- [ ] CLI baseline outputs captured

### Phase 2: Extract Runner Module

**Objective**: Extract model checking execution logic to runner.py

**Tasks**:
1. Create runner.py with ModelRunner class
2. Move run_model_check and related methods
3. Extract execution logic from BuildModule
4. Update all imports and dependencies

**Explicit Implementation Details**:

1. **Create runner.py Structure**:
```python
# src/model_checker/builder/runner.py
"""Model checking execution engine."""

from model_checker.output.progress import Spinner
from model_checker.syntactic import Syntax
from model_checker.builder.serialize import serialize_semantic_theory, deserialize_semantic_theory
import concurrent.futures
import time

class ModelRunner:
    """Executes model checking for theories."""
    
    def __init__(self, build_module):
        """Initialize with reference to parent BuildModule for settings."""
        self.build_module = build_module
        self.settings = build_module.general_settings
    
    def run_model_check(self, example_case, example_name, theory_name, semantic_theory):
        """Run model checking with the given parameters (lines 384-416)."""
        from model_checker.builder.example import BuildExample
        
        # Apply translation if needed
        dictionary = semantic_theory.get("dictionary", None)
        if dictionary:
            example_case = self.build_module.translate(example_case, dictionary)
        
        # Start progress tracking
        spinner = Spinner()
        spinner.start()
        
        try:
            example = BuildExample(self.build_module, semantic_theory, example_case, theory_name)
            return example
        finally:
            spinner.stop()
    
    def try_single_N(self, theory_name, semantic_theory, example_case):
        """Try a single N value (lines 417-466)."""
        from model_checker.models.constraints import ModelConstraints
        
        premises, conclusions, settings = example_case
        semantics_class = semantic_theory["semantics"]
        model_structure_class = semantic_theory["model"]
        operators = semantic_theory["operators"]
        syntax = Syntax(premises, conclusions, operators)
        
        # Handle different semantics initialization patterns
        if hasattr(semantics_class, '__name__') and 'Logos' in semantics_class.__name__:
            semantics = semantics_class(combined_settings=settings)
        else:
            semantics = semantics_class(settings)
            
        model_constraints = ModelConstraints(
            settings,
            syntax,
            semantics,
            semantic_theory["proposition"],
        )
        model_structure = model_structure_class(model_constraints, settings)
        run_time = model_structure.z3_model_runtime
        success = run_time < settings['max_time']
        
        self._print_timing_result(model_structure, theory_name, run_time, settings, success)
        return success, run_time
    
    @staticmethod
    def try_single_N_static(theory_name, theory_config, example_case):
        """Static version for multiprocessing (lines 467-535)."""
        # Keep existing implementation
    
    def process_example(self, example_name, example_case, theory_name, semantic_theory):
        """Process a single example with Z3 context isolation (lines 689-963)."""
        from model_checker.utils import Z3ContextManager
        from model_checker.builder.example import BuildExample
        
        with Z3ContextManager() as ctx:
            # Apply translation
            dictionary = semantic_theory.get("dictionary", None)
            if dictionary:
                example_case = self.build_module.translate(example_case, dictionary)
            
            # Create and process example
            example = BuildExample(self.build_module, semantic_theory, example_case, theory_name)
            
            # Handle iterations if needed
            if example.model_structure.z3_model_status and hasattr(example_case[2], 'get'):
                iterate_count = example_case[2].get('iterate', 0)
                if iterate_count > 0:
                    return self._handle_iterations(example, example_name, theory_name, iterate_count)
            
            return example
```

2. **Update BuildModule to Use Runner**:
```python
# In BuildModule.__init__ after line 159
from model_checker.builder.runner import ModelRunner
self.runner = ModelRunner(self)

# Replace method bodies with delegation
def run_model_check(self, example_case, example_name, theory_name, semantic_theory):
    """Delegate to runner."""
    return self.runner.run_model_check(example_case, example_name, theory_name, semantic_theory)
```

**Dual Testing Protocol**:

**Method 1 - TDD with Test Runner**:
```bash
# Run extraction tests
./run_tests.py builder.test_runner_extraction -v

# Run full builder tests
./run_tests.py --package --components builder -v
```

**Method 2 - Direct CLI Testing**:
```bash
# Test each theory and compare to baseline
for theory in logos bimodal exclusion imposition; do
    echo "Testing $theory..."
    ./dev_cli.py src/model_checker/theory_lib/$theory/examples.py > test_$theory.txt
    diff baseline_$theory.txt test_$theory.txt
done
```

**Success Criteria**:
- [ ] All model checking tests pass
- [ ] No circular imports
- [ ] Clean separation from BuildModule
- [ ] No differences from baseline behavior
- [ ] No Z3 casting errors

### Phase 3: Extract Comparison Module

**Objective**: Separate theory comparison logic

**Tasks**:
1. Create comparison.py with TheoryComparator class
2. Move run_comparison and comparison formatting
3. Extract comparison statistics logic
4. Clean up comparison output generation
5. Handle Z3 model comparisons properly

**Explicit Implementation Details**:

1. **Create comparison.py Structure**:
```python
# src/model_checker/builder/comparison.py
"""Theory comparison and benchmarking functionality."""

import concurrent.futures
from model_checker.builder.serialize import serialize_semantic_theory

class TheoryComparator:
    """Compares results across multiple theories."""
    
    def __init__(self, build_module):
        """Initialize with reference to parent BuildModule."""
        self.build_module = build_module
        self.translator = build_module.translator  # Will be created in Phase 4
    
    def run_comparison(self):
        """Compare theories across all examples (lines 638-665)."""
        print()
        for example_name, example_case in self.build_module.example_range.items():
            premises, conclusions, settings = example_case
            print(f"{'='*40}\n")
            print(f"EXAMPLE = {example_name}")
            print(f"  Premises:")
            for prem in premises:
                print(f"    {prem}")
            print(f"  Conclusions:")
            for con in conclusions:
                print(f"    {con}")
            print()
            
            # Use translator to prepare examples
            example_theory_tuples = self.translator.translate_example(
                example_case, self.build_module.semantic_theories
            )
            self.compare_semantics(example_theory_tuples)
            print(f"\n{'='*40}")
    
    def compare_semantics(self, example_theory_tuples):
        """Find maximum model sizes for theories (lines 557-637)."""
        results = []
        active_cases = {}  # Track active cases and their current N values
        
        with concurrent.futures.ProcessPoolExecutor() as executor:
            futures = {}
            all_times = []
            
            # Initialize first run for each case
            for case in example_theory_tuples:
                theory_name, semantic_theory, (premises, conclusions, settings) = case
                
                # Serialize for pickling
                theory_config = serialize_semantic_theory(theory_name, semantic_theory)
                example_case = [premises, conclusions, settings.copy()]
                active_cases[theory_name] = settings['N']
                all_times.append(settings['max_time'])
                
                # Submit with serialized data
                new_case = (theory_name, theory_config, example_case)
                futures[executor.submit(self._try_single_N_static, *new_case)] = (
                    theory_name, theory_config, example_case, semantic_theory
                )
            
            # Process results
            while futures:
                done, _ = concurrent.futures.wait(
                    futures,
                    return_when=concurrent.futures.FIRST_COMPLETED
                )
                
                for future in done:
                    theory_name, theory_config, example_case, semantic_theory = futures.pop(future)
                    
                    try:
                        success, runtime = future.result()
                        
                        if success and runtime < example_case[2]['max_time']:
                            # Increment N and resubmit
                            example_case[2]['N'] = active_cases[theory_name] + 1
                            active_cases[theory_name] = example_case[2]['N']
                            
                            new_case = (theory_name, theory_config, example_case)
                            futures[executor.submit(self._try_single_N_static, *new_case)] = (
                                theory_name, theory_config, example_case, semantic_theory
                            )
                        else:
                            # Found max N
                            results.append((theory_name, active_cases[theory_name] - 1))
                            
                    except Exception as e:
                        print(f"\nERROR: {theory_name} for N = {example_case[2]['N']}. {str(e)}")
                        results.append((theory_name, active_cases.get(theory_name, 0) - 1))
        
        return results
    
    @staticmethod
    def _try_single_N_static(theory_name, theory_config, example_case):
        """Static method for multiprocessing - delegate to runner."""
        from model_checker.builder.module import BuildModule
        return BuildModule.try_single_N_static(theory_name, theory_config, example_case)
```

2. **Update BuildModule**:
```python
# In __init__ after runner creation
from model_checker.builder.comparison import TheoryComparator
self.comparator = TheoryComparator(self)

# Replace methods with delegation
def run_comparison(self):
    """Delegate to comparator."""
    return self.comparator.run_comparison()

def compare_semantics(self, example_theory_tuples):
    """Delegate to comparator."""
    return self.comparator.compare_semantics(example_theory_tuples)
```

**Dual Testing Protocol**:

**Method 1 - TDD with Test Runner**:
```bash
# Test comparison extraction
./run_tests.py builder.test_comparison_extraction -v
```

**Method 2 - Direct CLI Testing**:
```bash
# Test comparison mode
./dev_cli.py -c src/model_checker/theory_lib/logos/examples.py > test_comparison.txt

# Verify output format preserved
grep "Theory Comparison Results" test_comparison.txt
```

**Success Criteria**:
- [ ] Comparison functionality preserved
- [ ] Cleaner output formatting
- [ ] Reusable comparison logic
- [ ] All comparison tests passing
- [ ] Output format matches baseline

### Phase 4: Extract Translation Module

**Objective**: Isolate theory operator translation

**Tasks**:
1. Create translation.py with TheoryTranslator class
2. Move translate_example and operator mappings
3. Consolidate translation logic from multiple locations
4. Add comprehensive translation tests
5. Ensure LaTeX notation preserved

**Explicit Implementation Details**:

1. **Create translation.py Structure**:
```python
# src/model_checker/builder/translation.py
"""Theory operator translation functionality."""

class TheoryTranslator:
    """Handles operator translation between theories."""
    
    def __init__(self, build_module):
        """Initialize with reference to parent BuildModule."""
        self.build_module = build_module
    
    def translate(self, example_case, dictionary):
        """Translate operators in example (lines 333-357)."""
        premises, conclusions, settings = example_case
        translated_premises = [self._replace_operators(prem, dictionary) for prem in premises]
        translated_conclusions = [self._replace_operators(conc, dictionary) for conc in conclusions]
        return [translated_premises, translated_conclusions, settings]
    
    def _replace_operators(self, logical_list, dictionary):
        """Recursively replace operators (lines 349-357)."""
        if not isinstance(logical_list, list):
            return logical_list
        
        if logical_list and logical_list[0] in dictionary:
            logical_list[0] = dictionary[logical_list[0]]
        
        for i in range(1, len(logical_list)):
            logical_list[i] = self._replace_operators(logical_list[i], dictionary)
        
        return logical_list
    
    def translate_example(self, example_case, semantic_theories):
        """Translate example for all theories (lines 358-383)."""
        example_theory_tuples = []
        
        for theory_name, semantic_theory in semantic_theories.items():
            dictionary = semantic_theory.get("dictionary", None)
            
            if dictionary:
                # Deep copy to avoid mutation
                import copy
                translated_case = copy.deepcopy(example_case)
                translated_case = self.translate(translated_case, dictionary)
            else:
                translated_case = example_case
            
            example_tuple = (theory_name, semantic_theory, translated_case)
            example_theory_tuples.append(example_tuple)
        
        return example_theory_tuples
```

2. **Theory-Specific Translation Patterns**:
```python
# Document common translation patterns
## Standard Translations by Theory:

### Logos Theory
dictionary = {
    '\\Box': 'L',          # Necessity to Logos operator
    '\\Diamond': 'M',      # Possibility to Logos operator
    '\\boxright': 'C',     # Counterfactual
}

### Bimodal Theory
dictionary = {
    '\\Box': '\\Box_1',       # Modal to temporal necessity
    '\\Diamond': '\\Diamond_1', # Modal to temporal possibility
    '\\Box_2': '\\Box_2',     # Spatial modality preserved
}

### Exclusion Theory
# Typically uses standard notation - no translation needed

### Imposition Theory
dictionary = {
    '\\boxright': '\\rightarrow_f',  # Fine's conditional
}
```

3. **Update BuildModule**:
```python
# In __init__ after output manager
from model_checker.builder.translation import TheoryTranslator
self.translator = TheoryTranslator(self)

# Replace methods with delegation
def translate(self, example_case, dictionary):
    """Delegate to translator."""
    return self.translator.translate(example_case, dictionary)

def translate_example(self, example_case, semantic_theories):
    """Delegate to translator."""
    return self.translator.translate_example(example_case, semantic_theories)
```

**Dual Testing Protocol**:

**Method 1 - TDD with Test Runner**:
```bash
# Test translation extraction
./run_tests.py builder.test_translation_extraction -v

# Test operator preservation
./run_tests.py builder.test_latex_notation -v
```

**Method 2 - Direct CLI Testing**:
```bash
# Test translation with different theories
./dev_cli.py -t logos,bimodal src/model_checker/theory_lib/logos/examples.py

# Verify operators translated correctly
grep "\\\\Box" test_output.txt  # Should see theory-specific translations
```

**Success Criteria**:
- [ ] All theories translate correctly
- [ ] No hardcoded theory names in core
- [ ] Extensible translation system
- [ ] LaTeX notation preserved
- [ ] Character encoding validated

### Phase 5: Core Module Refactoring

**Objective**: Refactor BuildModule to orchestration role only

**Tasks**:
1. Remove all extracted functionality
2. Update BuildModule to use new modules
3. Simplify initialization and configuration
4. Clean up file I/O operations
5. Rename module.py to core.py

**Explicit Implementation Details**:

1. **Refactor BuildModule to Pure Orchestration**:
```python
# src/model_checker/builder/core.py (renamed from module.py)
"""BuildModule orchestration for model checking examples."""

import os
import sys
import importlib.util
from model_checker.output.progress import UnifiedProgress
from model_checker.syntactic import Syntax

class BuildModule:
    """Orchestrates model checking operations."""
    
    def __init__(self, module_flags):
        """Initialize with minimal orchestration logic."""
        # Core initialization (lines 87-160)
        self.module_flags = module_flags
        self.module_path = module_flags.file_path
        self.module_name = os.path.splitext(os.path.basename(self.module_path))[0]
        
        # Load module and attributes
        self.module = self._load_module()
        self.semantic_theories = self._load_attribute("semantic_theories")
        self.example_range = self._load_attribute("example_range")
        
        # Process settings
        self._process_settings()
        
        # Initialize output management
        self._initialize_output_management()
        
        # Create component instances
        self._initialize_components()
    
    def _process_settings(self):
        """Process and validate settings (lines 110-132)."""
        from model_checker.settings import SettingsManager, DEFAULT_GENERAL_SETTINGS
        
        self.raw_general_settings = getattr(self.module, "general_settings", None)
        
        if self.raw_general_settings is not None:
            first_theory = next(iter(self.semantic_theories.values()))
            temp_manager = SettingsManager(first_theory, DEFAULT_GENERAL_SETTINGS)
            self.general_settings = temp_manager.validate_general_settings(self.raw_general_settings)
            self.general_settings = temp_manager.apply_flag_overrides(self.general_settings, self.module_flags)
        else:
            self.general_settings = DEFAULT_GENERAL_SETTINGS.copy()
        
        # Set attributes for backward compatibility
        for key, value in self.general_settings.items():
            setattr(self, key, value)
    
    def _initialize_output_management(self):
        """Initialize output manager (lines 133-160)."""
        from model_checker.output import OutputManager, InteractiveSaveManager, ConsoleInputProvider
        
        self.interactive_manager = None
        if self.save_output:
            input_provider = ConsoleInputProvider()
            self.interactive_manager = InteractiveSaveManager(input_provider)
            
            if hasattr(self.module_flags, 'interactive') and self.module_flags.interactive:
                self.interactive_manager.set_mode('interactive')
            else:
                self.interactive_manager.prompt_save_mode()
        
        self.output_manager = OutputManager(
            save_output=self.save_output,
            mode=getattr(self.module_flags, 'output_mode', 'batch'),
            sequential_files=getattr(self.module_flags, 'sequential_files', 'multiple'),
            interactive_manager=self.interactive_manager
        )
        
        if self.output_manager.should_save():
            self.output_manager.create_output_directory()
    
    def _initialize_components(self):
        """Create component instances."""
        from model_checker.builder.runner import ModelRunner
        from model_checker.builder.comparison import TheoryComparator
        from model_checker.builder.translation import TheoryTranslator
        
        self.translator = TheoryTranslator(self)
        self.runner = ModelRunner(self)
        self.comparator = TheoryComparator(self)
    
    # Keep these core methods unchanged
    def _discover_theory_module(self, theory_name, semantic_theory):
        """Lines 46-86 - keep as is"""
    
    def _is_generated_project(self, module_dir):
        """Lines 161-192 - keep as is"""
    
    def _find_project_directory(self, module_dir):
        """Lines 193-222 - keep as is"""
    
    def _load_module(self):
        """Lines 223-317 - keep as is"""
    
    def _load_attribute(self, attr_name):
        """Lines 318-332 - keep as is"""
    
    # Delegate all execution to components
    def translate(self, example_case, dictionary):
        return self.translator.translate(example_case, dictionary)
    
    def translate_example(self, example_case, semantic_theories):
        return self.translator.translate_example(example_case, semantic_theories)
    
    def run_model_check(self, example_case, example_name, theory_name, semantic_theory):
        return self.runner.run_model_check(example_case, example_name, theory_name, semantic_theory)
    
    def try_single_N(self, theory_name, semantic_theory, example_case):
        return self.runner.try_single_N(theory_name, semantic_theory, example_case)
    
    def process_example(self, example_name, example_case, theory_name, semantic_theory):
        return self.runner.process_example(example_name, example_case, theory_name, semantic_theory)
    
    def run_comparison(self):
        return self.comparator.run_comparison()
    
    def compare_semantics(self, example_theory_tuples):
        return self.comparator.compare_semantics(example_theory_tuples)
    
    def run_examples(self):
        """Main entry point - simplified orchestration (lines 1197-end)."""
        from model_checker.builder.example import BuildExample
        
        if self.module_flags.comparison:
            self.run_comparison()
        else:
            # Process each example
            for example_name, example_case in self.example_range.items():
                print(f"\nExample: {example_name}")
                
                for theory_name, semantic_theory in self.semantic_theories.items():
                    example = self.process_example(example_name, example_case, theory_name, semantic_theory)
                    
                    # Handle output capture
                    self._capture_and_save_output(example, example_name, theory_name)
    
    def _capture_and_save_output(self, example, example_name, theory_name, model_num=None):
        """Lines 1125-1196 - keep for output handling"""
```

**Dual Testing Protocol**:

**Method 1 - TDD with Test Runner**:
```bash
# Run all builder tests
./run_tests.py --package --components builder -v

# Run integration tests
./run_tests.py builder.test_integration_workflow -v
```

**Method 2 - Direct CLI Testing**:
```bash
# Comprehensive theory testing
for theory in logos bimodal exclusion imposition; do
    echo "=== Testing $theory ==="
    ./dev_cli.py src/model_checker/theory_lib/$theory/examples.py
    # Test with iterations (examples have iterate settings)
    ./dev_cli.py src/model_checker/theory_lib/$theory/examples.py
done

# Performance check
time ./dev_cli.py src/model_checker/theory_lib/logos/examples.py
```

**Success Criteria**:
- [ ] BuildModule under 300 lines (from 1267)
- [ ] Clear orchestration pattern
- [ ] All tests still passing (2764+ lines)
- [ ] No performance regression
- [ ] No circular imports

**Migration Strategy**:
1. Keep static method try_single_N_static in runner.py
2. Update imports: `from model_checker.builder.module import BuildModule` → `from model_checker.builder.core import BuildModule`
3. Ensure runner has access to build_module for translation calls
4. Test iteration support thoroughly with process_example

### Phase 6: Cleanup and Integration

**Objective**: Remove duplication and integrate improvements

**Tasks**:
1. Remove graph_utils.py (use iterate/graph.py)
2. Integrate validation.py into appropriate modules
3. Update all imports throughout codebase
4. Clean up project.py interactions
5. Update __init__.py exports

**Explicit Implementation Details**:

1. **Remove Duplicate graph_utils.py**:
```bash
# Remove duplicate functionality
rm src/model_checker/builder/graph_utils.py

# Update any references to use iterate version
grep -r "builder.graph_utils" src/
# Replace with "iterate.graph"
```

2. **Integrate validation.py**:
```python
# Move validation functions to runner.py where they're used
# In runner.py, add at top:

def validate_premises_conclusions(premises, conclusions):
    """Validate that premises and conclusions are lists of strings."""
    if not isinstance(premises, list) or not isinstance(conclusions, list):
        raise ValueError("Premises and conclusions must be lists")
    
    for i, premise in enumerate(premises):
        if not isinstance(premise, str):
            raise TypeError(f"Premise {i} must be a string, got {type(premise)}")
    
    for i, conclusion in enumerate(conclusions):
        if not isinstance(conclusion, str):
            raise TypeError(f"Conclusion {i} must be a string, got {type(conclusion)}")

def validate_semantic_theory(semantic_theory, theory_name):
    """Validate semantic theory has required components."""
    required = ['semantics', 'proposition', 'model', 'operators']
    missing = [key for key in required if key not in semantic_theory]
    
    if missing:
        raise ValueError(
            f"Semantic theory '{theory_name}' missing required components: {missing}"
        )
```

3. **Update All Imports**:
```python
# Update __main__.py
from model_checker.builder.core import BuildModule  # Changed from .module

# Update iterate/build_example.py
# No changes needed - uses builder.example

# Update jupyter/interactive.py
from model_checker.builder.core import BuildModule  # Changed from .module

# Update builder/__init__.py
from model_checker.builder.core import BuildModule  # Changed from .module
from model_checker.builder.project import BuildProject
from model_checker.builder.example import BuildExample

__all__ = ['BuildModule', 'BuildProject', 'BuildExample']
```

4. **Update Import Order in New Modules**:
```python
# Ensure proper import order to avoid circular dependencies

# core.py imports (in order):
import os
import sys
import importlib.util
# NO direct imports of runner, comparison, translation here

# runner.py imports:
from model_checker.output.progress import Spinner
from model_checker.syntactic import Syntax
# Late import BuildExample where needed

# comparison.py imports:
import concurrent.futures
from model_checker.builder.serialize import serialize_semantic_theory
# NO import of BuildModule to avoid circularity

# translation.py imports:
import copy
# Minimal imports, no circular dependencies
```

5. **Test Import Structure**:
```python
# Create test_imports.py to verify no circular imports
import sys
sys.path.insert(0, 'src')

# Test each module can be imported independently
import model_checker.builder.core
import model_checker.builder.runner  
import model_checker.builder.comparison
import model_checker.builder.translation

# Test main entry points still work
from model_checker.builder import BuildModule
from model_checker.__main__ import ParseFileFlags
```

**Validation Commands**:
```bash
# Check for duplicate code
grep -n "class ModelGraph" src/model_checker/builder/
grep -n "class ModelGraph" src/model_checker/iterate/

# Verify no circular imports
python -c "import model_checker.builder"

# Character validation
grep -n '[^[:print:][:space:]]' src/model_checker/builder/

# UTF-8 encoding check
file -i src/model_checker/builder/*.py
```

**Success Criteria**:
- [ ] No duplicate code
- [ ] All circular dependencies resolved
- [ ] Clean import structure
- [ ] All imports work correctly
- [ ] No character encoding issues

### Phase 7: Documentation and Polish

**Objective**: Complete documentation and final cleanup

**Tasks**:
1. Update builder/README.md with new architecture
2. Document all public APIs
3. Add migration notes for breaking changes
4. Update all affected component documentation
5. Update spec with completion status

**Documentation Updates**:
```bash
# Update module documentation
src/model_checker/builder/README.md
src/model_checker/builder/core.py (docstrings)
src/model_checker/builder/runner.py (docstrings)
src/model_checker/builder/comparison.py (docstrings)
src/model_checker/builder/translation.py (docstrings)

# Update cross-references
grep -r "builder.module" docs/ src/
```

**Final Validation**:
```bash
# Full test suite
./run_tests.py --all --verbose

# Documentation validation
# Verify all examples in docs still work
# Check cross-references are intact
```

**Success Criteria**:
- [ ] Complete README following maintenance/README_STANDARDS.md
- [ ] All modules well-documented
- [ ] Examples updated for new APIs
- [ ] All cross-references updated
- [ ] Spec marked as IMPLEMENTED

## Phase Completion Protocol

Per IMPLEMENT.md section 4, after completing each phase:

```bash
# 1. Run comprehensive validation
./run_tests.py --all
grep -n '[^[:print:][:space:]]' src/  # Character validation

# 2. Commit phase with descriptive message
git add -A
git commit -m "Phase X Complete: [Brief description]

- [List key achievements]
- All tests passing
- No regressions detected

Next: Phase Y - [Next phase description]"

# 3. Push to remote
git push origin feature/builder-v1-refactor
```

## Testing Strategy

### Dual Testing Protocol (per IMPLEMENT.md)

Each refactoring step MUST use BOTH testing methods:

1. **Method 1 - TDD with Test Runner**:
   ```bash
   # Write tests first
   ./run_tests.py builder --verbose
   ./run_tests.py --package --components builder
   ./run_tests.py --all  # Full regression
   ```

2. **Method 2 - Direct CLI Testing**:
   ```bash
   # Test with actual theories (examples have iterate settings)
   ./dev_cli.py src/model_checker/theory_lib/logos/examples.py
   ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py
   ./dev_cli.py src/model_checker/theory_lib/exclusion/examples.py
   ./dev_cli.py src/model_checker/theory_lib/imposition/examples.py
   ```

### Regression Testing

- Maintain baseline outputs throughout
- Compare results after each phase
- Ensure no functionality lost
- Performance benchmarks maintained
- No Z3 casting errors introduced

## Risk Mitigation

### Identified Risks

1. **Breaking Iterate Integration**:
   - Mitigation: Test iterate functionality after each phase
   - Have rollback plan for each phase
   - Test iteration examples specifically

2. **Theory Loading Issues**:
   - Mitigation: Comprehensive theory loading tests
   - Verify all theories load correctly
   - Check for late import problems

3. **Output Format Changes**:
   - Mitigation: Capture output baselines
   - Ensure backward compatibility for output formats
   - Test interactive mode specifically

4. **Z3 Context Issues**:
   - Mitigation: Follow iterator's Z3 evaluation patterns
   - Test for "cannot cast to concrete Boolean" errors
   - Use explicit Z3 evaluation methods

### Debugging Philosophy (per IMPLEMENT.md)

- **Fail-Fast Strategy**: Prefer deterministic failures with helpful error messages
- **Deep Root Cause Analysis**: Trace to fundamental cause when errors occur
- **Uniform High-Quality Solutions**: Avoid cheap patches and band-aid fixes

## Success Metrics

- **Code Quality**: Reduce module.py from 1267 to ~300 lines (76% reduction)
- **Modularity**: Clean separation of concerns
- **Testing**: Maintain comprehensive test coverage (currently 11 test files)
- **Performance**: No regression in execution time
- **Documentation**: Complete and accurate
- **V1 Readiness**: Remove last major blocker for release

## Timeline

- **Day 0**: Phase 0 (Research and Design) - REQUIRED FIRST
- **Day 1**: Phase 1-2 (Test infrastructure, Runner extraction)
- **Day 2**: Phase 3-4 (Comparison and Translation extraction) 
- **Day 3**: Phase 5-6 (Core refactoring and cleanup)
- **Day 4**: Phase 7 (Documentation and polish)

Total estimated time: 5 days (including research phase)

## Implementation Tracking

### Phase Status
- [x] Phase 0: Research and Design (COMPLETED IN SPEC)
- [ ] Phase 1: Test Infrastructure and Baseline
- [ ] Phase 2: Extract Runner Module
- [ ] Phase 3: Extract Comparison Module
- [ ] Phase 4: Extract Translation Module
- [ ] Phase 5: Core Module Refactoring
- [ ] Phase 6: Cleanup and Integration
- [ ] Phase 7: Documentation and Polish

### Success Metrics Progress
- [ ] Code Quality: module.py reduced from 1267 to ~300 lines (CURRENT: 1267 lines - NO CHANGE)
- [ ] All 2764+ lines of tests passing
- [ ] No performance regression
- [ ] Documentation updated
- [ ] V1 blocker removed

### Current Implementation Status (2025-09-04)
- **NO REFACTORING HAS BEEN IMPLEMENTED**
- module.py remains at 1267 lines (unchanged from spec creation)
- No new modules created (runner.py, comparison.py, translation.py, core.py do not exist)
- All original modules present with same line counts
- Builder package remains the sole major blocker for v1 release

## Post-Implementation

After successful implementation:

1. Run comprehensive v1 readiness testing
2. Update affected documentation (especially builder/README.md)
3. Create migration guide for API changes
4. Update v1 release analysis to mark builder as complete
5. Proceed with v1 release preparation

**Context**: This refactoring removes the last major blocker for v1 release. The iterate package has been accepted in its current state (729-line core.py) after risk assessment showed further refactoring would likely break functionality. Builder has no such constraints and is safe to refactor.

## Notes

- This refactoring follows NO BACKWARDS COMPATIBILITY principle
- All changes should improve code clarity and maintainability  
- Module count is balanced between too many and too few
- Each phase is independently valuable and testable
- Builder is currently the sole major blocker for v1 release
- Unlike iterate, builder has no fragility concerns preventing refactoring
- The 19% growth in module.py size emphasizes urgency of this work

## Common Issues and Solutions (per IMPLEMENT.md)

### Z3 Boolean Evaluation Errors
```python
# WRONG - Causes "cannot cast to concrete Boolean"
if z3_expr:
    ...

# CORRECT - Explicit Z3 evaluation
if not z3.is_false(z3_expr):
    ...
```

### Import Circularity
- Move shared dependencies to separate modules
- Use proper import ordering (see CODE_ORGANIZATION.md)
- Consider interface segregation

### Test Failures After Refactoring
- Run baseline comparison before changes
- Use both testing methods to catch different issues
- Check for implicit dependencies

## Detailed Method Mapping

### Methods Moving to runner.py (~400 lines)
- `run_model_check` (lines 384-416): Main model checking entry
- `try_single_N` (lines 417-466): Single N value testing
- `try_single_N_static` (lines 467-535): Static version for multiprocessing
- `try_single_N_serialized` (lines 536-556): Serialized version
- `process_example` (lines 689-963): Full example processing with iterations
- `process_iterations` (lines 1108-1124): Iteration handling
- `_run_generator_iteration` (lines 966-1036): Generator iteration support
- `_get_termination_info` (lines 1037-1070): Iteration termination
- `_get_termination_reason` (lines 1071-1107): Termination reason formatting

### Methods Moving to comparison.py (~350 lines)
- `compare_semantics` (lines 557-637): Core comparison logic
- `run_comparison` (lines 638-665): Main comparison entry point
- Comparison output formatting logic

### Methods Moving to translation.py (~250 lines)
- `translate` (lines 333-357): Basic translation
- `translate_example` (lines 358-383): Full example translation
- `replace_operators` (nested in translate): Recursive operator replacement

### Methods Staying in core.py (~300 lines)
- `__init__` (lines 87-160): Initialization and setup
- `_discover_theory_module` (lines 46-86): Theory discovery
- `_is_generated_project` (lines 161-192): Project detection
- `_find_project_directory` (lines 193-222): Project directory location
- `_load_module` (lines 223-317): Module loading with import handling
- `_load_attribute` (lines 318-332): Attribute validation
- `run_examples` (lines 1197-end): Main orchestration
- `_capture_and_save_output` (lines 1125-1196): Output handling
- `_prompt_for_iterations` (lines 666-688): Interactive prompting
