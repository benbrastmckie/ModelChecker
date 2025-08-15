# Implementation Plan: Builder Package v1 Modular Refactor

**Date**: 2025-01-11 (Updated 2025-08-15)  
**Author**: AI Assistant  
**Status**: Ready for Implementation  
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

## Current State Analysis (Updated 2025-08-15)

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

### Phase 0: Research and Design (REQUIRED FIRST)

**Objective**: Analyze current implementation and finalize design

**Tasks**:
1. Analyze module.py to identify exact extraction boundaries
2. Map all dependencies and circular import risks
3. Document implicit contracts and coupling points
4. Create detailed extraction plan for each module
5. Identify potential Z3 evaluation issues

**Analysis Checklist**:
```bash
# Analyze current structure
grep -n "class " src/model_checker/builder/module.py
grep -n "def " src/model_checker/builder/module.py | wc -l
grep -n "import" src/model_checker/builder/*.py | grep -v tests

# Check for circular dependencies
grep -n "from model_checker" src/model_checker/builder/*.py
```

**Success Criteria**:
- [ ] Complete dependency map created
- [ ] Extraction boundaries clearly defined
- [ ] Risk areas identified and mitigation planned

### Phase 1: Test Infrastructure and Baseline

**Objective**: Establish comprehensive test baseline before refactoring

**Tasks**:
1. Create baseline captures of current behavior
2. Write comprehensive tests for module.py components
3. Document all implicit contracts and dependencies
4. Set up test infrastructure for phased refactoring

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

**Key Extractions**:
```python
# runner.py
class ModelRunner:
    """Executes model checking for theories."""
    
    def __init__(self, settings, output_manager):
        self.settings = settings
        self.output_manager = output_manager
    
    def run_model_check(self, example_case, theory_name, semantic_theory):
        """Run model checking for a single example."""
        # Extracted from BuildModule.run_model_check
    
    def _create_build_example(self, example_case, semantic_theory):
        """Create BuildExample instance."""
        # Extracted helper logic
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

**Key Components**:
```python
# comparison.py
class TheoryComparator:
    """Compares results across multiple theories."""
    
    def compare_theories(self, examples, theories):
        """Run comparison across theories."""
        # Extracted from BuildModule.run_comparison
    
    def format_comparison_results(self, results):
        """Format comparison output."""
        # Consolidated formatting logic
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

**Architecture**:
```python
# translation.py
class TheoryTranslator:
    """Handles operator translation between theories."""
    
    OPERATOR_MAPPINGS = {
        'logos': {'\\Box': 'L', '\\Diamond': 'M'},
        'bimodal': {'\\Box': '\\Box_1', '\\Diamond': '\\Diamond_1'}
    }
    
    def translate_example(self, example, target_theories):
        """Translate operators for each theory."""
        # Consolidated translation logic
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

**Final Structure**:
```python
# core.py (renamed from module.py)
class BuildModule:
    """Orchestrates model checking operations."""
    
    def __init__(self, module_flags):
        self.settings = self._process_flags(module_flags)
        self.runner = ModelRunner(self.settings, self.output_manager)
        self.comparator = TheoryComparator(self.output_manager)
        self.translator = TheoryTranslator()
    
    def run_examples(self):
        """Run all examples with proper orchestration."""
        # Simplified orchestration logic
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

### Phase 6: Cleanup and Integration

**Objective**: Remove duplication and integrate improvements

**Tasks**:
1. Remove graph_utils.py (use iterate/graph.py)
2. Integrate validation.py into appropriate modules
3. Update all imports throughout codebase
4. Clean up project.py interactions
5. Update __init__.py exports

**Integration Points**:
- Update iterate package to use builder's interfaces
- Ensure consistent validation across modules
- Remove all circular dependencies

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
- [ ] Phase 0: Research and Design
- [ ] Phase 1: Test Infrastructure and Baseline
- [ ] Phase 2: Extract Runner Module
- [ ] Phase 3: Extract Comparison Module
- [ ] Phase 4: Extract Translation Module
- [ ] Phase 5: Core Module Refactoring
- [ ] Phase 6: Cleanup and Integration
- [ ] Phase 7: Documentation and Polish

### Success Metrics Progress
- [ ] Code Quality: module.py reduced from 1267 to ~300 lines
- [ ] All 2764+ lines of tests passing
- [ ] No performance regression
- [ ] Documentation updated
- [ ] V1 blocker removed

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
