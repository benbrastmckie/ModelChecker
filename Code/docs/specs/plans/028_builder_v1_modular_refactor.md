# Implementation Plan: Builder Package v1 Modular Refactor

**Date**: 2025-01-11  
**Author**: AI Assistant  
**Status**: Ready for Implementation  
**Priority**: High  
**Focus**: Refactor builder package for v1 release with improved modularity

## Executive Summary

This plan refactors the builder package from its current monolithic structure (module.py: 1063 lines) into a well-organized modular architecture. Learning from the successful iterate refactoring, this plan emphasizes **breaking compatibility for cleaner architecture**, **module consolidation to avoid fragmentation**, and **comprehensive testing at each phase**.

## Current State Analysis

### Module Overview
```
builder/
├── module.py (1063 lines) - MONOLITHIC: Running, comparison, translation, I/O
├── project.py (526 lines) - Mixed project management and execution
├── example.py (320 lines) - Core BuildExample class
├── graph_utils.py (315 lines) - DUPLICATE of iterate functionality
├── z3_utils.py (114 lines) - Z3 model utilities
├── validation.py (105 lines) - Parameter validation
├── progress.py (57 lines) - Progress tracking
└── tests/ - Comprehensive test suite
```

### Key Issues

1. **Mixed Responsibilities in module.py**:
   - Model checking execution
   - Theory comparison logic
   - Theory translation
   - File I/O operations
   - Result formatting

2. **Duplication**:
   - graph_utils.py duplicates iterate/graph.py functionality
   - Validation logic scattered across modules

3. **Circular Dependencies**:
   - Late imports throughout to avoid circular references
   - Complex dependency on models and syntactic packages

4. **Large Methods**:
   - Several methods exceed 100 lines
   - Complex nested logic in run_comparison()

## Design Philosophy

Following successful patterns from iterate refactoring:

1. **NO BACKWARDS COMPATIBILITY**: Break interfaces freely for cleaner architecture
2. **Module Consolidation**: Combine related functionality to avoid too many small files
3. **Clear Separation**: Each module has a single, well-defined responsibility
4. **Test-Driven Development**: Write tests before refactoring each component
5. **Unified Interfaces**: Ensure consistent patterns across all modules

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

**Module Count**: 9 core modules (removing graph_utils.py duplicate, integrating validation.py)

## Implementation Phases

### Phase 1: Test Infrastructure and Baseline (Day 1)

**Objective**: Establish comprehensive test baseline before refactoring

**Tasks**:
1. Create baseline captures of current behavior
2. Write comprehensive tests for module.py components
3. Document all implicit contracts and dependencies
4. Set up test infrastructure for phased refactoring

**Tests to Write**:
```python
# tests/test_baseline.py - Capture current behavior
# tests/test_runner.py - Test model checking execution
# tests/test_comparison.py - Test theory comparison
# tests/test_translation.py - Test operator translation
```

**Success Criteria**:
- [ ] 100% test coverage for public interfaces
- [ ] Baseline behavior documented
- [ ] All existing tests passing

### Phase 2: Extract Runner Module (Day 1-2)

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

**Success Criteria**:
- [ ] All model checking tests pass
- [ ] No circular imports
- [ ] Clean separation from BuildModule

### Phase 3: Extract Comparison Module (Day 2)

**Objective**: Separate theory comparison logic

**Tasks**:
1. Create comparison.py with TheoryComparator class
2. Move run_comparison and comparison formatting
3. Extract comparison statistics logic
4. Clean up comparison output generation

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

**Success Criteria**:
- [ ] Comparison functionality preserved
- [ ] Cleaner output formatting
- [ ] Reusable comparison logic

### Phase 4: Extract Translation Module (Day 2-3)

**Objective**: Isolate theory operator translation

**Tasks**:
1. Create translation.py with TheoryTranslator class
2. Move translate_example and operator mappings
3. Consolidate translation logic from multiple locations
4. Add comprehensive translation tests

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

**Success Criteria**:
- [ ] All theories translate correctly
- [ ] No hardcoded theory names in core
- [ ] Extensible translation system

### Phase 5: Core Module Refactoring (Day 3)

**Objective**: Refactor BuildModule to orchestration role only

**Tasks**:
1. Remove all extracted functionality
2. Update BuildModule to use new modules
3. Simplify initialization and configuration
4. Clean up file I/O operations

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

**Success Criteria**:
- [ ] BuildModule under 400 lines
- [ ] Clear orchestration pattern
- [ ] All tests still passing

### Phase 6: Cleanup and Integration (Day 3-4)

**Objective**: Remove duplication and integrate improvements

**Tasks**:
1. Remove graph_utils.py (use iterate/graph.py)
2. Integrate validation.py into appropriate modules
3. Update all imports throughout codebase
4. Clean up project.py interactions

**Integration Points**:
- Update iterate package to use builder's interfaces
- Ensure consistent validation across modules
- Remove all circular dependencies

**Success Criteria**:
- [ ] No duplicate code
- [ ] All circular dependencies resolved
- [ ] Clean import structure

### Phase 7: Documentation and Polish (Day 4)

**Objective**: Complete documentation and final cleanup

**Tasks**:
1. Update builder/README.md with new architecture
2. Document all public APIs
3. Add migration notes for breaking changes
4. Update all affected component documentation

**Documentation Updates**:
- Module-level docstrings
- Public API documentation
- Usage examples for new structure
- Cross-references to related packages

**Success Criteria**:
- [ ] Complete README following standards
- [ ] All modules well-documented
- [ ] Examples updated for new APIs

## Testing Strategy

### Dual Testing Protocol

Following successful iterate refactoring approach:

1. **Test Runner Method**:
   ```bash
   ./run_tests.py builder --verbose
   ./run_tests.py --package --components builder
   ```

2. **Direct CLI Testing**:
   ```bash
   # Test with actual theories (examples have iterate=2 built-in)
   ./dev_cli.py src/model_checker/theory_lib/logos/examples.py
   ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py
   ```

### Regression Testing

- Maintain baseline outputs throughout
- Compare results after each phase
- Ensure no functionality lost
- Performance benchmarks maintained

## Risk Mitigation

### Identified Risks

1. **Breaking Iterate Integration**:
   - Mitigation: Test iterate functionality after each phase
   - Have rollback plan for each phase

2. **Theory Loading Issues**:
   - Mitigation: Comprehensive theory loading tests
   - Verify all theories load correctly

3. **Output Format Changes**:
   - Mitigation: Capture output baselines
   - Ensure backward compatibility for output formats

## Success Metrics

- **Code Quality**: 50% reduction in module.py size
- **Modularity**: Clean separation of concerns
- **Testing**: 95%+ test coverage maintained
- **Performance**: No regression in execution time
- **Documentation**: Complete and accurate

## Timeline

- **Day 1**: Phase 1-2 (Test infrastructure, Runner extraction)
- **Day 2**: Phase 3-4 (Comparison and Translation extraction)
- **Day 3**: Phase 5-6 (Core refactoring and cleanup)
- **Day 4**: Phase 7 (Documentation and polish)

Total estimated time: 4 days

## Post-Implementation

After successful implementation:

1. Run comprehensive v1 readiness testing
2. Update affected documentation
3. Create migration guide for API changes
4. Consider further optimizations based on new structure

## Notes

- This refactoring follows NO BACKWARDS COMPATIBILITY principle
- All changes should improve code clarity and maintainability
- Module count is balanced between too many and too few
- Each phase is independently valuable and testable
