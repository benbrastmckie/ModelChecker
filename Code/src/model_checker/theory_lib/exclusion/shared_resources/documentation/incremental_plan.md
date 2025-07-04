# Incremental Model Checking Implementation Plan

## Overview

This document provides a detailed, phased implementation plan for introducing incremental model checking to the exclusion theory without disrupting other theories (especially logos). The plan creates new modules within the exclusion directory that implement the three-level integration architecture while maintaining compatibility with the existing ModelChecker framework.

## Design Constraints

1. **No External Changes**: Avoid modifying files outside `exclusion/` to preserve other theories
2. **Isolated Implementation**: Create new modules within `exclusion/attempt6_incremental/` 
3. **Framework Compatibility**: Maintain interface compatibility with existing ModelChecker patterns
4. **Testable Phases**: Each phase must be fully tested before proceeding
5. **Documentation Updates**: Documentation must be updated with each phase
6. **Future Migration**: New modules include TODOs explaining their eventual integration into core ModelChecker

## Phase Structure

Each phase follows this workflow:
1. **Implementation**: Create/modify code following the architectural design
2. **Testing**: Comprehensive testing of phase deliverables
3. **Documentation**: Update relevant documentation
4. **Commit**: Commit changes before proceeding to next phase

## Phase 1: Core Infrastructure Setup

### Objectives
- Establish basic incremental processing infrastructure
- Create foundational classes for witness tracking and truth evaluation
- Implement minimal incremental constraint builder

### Deliverables

#### 1.1 Witness Management System
**File**: `incremental/witness_store.py`

```python
# TODO: Future migration - replace witness tracking in src/model_checker/model.py
# This module provides persistent witness storage that the core ModelChecker 
# currently lacks for Skolem function interpretations

class WitnessStore:
    """Manages persistent witness information across incremental solving."""
    
class WitnessMapping:
    """Tracks individual witness function mappings."""
    
class SkolemRegistry:
    """Registry for Skolem functions with incremental access."""
```

**Purpose**: Replaces the implicit witness handling in the core framework with explicit, persistent tracking.

#### 1.2 Incremental Truth Cache
**File**: `incremental/truth_cache.py`

```python
# TODO: Future migration - enhance src/model_checker/model.py truth evaluation
# This module provides incremental truth evaluation that the core ModelChecker
# performs statically in separate phases

class TruthCache:
    """Caches partial truth evaluations during incremental solving."""
    
class VerifierCache:
    """Tracks verifier sets with dependency management."""
    
class FormulaRegistry:
    """Registry for formulas being incrementally processed."""
```

**Purpose**: Extends the core framework's truth evaluation with incremental capabilities and dependency tracking.

#### 1.3 Incremental Constraint Builder
**File**: `incremental/constraint_builder.py`

```python
# TODO: Future migration - replace static constraint generation in src/model_checker/model.py
# This module provides incremental constraint building that maintains solver state
# persistence, unlike the current batch processing approach

class ConstraintBuilder:
    """Builds constraints incrementally with immediate satisfiability checking."""
    
class SolverManager:
    """Manages persistent Z3 solver state across constraint additions."""
    
class ConstraintQueue:
    """Manages constraint dependencies and build order."""
```

**Purpose**: Replaces the core framework's `ModelConstraints.build_constraints()` with incremental, stateful constraint building.

### Testing Strategy
- Unit tests for each class in isolation
- Integration tests between witness store and truth cache
- Mock Z3 solver tests for constraint builder
- Memory leak tests for persistent state management

### Documentation Updates
- Update `incremental_modeling.md` with actual class interfaces
- Create API documentation for each module
- Update README.md with phase 1 completion status

## Phase 2: Operator Integration Architecture

### Objectives
- Extend existing operator interface for incremental support
- Implement wrapper system for backward compatibility
- Create incremental operator base classes

### Deliverables

#### 2.1 Incremental Operator Interface
**File**: `incremental/operators/base.py`

```python
# TODO: Future migration - extend src/model_checker/syntactic.py Operator class
# This module provides incremental operator capabilities that the core Operator
# class doesn't support, enabling witness-aware semantic operations

class IncrementalOperatorMixin:
    """Mixin providing incremental capabilities to existing operators."""
    
    def compute_verifiers(self, *args, witness_store, truth_cache):
        """Compute verifiers using witness information."""
        
    def evaluate_with_witnesses(self, *args, eval_point, witness_store, truth_cache):
        """Evaluate truth using available witnesses."""
        
    def has_sufficient_witnesses(self, *args, witness_store):
        """Check if witness information is complete for evaluation."""
        
    def register_witnesses(self, *args, witness_store):
        """Register witness functions for tracking."""

class OperatorAdapter:
    """Adapts existing operators for incremental processing."""
```

**Purpose**: Extends the core `syntactic.Operator` class with incremental capabilities without modifying the original.

#### 2.2 Exclusion Operator Implementation
**File**: `incremental/operators/exclusion.py`

```python
# TODO: Future migration - replace exclusion operator in exclusion/operators.py
# This module provides incremental exclusion semantics that solve the false premise
# problem through witness persistence

class ExclusionOperator(syntactic.Operator, IncrementalOperatorMixin):
    """Exclusion operator with incremental witness tracking."""

class ExclusionWitnessManager:
    """Manages h and y witness functions for exclusion semantics."""
    
class ThreeConditionEvaluator:
    """Evaluates three-condition exclusion using witness mappings."""
```

**Purpose**: Replaces the current exclusion operator with one supporting incremental witness access.

#### 2.3 Logical Operator Extensions
**File**: `incremental/operators/logical.py`

```python
# TODO: Future migration - enhance logical operators in exclusion/operators.py
# This module provides incremental support for conjunction, disjunction, and identity
# operators that interact properly with exclusion witness tracking

class UniAndOperator(syntactic.Operator, IncrementalOperatorMixin):
    """Conjunction with incremental support."""
    
class UniOrOperator(syntactic.Operator, IncrementalOperatorMixin):
    """Disjunction with incremental support."""
    
class UniIdentityOperator(syntactic.Operator, IncrementalOperatorMixin):
    """Identity with incremental support."""
```

**Purpose**: Extends existing logical operators to work within the incremental three-level architecture.

### Testing Strategy
- Operator unit tests with mock witness stores
- Integration tests between operators and witness management
- Backward compatibility tests with existing operator interface
- Cross-operator dependency tests (exclusion with conjunction)

### Documentation Updates
- Document incremental operator interface design
- Update operator documentation with new capabilities
- Create migration guide for operator extension

## Phase 3: Semantic Engine Integration

### Objectives
- Create incremental semantic engine that orchestrates three-level integration
- Implement `IncrementalProcessor` as main coordination class
- Integrate with existing semantic interface

### Deliverables

#### 3.1 Three-Level Integration Engine
**File**: `incremental/semantic_engine.py`

```python
# TODO: Future migration - replace semantic processing in src/model_checker/model.py
# This module provides three-level integration that the core ModelConstraints class
# cannot support due to its static two-phase architecture

class ThreeLevelIntegrator:
    """Coordinates syntax, truth-conditions, and extensions levels."""
    
class IncrementalProcessor:
    """Main processor for incremental model checking."""
    
    def process_incrementally(self, sentence, eval_point):
        """Process formula with circular three-level information flow."""

class LevelCoordinator:
    """Manages transitions between methodology levels."""
```

**Purpose**: Replaces the core framework's static `ModelConstraints` with incremental three-level processing.

#### 3.2 Exclusion Semantics Implementation
**File**: `incremental/semantics.py`

```python
# TODO: Future migration - replace static semantics in exclusion/semantic.py
# This module provides incremental exclusion semantics that maintain witness
# accessibility across the three-level methodology

class ExclusionSemantics(ModelDefaults):
    """Exclusion semantics with incremental verification."""
    
    def verify_formula(self, sentence, eval_point):
        """Main entry point for incremental verification."""
        
    def true_at(self, sentence, eval_point):
        """Backward-compatible truth evaluation with incremental support."""
        
    def extended_verify(self, state, sentence, eval_point):
        """Backward-compatible verification with witness registration."""

class IncrementalModelStructure:
    """Model structure supporting incremental witness access."""
```

**Purpose**: Provides incremental exclusion semantics while maintaining interface compatibility with existing theory structure.

#### 3.3 Framework Integration Layer
**File**: `incremental/framework_adapter.py`

```python
# TODO: Future migration - enhance theory loading in src/model_checker/utils.py
# This module provides seamless integration with the existing ModelChecker framework
# without requiring changes to core theory loading mechanisms

class TheoryAdapter:
    """Adapts incremental semantics to ModelChecker framework expectations."""
    
class ExampleRunner:
    """Runs incremental examples through existing dev_cli.py interface."""
    
class FrameworkBridge:
    """Bridges incremental processing with static framework expectations."""
```

**Purpose**: Ensures incremental implementation works with existing `dev_cli.py` and theory loading without framework modifications.

### Testing Strategy
- End-to-end tests with complete exclusion examples
- Framework integration tests via `dev_cli.py`
- Performance comparison tests (incremental vs static)
- Regression tests ensuring non-exclusion theories unaffected

### Documentation Updates
- Complete API documentation for semantic engine
- Update examples documentation showing incremental processing
- Performance analysis and comparison documentation

## Phase 4: Example Implementation and Testing

### Objectives
- Implement complete exclusion examples using incremental processing
- Create comprehensive test suite comparing static vs incremental results
- Demonstrate false premise resolution

### Deliverables

#### 4.1 Incremental Examples
**File**: `incremental/examples.py`

```python
# TODO: Future migration - replace exclusion/examples.py with incremental version
# This module demonstrates incremental exclusion semantics solving the false premise
# problem that the static examples in exclusion/examples.py exhibit

def incremental_examples():
    """Complete set of exclusion examples using incremental processing."""
    
def double_negation_incremental():
    """Double negation example with true premises."""
    
def demorgans_incremental():
    """DeMorgan's laws with correct premise evaluation."""
    
def complex_exclusion_incremental():
    """Complex exclusion formulas demonstrating witness tracking."""
```

**Purpose**: Replaces problematic static examples with working incremental versions.

#### 4.2 Comparative Test Suite
**File**: `incremental/tests/comparison_tests.py`

```python
class IncrementalVsStaticTests:
    """Comprehensive comparison between static and incremental approaches."""
    
    def test_premise_evaluation_accuracy(self):
        """Verify incremental approach resolves false premise issues."""
        
    def test_witness_accessibility(self):
        """Verify witness functions remain accessible."""
        
    def test_performance_characteristics(self):
        """Compare processing speed and memory usage."""

class RegressionTests:
    """Ensure incremental changes don't break working examples."""
```

#### 4.3 Integration Test Framework
**File**: `incremental/tests/integration_tests.py`

```python
class FrameworkIntegrationTests:
    """Test integration with existing ModelChecker infrastructure."""
    
    def test_dev_cli_compatibility(self):
        """Verify examples run through dev_cli.py."""
        
    def test_other_theories_unaffected(self):
        """Verify logos and other theories continue working."""
        
    def test_backward_compatibility(self):
        """Verify existing exclusion interface still works."""
```

### Testing Strategy
- Automated false premise detection tests
- Performance benchmarking against static implementation
- Memory usage analysis for long-running incremental processes
- Cross-platform compatibility tests

### Documentation Updates
- Complete test results documentation
- Performance analysis report
- Troubleshooting guide for common issues
- Migration guide from static to incremental

## Phase 5: Production Readiness and Optimization

### Objectives
- Optimize incremental processing for production use
- Create comprehensive documentation and examples
- Establish migration path for future core integration

### Deliverables

#### 5.1 Performance Optimization
**File**: `incremental/optimization/`

```python
# TODO: Future migration - performance optimizations for core ModelChecker
# These modules provide optimized incremental processing that could enhance
# the core framework's constraint solving and truth evaluation performance

# optimization/solver_tuning.py
class SolverOptimizer:
    """Z3 solver optimization for incremental processing."""

# optimization/witness_compression.py  
class WitnessCompressor:
    """Compress witness storage for memory efficiency."""

# optimization/constraint_scheduling.py
class ConstraintScheduler:
    """Optimize constraint building order for performance."""
```

#### 5.2 Production Configuration
**File**: `incremental/config.py`

```python
# TODO: Future migration - configuration system for src/model_checker/
# This module provides configuration management that the core framework
# lacks for tuning incremental processing parameters

class IncrementalConfig:
    """Configuration for incremental processing parameters."""
    
class PerformanceTuning:
    """Performance tuning parameters for different use cases."""
    
class DebuggingConfig:
    """Configuration for debugging incremental processing."""
```

#### 5.3 Migration Documentation
**File**: `incremental/MIGRATION.md`

Complete migration guide including:
- Core framework integration points
- Required changes to `src/model_checker/`
- Backward compatibility strategies
- Performance impact analysis
- Timeline for full integration

### Testing Strategy
- Load testing with large formula sets
- Long-running stability tests
- Memory leak detection
- Production environment simulation

### Documentation Updates
- Complete user guide for incremental exclusion theory
- Developer guide for extending incremental capabilities
- Performance tuning guide
- Production deployment guide

## Success Criteria

### Phase-by-Phase Criteria

**Phase 1**: Infrastructure classes implemented and unit tested
**Phase 2**: Operators working with witness tracking, integration tests passing
**Phase 3**: Complete incremental semantic engine, framework integration working
**Phase 4**: All exclusion examples working with true premises, comparison tests passing
**Phase 5**: Production-ready implementation with comprehensive documentation

### Overall Success Metrics

1. **False Premise Resolution**: All previously problematic examples (¬¬A, DeMorgan's laws) have true premises
2. **Performance Acceptability**: Incremental processing d 3x slower than static for comparable examples
3. **Framework Compatibility**: `dev_cli.py` works seamlessly with incremental examples
4. **Isolation Success**: No impact on logos or other theories
5. **Test Coverage**: >90% test coverage for all incremental modules
6. **Documentation Completeness**: Complete API documentation and user guides

## Risk Mitigation

### Technical Risks
- **Performance degradation**: Addressed through Phase 5 optimization
- **Memory leaks**: Mitigated through persistent state testing in Phase 1
- **Framework incompatibility**: Addressed through adapter pattern in Phase 3

### Project Risks
- **Scope creep**: Strict phase boundaries with commit requirements
- **Integration complexity**: Isolated implementation with no external dependencies
- **Backward compatibility**: Adapter layers maintain existing interfaces

## Timeline Estimate

- **Phase 1**: 2-3 weeks (Infrastructure)
- **Phase 2**: 3-4 weeks (Operators)  
- **Phase 3**: 4-5 weeks (Semantic Engine)
- **Phase 4**: 2-3 weeks (Examples & Testing)
- **Phase 5**: 2-3 weeks (Production Readiness)

**Total**: 13-18 weeks for complete incremental implementation

## Conclusion

This phased approach provides a systematic path to implementing incremental model checking within the exclusion theory while maintaining complete isolation from other framework components. Each phase builds upon the previous while maintaining testability and documentation requirements. The extensive use of TODO comments in new modules provides a clear migration path for eventual core framework integration.

The incremental architecture addresses the fundamental three-level integration problem that causes false premises in exclusion semantics, while the phased implementation approach ensures stability and maintainability throughout the development process.