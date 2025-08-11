# BuildExample Iterator Integration Plan

**Date**: 2025-01-11  
**Author**: AI Assistant  
**Status**: Planning  
**Priority**: High - Eliminate code duplication in iteration  
**Context**: Ensure theory-specific concepts stay in theory_lib  
**Protocol**: IMPLEMENT.md focused execution  
**Type**: Major Refactoring - Theory Isolation and Code Deduplication

## Table of Contents
1. [Executive Summary](#executive-summary)
2. [Problem Statement](#problem-statement)
3. [Root Cause Analysis](#root-cause-analysis)
4. [Proposed Solution](#proposed-solution)
5. [Implementation Phases](#implementation-phases)
6. [Testing Strategy](#testing-strategy)
7. [Risk Mitigation](#risk-mitigation)
8. [Success Criteria](#success-criteria)
9. [Timeline](#timeline)
10. [Validation Checklist](#validation-checklist)
11. [Architecture Benefits](#architecture-benefits)
12. [Research and Analysis](#research-and-analysis)
13. [Implementation Dependencies](#implementation-dependencies)
14. [Performance Considerations](#performance-considerations)
15. [Documentation Requirements](#documentation-requirements)  

## Executive Summary

This revised plan creates a dependent IteratorBuildExample class in the iterate package to support model iteration, eliminating the 600+ lines of duplicated model building logic in iterate/core.py. **Critically, all theory-specific concepts (states, worlds, verify, falsify, possible) remain exclusively in theory_lib packages.**

## Problem Statement

### Current Issues

1. **Code Duplication**: Model building logic exists in both:
   - `BuildExample.__init__()` (lines 105-130) - Initial model creation
   - `BaseModelIterator._build_new_model_structure()` (lines 520-656) - Iteration model creation
   - ~600 lines of duplicated logic with slight variations

2. **Theory Concepts in Core**: core.py contains theory-specific concepts that violate separation:
   - `is_world(state)`, `possible(state)` - Theory-specific predicates
   - `verify(state, atom)`, `falsify(state, atom)` - Logos-specific relations
   - State representation assumptions (`2**semantics.N`) - Not all theories use bit vectors
   - These concepts assume hyperintensional semantics not shared by all theories

3. **Maintenance Burden**: 
   - Changes to model building require updates in two places
   - Risk of divergence between initial and iteration model building
   - Test synchronization complexity (test_model_building_sync.py)

4. **Architectural Violations**:
   - Core packages should be theory-agnostic
   - Theory-specific logic belongs exclusively in theory_lib
   - Current structure makes adding new theories harder

## Root Cause Analysis

### Deep Analysis

The root cause stems from two architectural decisions:

1. **Historical Evolution**: The iterator was developed after BuildExample, leading to reimplementation rather than reuse
2. **Z3 Injection Timing**: MODEL 2+ requires injecting Z3 values at a specific point in construction:
   - After creating syntax/semantics/constraints
   - Before creating the model structure
   - This timing requirement led to duplicating the entire process

### Pattern Recognition

This duplication pattern indicates a missing abstraction - the ability to create models with pre-existing constraints. The current approach violates DRY (Don't Repeat Yourself) and improperly couples theory concepts to core infrastructure.

### Architectural Impact

The current structure:
- Makes it difficult to add new theories (must update core.py)
- Increases maintenance burden
- Violates the principle that theory-specific code stays in theory_lib
- Creates risk of subtle bugs when the two implementations diverge

## Maintenance Standards Compliance

### Key Standards from Code/maintenance/

1. **NO DECORATORS** (CLAUDE.md, IMPLEMENT.md)
   - No @abstractmethod, @classmethod, @staticmethod
   - Use explicit NotImplementedError for abstract methods
   - Use module-level functions instead of class methods

2. **Testing Protocol** (IMPLEMENT.md §Testing Protocol)
   - MUST use BOTH testing methods for each phase
   - Method 1: TDD with test runner
   - Method 2: Direct CLI testing with dev_cli.py
   - Write tests BEFORE implementation

3. **No Backwards Compatibility** (CLAUDE.md)
   - Break compatibility freely for cleaner architecture
   - Never add optional parameters for legacy support
   - Remove old code immediately

4. **Theory Isolation** (Project Architecture)
   - Theory concepts ONLY in theory_lib
   - Core packages must be theory-agnostic
   - No assumptions about model structure

## Proposed Solution

### Design Principles

1. **Separation of Concerns**: 
   - BuildExample remains focused on initial model building
   - IteratorBuildExample handles iteration-specific model creation
   - Theory semantics handle all theory-specific injection

2. **Theory Isolation**: 
   - ALL theory-specific concepts (states, worlds, verify, etc.) stay in theory_lib
   - Core packages remain completely theory-agnostic
   - No assumptions about model structure outside theories

3. **No Decorators or Class Methods**: 
   - Following CLAUDE.md and IMPLEMENT.md guidelines:
     - NO decorators (@abstractmethod, @classmethod, @staticmethod)
     - NO class methods - use regular functions or instance methods
   - Use explicit inheritance and method calls
   - Clear, debuggable code paths
   - Factory functions at module level, not class methods

4. **Clean Dependencies**:
   - One-way: iterate → builder → models → theory_lib
   - No circular dependencies
   - No backward references

5. **Extensibility**:
   - Easy to add new theories (just implement inject_z3_model_values)
   - Iterator features can be enhanced without touching builder
   - Clear extension points

### High-Level Architecture

```
Current Architecture (Problematic):
┌─────────────────┐
│ BuildExample    │ → Creates MODEL 1
└─────────────────┘
┌─────────────────────────────────┐
│ BaseModelIterator               │ → Duplicates BuildExample logic
│ - Knows about worlds, states    │ → Contains theory-specific code
│ - 600+ lines of duplication     │ → Creates MODEL 2+
└─────────────────────────────────┘

Proposed Architecture (Clean):
┌─────────────────┐
│ BuildExample    │ → Creates MODEL 1 (unchanged)
└─────────────────┘
         ↑
         │ extends
┌─────────────────────┐
│ IteratorBuildExample│ → Reuses BuildExample logic
│ (theory-agnostic)   │ → Adds Z3 injection capability
└─────────────────────┘
         ↓ delegates
┌─────────────────┐
│ ModelConstraints │ → Provides injection hook
│ (delegation only)│ → NO theory logic
└─────────────────┘
         ↓ delegates
┌─────────────────┐
│ Theory Semantics │ → Contains ALL theory-specific logic
│ (in theory_lib) │ → Handles worlds, states, verify, etc.
└─────────────────┘
```

### Detailed Component Interactions

1. **BaseModelIterator** imports and calls `create_with_z3_model()` function
2. **create_with_z3_model** function:
   - Creates IteratorBuildExample instance
   - Copies attributes from original BuildExample
   - Creates fresh syntax/semantics/constraints (all theory-agnostic)
   - Calls `model_constraints.inject_z3_values(z3_model)`
3. **ModelConstraints** delegates to theory: `semantics.inject_z3_model_values()`
4. **Theory Semantics** performs all theory-specific injection
5. Model structure is created with injected constraints

## Implementation Phases

### Phase 1: Add Injection Hook to ModelConstraints

**Goal**: Enable ModelConstraints to delegate Z3 injection to theory-specific code.

**Rationale**: ModelConstraints is the bridge between syntax/semantics and model structure. Adding a delegation hook here allows theories to inject values without core packages knowing theory details.

**Tasks**:
1. Add `inject_z3_values()` method that delegates to semantics
2. Ensure NO theory-specific logic in the method
3. Update ModelConstraints docstring to document the hook
4. Add unit tests for delegation behavior

**File**: `src/model_checker/models/constraints.py`

```python
def inject_z3_values(self, z3_model):
    """Delegate Z3 value injection to theory-specific semantics.
    
    This method provides a hook for theories to inject concrete
    values from iteration. The actual injection logic MUST be
    implemented in the theory's semantics class.
    
    This method contains NO theory-specific logic and makes NO
    assumptions about model structure, states, worlds, or any
    other theory concepts.
    
    Args:
        z3_model: Z3 model with concrete values from iteration
        
    Note:
        The semantics.inject_z3_model_values method receives both
        the z3_model and self (ModelConstraints) to allow updating
        the constraint list.
    """
    # Store for potential use by model structure
    self.injected_z3_model = z3_model
    
    # Delegate to theory-specific injection if available
    if hasattr(self.semantics, 'inject_z3_model_values'):
        # Pass self so semantics can update constraints
        self.semantics.inject_z3_model_values(z3_model, self)
    # No else - if theory doesn't implement injection, nothing happens
```

**Test Implementation**:
```python
# src/model_checker/models/tests/test_constraints_injection.py
import unittest
from unittest.mock import Mock, MagicMock
from model_checker.models.constraints import ModelConstraints

class TestConstraintsInjection(unittest.TestCase):
    """Test Z3 injection delegation in ModelConstraints."""
    
    def test_inject_z3_values_delegates_to_semantics(self):
        """Test that injection delegates to semantics if available."""
        # Create mock semantics with injection method
        mock_semantics = Mock()
        mock_semantics.inject_z3_model_values = Mock()
        
        # Create ModelConstraints with mock
        settings = {'N': 3}
        syntax = Mock()
        proposition = Mock()
        constraints = ModelConstraints(settings, syntax, mock_semantics, proposition)
        
        # Call injection
        mock_z3_model = Mock()
        constraints.inject_z3_values(mock_z3_model)
        
        # Verify delegation
        mock_semantics.inject_z3_model_values.assert_called_once_with(
            mock_z3_model, constraints
        )
        
        # Verify z3_model stored
        self.assertEqual(constraints.injected_z3_model, mock_z3_model)
    
    def test_inject_z3_values_no_delegation_if_not_supported(self):
        """Test graceful handling when semantics doesn't support injection."""
        # Create mock semantics without injection method
        mock_semantics = Mock(spec=[])  # No methods
        
        # Create ModelConstraints
        constraints = ModelConstraints({}, Mock(), mock_semantics, Mock())
        
        # Should not raise error
        mock_z3_model = Mock()
        constraints.inject_z3_values(mock_z3_model)
        
        # Z3 model still stored
        self.assertEqual(constraints.injected_z3_model, mock_z3_model)
    
    def test_no_theory_concepts_in_injection(self):
        """Verify inject_z3_values contains no theory-specific concepts."""
        import inspect
        source = inspect.getsource(ModelConstraints.inject_z3_values)
        
        # These theory concepts should NOT appear
        forbidden_concepts = [
            'is_world', 'possible', 'verify', 'falsify',
            'state', 'N', 'atom', 'sentence_letter'
        ]
        
        for concept in forbidden_concepts:
            self.assertNotIn(concept, source,
                f"Theory concept '{concept}' found in inject_z3_values")
```

**Success Criteria**:
- Method delegates correctly when semantics supports injection
- Method handles gracefully when semantics doesn't support injection  
- No theory-specific concepts in the implementation
- All tests pass

### Phase 2: Create IteratorBuildExample Class

**Goal**: Create dependent class that extends BuildExample for iteration support.

**Rationale**: By extending BuildExample in the iterate package, we maintain separation of concerns while reusing all model building logic. This avoids duplication and keeps iteration-specific code in the iterate package.

**Tasks**:
1. Create new file `iterate/build_example.py`
2. Implement IteratorBuildExample extending BuildExample
3. Add factory method `create_with_z3_model`
4. Implement helper methods for copying and building
5. Add comprehensive tests

**File**: `src/model_checker/iterate/build_example.py` (new file)

```python
"""BuildExample extension for model iteration support.

This module provides IteratorBuildExample which extends BuildExample
to support creating models with pre-existing Z3 values during iteration.
This class is completely theory-agnostic - all theory-specific logic
is delegated to the theory's semantics class.
"""

from model_checker.builder.example import BuildExample
from model_checker.syntactic import Syntax
from model_checker.models.constraints import ModelConstraints

class IteratorBuildExample(BuildExample):
    """Extended BuildExample with iteration support.
    
    This class adds methods for creating models during iteration
    with pre-existing Z3 values. It remains completely theory-agnostic,
    delegating all theory-specific injection to the semantics classes.
    
    The class uses a factory pattern to create instances without going
    through the normal BuildExample initialization, allowing precise
    control over the model building process for iteration.
    """
    
    def __init__(self):
        """Initialize without calling BuildExample.__init__.
        
        This empty init is intentional - we use factory methods to
        create properly initialized instances.
        """
        pass
    
    @classmethod
    def create_with_z3_model(cls, original_build, z3_model):
        """Create a new model structure with Z3 value injection.
        
        This factory method creates a new IteratorBuildExample instance
        that reuses the configuration from an original BuildExample but
        creates a new model with specific Z3 values injected.
        
        Args:
            original_build: Original BuildExample with initial model
            z3_model: Z3 model with concrete values to inject
            
        Returns:
            IteratorBuildExample instance with new model structure
            
        Note:
            This method is completely theory-agnostic. All theory-specific
            injection logic is handled by the theory's semantics class.
        """
        # Create instance without normal initialization
        instance = cls.__new__(cls)
        
        # Copy configuration from original
        instance._copy_from_original(original_build)
        
        # Build new model with Z3 injection
        instance._build_with_injection(z3_model)
        
        return instance
    
    def _copy_from_original(self, original):
        """Copy necessary attributes from original BuildExample.
        
        This copies all the configuration needed to build a new model
        while avoiding any mutable state that could cause issues.
        
        Args:
            original: Original BuildExample to copy from
        """
        # Copy immutable configuration
        self.build_module = original.build_module
        self.semantic_theory = original.semantic_theory
        self.semantics = original.semantics
        self.proposition = original.proposition
        self.operators = original.operators
        self.model_structure_class = original.model_structure_class
        
        # Copy example definition
        self.premises = original.premises
        self.conclusions = original.conclusions
        
        # Deep copy settings to avoid mutation
        self.settings = original.settings.copy()
        
        # Copy settings manager for validation
        self.settings_manager = original.settings_manager
        
        # Store reference to original for debugging
        self._original_build = original
    
    def _build_with_injection(self, z3_model):
        """Build model structure with Z3 value injection.
        
        This creates all fresh components and delegates injection
        to the theory-specific semantics class.
        
        Args:
            z3_model: Z3 model with values to inject
        """
        # Create fresh syntax (reuses sentence parsing)
        self.example_syntax = Syntax(
            self.premises,
            self.conclusions,
            self.operators
        )
        
        # Create fresh semantics instance
        self.example_semantics = self.semantics(self.settings)
        
        # Create model constraints
        self.model_constraints = ModelConstraints(
            self.settings,
            self.example_syntax,
            self.example_semantics,
            self.proposition
        )
        
        # Delegate injection to theory-specific code
        # This is where theory concepts are handled
        self.model_constraints.inject_z3_values(z3_model)
        
        # Create model structure with injected constraints
        self.model_structure = self.model_structure_class(
            self.model_constraints,
            self.settings
        )
        
        # Store Z3 model for reference
        self.model_structure.z3_model = z3_model
        
        # Mark as iteration model for debugging
        self.model_structure._is_iteration_model = True
        
        # Interpret sentences in the new model
        self._interpret_sentences()
    
    def _interpret_sentences(self):
        """Interpret sentences in the new model structure.
        
        This finalizes the model by interpreting all sentences
        according to the injected values.
        """
        sentence_objects = (self.model_structure.premises + 
                          self.model_structure.conclusions)
        self.model_structure.interpret(sentence_objects)
        
        # Store solver reference as BuildExample does
        self.solver = self.model_structure.solver
```

**Test Implementation**:
```python
# src/model_checker/iterate/tests/test_build_example.py
import unittest
from unittest.mock import Mock, patch
import z3
from model_checker.iterate.build_example import IteratorBuildExample
from model_checker.builder.example import BuildExample

class TestIteratorBuildExample(unittest.TestCase):
    """Test IteratorBuildExample functionality."""
    
    def setUp(self):
        """Create mock BuildExample for testing."""
        self.mock_build = Mock(spec=BuildExample)
        self.mock_build.semantic_theory = {
            'semantics': Mock,
            'model': Mock,
            'proposition': Mock
        }
        self.mock_build.semantics = Mock
        self.mock_build.proposition = Mock
        self.mock_build.operators = {}
        self.mock_build.model_structure_class = Mock
        self.mock_build.premises = ['A', 'B']
        self.mock_build.conclusions = ['C']
        self.mock_build.settings = {'N': 3}
        self.mock_build.settings_manager = Mock()
        self.mock_build.build_module = Mock()
    
    def test_create_with_z3_model(self):
        """Test factory function creates proper instance."""
        mock_z3_model = Mock()
        
        # Create instance
        from model_checker.iterate.build_example import create_with_z3_model
        iter_build = create_with_z3_model(
            self.mock_build, mock_z3_model
        )
        
        # Verify instance created
        self.assertIsInstance(iter_build, IteratorBuildExample)
        
        # Verify model structure created
        self.assertIsNotNone(iter_build.model_structure)
        
        # Verify Z3 model stored
        self.assertEqual(iter_build.model_structure.z3_model, mock_z3_model)
    
    def test_theory_agnostic_implementation(self):
        """Verify no theory concepts in IteratorBuildExample."""
        import inspect
        source = inspect.getsource(IteratorBuildExample)
        
        # Theory concepts that should NOT appear
        forbidden = [
            'is_world', 'possible', 'verify', 'falsify',
            'states', '2**', 'atom', 'sentence_letter'
        ]
        
        for concept in forbidden:
            self.assertNotIn(concept, source,
                f"Theory concept '{concept}' found in IteratorBuildExample")
    
    @patch('model_checker.iterate.build_example.ModelConstraints')
    def test_injection_delegation(self, mock_constraints_class):
        """Test that injection is delegated to ModelConstraints."""
        mock_z3_model = Mock()
        mock_constraints = Mock()
        mock_constraints_class.return_value = mock_constraints
        
        # Create instance
        from model_checker.iterate.build_example import create_with_z3_model
        iter_build = create_with_z3_model(
            self.mock_build, mock_z3_model
        )
        
        # Verify injection was called
        mock_constraints.inject_z3_values.assert_called_once_with(mock_z3_model)
```

**Success Criteria**:
- IteratorBuildExample successfully extends BuildExample
- Factory function creates working instances (NOT class method)
- Z3 injection properly delegated
- No theory-specific concepts in implementation
- No decorators or class methods used
- All tests pass

### Phase 3: Add Theory-Specific Injection Methods

**Goal**: Move ALL theory-specific injection logic to theory semantics classes.

**Rationale**: Each theory knows its own structure (states, worlds, relations). By moving injection logic to theory semantics, we ensure proper encapsulation and make it easy to add new theories.

**Tasks**:
1. Add `inject_z3_model_values` to each theory's semantics class
2. Move theory-specific logic from core.py to appropriate theory
3. Ensure each implementation handles its unique concepts
4. Add tests for each theory's injection

**Example - Logos Theory**:

**File**: `src/model_checker/theory_lib/logos/semantic.py`

```python
class LogosSemantics(SemanticDefaults):
    """Logos theory semantics with hyperintensional state spaces."""
    
    def inject_z3_model_values(self, z3_model, model_constraints):
        """Inject Z3 values for Logos theory iteration.
        
        This method contains ALL the Logos-specific logic for extracting
        values from a Z3 model and constraining the new model to match
        those values. This includes:
        - World and possible state assignments
        - Verify/falsify relations for atomic sentences
        - Any other Logos-specific constraints
        
        Args:
            z3_model: Z3 model from iteration with concrete values
            model_constraints: ModelConstraints instance to update
            
        Note:
            This method encapsulates all knowledge about Logos theory
            structure, keeping it out of the core iteration framework.
        """
        # Create temporary solver to build up constraints
        temp_solver = z3.Solver()
        
        # Start with existing base constraints
        for constraint in model_constraints.all_constraints:
            temp_solver.add(constraint)
        
        # Logos-specific: constrain worlds and possible states
        # This knowledge about state representation belongs here
        for state in range(2**self.N):
            # Extract world value from iterator's model
            is_world_val = self._evaluate_z3_boolean(z3_model, self.is_world(state))
            if is_world_val:
                temp_solver.add(self.is_world(state))
            else:
                temp_solver.add(z3.Not(self.is_world(state)))
            
            # Extract possible value
            is_possible_val = self._evaluate_z3_boolean(z3_model, self.possible(state))
            if is_possible_val:
                temp_solver.add(self.possible(state))
            else:
                temp_solver.add(z3.Not(self.possible(state)))
        
        # Logos-specific: constrain verify/falsify relations
        for letter_obj in model_constraints.syntax.sentence_letters:
            atom = getattr(letter_obj, 'sentence_letter', None)
            if atom is not None:
                for state in range(2**self.N):
                    # Verify relation
                    verify_val = self._evaluate_z3_boolean(
                        z3_model, self.verify(state, atom)
                    )
                    if verify_val:
                        temp_solver.add(self.verify(state, atom))
                    else:
                        temp_solver.add(z3.Not(self.verify(state, atom)))
                    
                    # Falsify relation
                    falsify_val = self._evaluate_z3_boolean(
                        z3_model, self.falsify(state, atom)
                    )
                    if falsify_val:
                        temp_solver.add(self.falsify(state, atom))
                    else:
                        temp_solver.add(z3.Not(self.falsify(state, atom)))
        
        # Update model_constraints with all injected constraints
        model_constraints.all_constraints = list(temp_solver.assertions())
    
    def _evaluate_z3_boolean(self, z3_model, expression):
        """Evaluate Z3 expression to boolean using model.
        
        Args:
            z3_model: Z3 model for evaluation
            expression: Z3 expression to evaluate
            
        Returns:
            bool: The boolean value of the expression
        """
        from model_checker.iterate.validation import ModelValidator
        return ModelValidator.evaluate_z3_boolean(z3_model, expression)
```

**Example - Exclusion Theory**:

**File**: `src/model_checker/theory_lib/exclusion/semantic.py`

```python
class ExclusionSemantics(SemanticDefaults):
    """Exclusion theory with unilateral semantics."""
    
    def inject_z3_model_values(self, z3_model, model_constraints):
        """Inject Z3 values for Exclusion theory iteration.
        
        Exclusion theory has different concepts than Logos:
        - Exclusion relations between states
        - Coherence predicates
        - Different world criteria
        """
        temp_solver = z3.Solver()
        for constraint in model_constraints.all_constraints:
            temp_solver.add(constraint)
        
        # Exclusion-specific injection logic
        # (Details depend on exclusion theory structure)
        
        model_constraints.all_constraints = list(temp_solver.assertions())
```

**Other Theories**: 
- Relevance theory: Handle relevance-specific relations
- Bimodal theory: Handle temporal and modal dimensions
- Imposition theory: Handle imposition functions
- Each implements its own `inject_z3_model_values` with its concepts

### Phase 4: Simplify BaseModelIterator

**Goal**: Remove ALL theory-specific logic from core.py and simplify to use IteratorBuildExample.

**Rationale**: With IteratorBuildExample handling model creation and theories handling injection, BaseModelIterator can focus purely on orchestration.

**Tasks**:
1. Add import for IteratorBuildExample
2. Replace entire `_build_new_model_structure` method
3. Remove ~600 lines of theory-specific code
4. Verify no theory concepts remain
5. Update method documentation

**File**: `src/model_checker/iterate/core.py`

**Changes**:
```python
# At top of file, add import
from model_checker.iterate.build_example import IteratorBuildExample

# Replace entire _build_new_model_structure method (was ~600 lines)
def _build_new_model_structure(self, z3_model):
    """Build a new model structure using IteratorBuildExample.
    
    This method is now completely theory-agnostic. It delegates model
    creation to IteratorBuildExample, which in turn delegates all
    theory-specific injection logic to the theory's semantics class.
    
    Args:
        z3_model: Z3 model with concrete values from iteration
        
    Returns:
        ModelStructure or None if building fails
        
    Note:
        This method no longer contains ANY theory-specific concepts.
        All knowledge about states, worlds, verify, falsify, etc. is
        encapsulated in the theory's semantics class.
    """
    try:
        # Create new model with Z3 injection (completely theory-agnostic)
        iter_build = IteratorBuildExample.create_with_z3_model(
            self.build_example,
            z3_model
        )
        
        # Extract the model structure
        new_structure = iter_build.model_structure
        
        # Add debugging information if successful
        if new_structure:
            new_structure._debug_model_number = self.current_iteration + 1
            new_structure._is_iteration_model = True
            
            # Log success
            logger.debug(f"Successfully built MODEL {self.current_iteration + 1}")
        
        return new_structure
        
    except Exception as e:
        # Log detailed error information
        logger.error(f"Error building new model structure: {str(e)}")
        logger.error(f"Model number: {self.current_iteration + 1}")
        logger.error(f"Theory: {self.build_example.semantic_theory.get('name', 'unknown')}")
        
        # Include full traceback for debugging
        import traceback
        logger.error(f"Full traceback:\n{traceback.format_exc()}")
        
        return None
```

**Code to Remove** (all theory-specific):
- All references to `semantics.is_world(state)`
- All references to `semantics.possible(state)`
- All references to `semantics.verify(state, atom)`
- All references to `semantics.falsify(state, atom)`
- All state iteration logic (`for state in range(2**semantics.N)`)
- All sentence letter extraction and processing
- All temporary solver creation and constraint injection
- All direct ModelConstraints manipulation

**Validation Test**:
```python
def test_core_has_no_theory_concepts():
    """Ensure core.py contains no theory-specific concepts."""
    with open('src/model_checker/iterate/core.py', 'r') as f:
        content = f.read()
    
    # These should NOT appear anywhere in core.py
    forbidden = [
        'is_world', 'possible(', 'verify(', 'falsify(',
        '2**semantics.N', '2**self.N', 'sentence_letter',
        'atom', 'states', 'worlds'
    ]
    
    for concept in forbidden:
        assert concept not in content, f"Found '{concept}' in core.py"
```

**Expected Outcome**:
- core.py reduced from ~1019 lines to ~400 lines
- No theory-specific concepts remain
- Much cleaner and more maintainable code

### Phase 5: Add Injection to Remaining Theories

**Goal**: Ensure all theories that support iteration implement proper injection.

**Rationale**: Each theory has unique concepts and structure. By implementing injection in each theory, we ensure proper encapsulation and make the framework easily extensible.

**Theories to Update**:

1. **Relevance Theory** (`theory_lib/logos/subtheories/relevance/`)
2. **Exclusion Theory** (`theory_lib/exclusion/`)
3. **Bimodal Theory** (`theory_lib/bimodal/`)
4. **Imposition Theory** (`theory_lib/imposition/`)
5. **Default/Classical Theory** (`theory_lib/default/`)

**Template for Theory Implementation**:
```python
def inject_z3_model_values(self, z3_model, model_constraints):
    """Inject Z3 values for [Theory Name] iteration.
    
    Args:
        z3_model: Z3 model with concrete values
        model_constraints: ModelConstraints to update
    """
    # Theory-specific implementation
    # Each theory knows its own structure
```

**Handling Optional Methods Without Decorators**:
```python
# In base class (if needed)
class SemanticDefaults:
    def inject_z3_model_values(self, z3_model, model_constraints):
        """Optional method for iteration support."""
        # Default: do nothing (not all theories support iteration)
        pass

# In ModelConstraints - check before calling
if hasattr(self.semantics, 'inject_z3_model_values'):
    self.semantics.inject_z3_model_values(z3_model, self)
```

**Success Criteria**:
- Each theory that has an iterate.py implements injection
- Each implementation handles theory-specific concepts
- No cross-theory dependencies

### Phase 6: Clean Up and Document

**Goal**: Remove obsolete code and update all documentation.

**Tasks**:

1. **Remove Obsolete Code**:
   - Delete old `_build_new_model_structure()` implementation (~600 lines)
   - Remove `test_model_building_sync.py` (no longer needed)
   - Clean up any temporary files or backups

2. **Verify Theory Isolation**:
   ```bash
   # Search for theory concepts outside theory_lib
   grep -r "is_world\|possible(\|verify(\|falsify(" src/ | grep -v theory_lib
   # Should return nothing
   ```

3. **Update Documentation**:
   - Update `iterate/README.md` with new architecture
   - Add section on IteratorBuildExample
   - Document injection pattern for new theories
   - Update theory development guide

4. **Add Integration Documentation**:
   - Document how to add iteration support to new theories
   - Provide injection method template
   - Add troubleshooting guide

## Testing Strategy

Following IMPLEMENT.md dual testing methodology:

### Method 1: Test-Driven Development

**Unit Tests** (write first, then implement):

1. **Phase 1 - ModelConstraints Injection**:
   ```bash
   # Write test
   python -m pytest src/model_checker/models/tests/test_constraints_injection.py::test_inject_z3_values_delegation -xvs
   # Implement inject_z3_values
   # Test passes
   ```

2. **Phase 2 - IteratorBuildExample**:
   ```bash
   # Write test
   python -m pytest src/model_checker/iterate/tests/test_build_example.py -xvs
   # Implement IteratorBuildExample
   # Test passes
   ```

3. **Phase 3 - Theory Injection**:
   ```bash
   # For each theory
   python -m pytest src/model_checker/theory_lib/logos/tests/test_injection.py -xvs
   ```

4. **Phase 4 - Core Simplification**:
   ```bash
   # Validation test
   python -m pytest src/model_checker/iterate/tests/test_core.py::test_no_theory_concepts -xvs
   ```

### Method 2: Direct CLI Testing

**Critical**: Test with iterations after each phase to detect regressions.

```bash
# After Phase 1-2 (might fail until Phase 3)
./dev_cli.py -i 1 src/model_checker/theory_lib/logos/examples.py

# After Phase 3 (should start working for implemented theories)
./dev_cli.py -i 2 src/model_checker/theory_lib/logos/examples.py
./dev_cli.py -i 3 src/model_checker/theory_lib/logos/examples.py

# After Phase 4-5 (all theories should work)
./dev_cli.py -i 2 src/model_checker/theory_lib/exclusion/examples.py
./dev_cli.py -i 2 src/model_checker/theory_lib/relevance/examples.py
./dev_cli.py -i 2 src/model_checker/theory_lib/bimodal/examples.py
./dev_cli.py -i 2 src/model_checker/theory_lib/imposition/examples.py

# Stress test
./dev_cli.py -i 5 src/model_checker/theory_lib/logos/examples.py
```

### Regression Testing

After each phase:
```bash
# Full test suite
./run_tests.py --all

# Iterator-specific regression
./run_tests.py iterate --verbose

# Theory-specific tests
./run_tests.py logos exclusion relevance --verbose
```

### Performance Testing

```bash
# Baseline before changes
time ./dev_cli.py -i 10 src/model_checker/theory_lib/logos/examples.py > baseline.txt

# After implementation
time ./dev_cli.py -i 10 src/model_checker/theory_lib/logos/examples.py > new.txt

# Compare times (should be within 5%)
```

## Risk Mitigation

### Identified Risks

1. **Breaking Existing Iteration**: 
   - Mitigation: Keep old code available until new code tested
   - Use feature flag if needed

2. **Theory Implementation Errors**:
   - Mitigation: Implement one theory at a time
   - Test thoroughly before moving to next

3. **Performance Degradation**:
   - Mitigation: Benchmark before and after
   - Profile if slowdown detected

4. **Missing Theory Support**:
   - Mitigation: Document which theories support iteration
   - Provide clear error messages

### Rollback Plan

If critical issues discovered:
1. Git revert to previous commit
2. Analyze failure mode
3. Adjust approach
4. Re-implement with fixes

### Debugging Support

Add debug logging:
```python
logger.debug(f"Injecting Z3 values for {theory_name}")
logger.debug(f"Constraints before: {len(model_constraints.all_constraints)}")
logger.debug(f"Constraints after: {len(model_constraints.all_constraints)}")
```

## Success Criteria

1. **Theory Isolation**: ✓ NO theory concepts outside theory_lib
2. **Code Reduction**: ✓ ~600 lines removed from core.py
3. **No Duplication**: ✓ Single model building path through BuildExample
4. **Clean Architecture**: ✓ Clear separation of concerns
5. **All Tests Pass**: ✓ Full regression suite passes
6. **Performance**: ✓ No significant slowdown (<5%)
7. **Extensibility**: ✓ Easy to add new theories

## Timeline

- **Phase 1**: 0.5 days - ModelConstraints injection hook
- **Phase 2**: 0.5 days - Create IteratorBuildExample
- **Phase 3**: 1 day - Theory-specific injection methods
- **Phase 4**: 0.5 days - Simplify BaseModelIterator
- **Phase 5**: 1 day - Remaining theory implementations
- **Phase 6**: 0.5 days - Clean up and document

**Total**: 4 days

## Validation Checklist

**Phase 1**:
- [ ] ModelConstraints.inject_z3_values implemented
- [ ] Delegation to semantics works
- [ ] No theory concepts in method
- [ ] All tests pass

**Phase 2**:
- [ ] IteratorBuildExample created
- [ ] Factory method works
- [ ] Extends BuildExample properly
- [ ] No theory concepts in class

**Phase 3**:
- [ ] Logos theory injection implemented
- [ ] At least one other theory implemented
- [ ] Theory concepts properly encapsulated
- [ ] Iteration works for implemented theories

**Phase 4**:
- [ ] Old implementation removed
- [ ] New implementation in place
- [ ] NO theory concepts in core.py
- [ ] File size reduced by ~600 lines

**Phase 5**:
- [ ] All theories implement injection
- [ ] All iteration tests pass
- [ ] No cross-theory dependencies

**Phase 6**:
- [ ] Documentation updated
- [ ] Obsolete code removed
- [ ] Theory isolation verified
- [ ] Performance acceptable

## Architecture Benefits

### Clean Separation
- BuildExample: Initial model building only
- IteratorBuildExample: Iteration-specific model building  
- Theory Semantics: ALL theory-specific logic
- No theory concepts in core packages

### Maintainability
- Single source of truth for model building
- Theory changes don't affect core
- Easy to understand and modify

### Extensibility
- New theories just implement inject_z3_model_values
- No changes needed to core packages
- Clear pattern to follow

## Research and Analysis

### Current Code Analysis

**Files Analyzed**:
1. `src/model_checker/builder/example.py` (321 lines)
   - Lines 105-130: Initial model construction
   - Well-structured, clean implementation
   - Comment at line 117-119 acknowledges duplication

2. `src/model_checker/iterate/core.py` (1019 lines)
   - Lines 520-656: `_build_new_model_structure()` method
   - Contains ~600 lines of duplicated logic
   - Heavy coupling to theory-specific concepts

3. `src/model_checker/models/constraints.py` (examined for injection point)
   - Clean abstraction layer
   - No existing injection mechanism

### Pattern Analysis

**Duplication Pattern**:
```python
# BuildExample.__init__ (simplified)
self.example_syntax = Syntax(premises, conclusions, operators)
self.example_semantics = self.semantics(self.settings)
self.model_constraints = ModelConstraints(...)
self.model_structure = self.model_structure_class(...)
self.model_structure.interpret(sentence_objects)

# BaseModelIterator._build_new_model_structure (simplified)
example_syntax = Syntax(premises, conclusions, operators)
example_semantics = semantics(settings)
model_constraints = ModelConstraints(...)
# 600+ lines of Z3 injection logic HERE
model_structure = model_structure_class(...)
model_structure.interpret(sentence_objects)
```

### Theory Concept Analysis

**Violations Found in core.py**:
1. Line 542: `semantics.is_world(state)` - Logos-specific
2. Line 548: `semantics.possible(state)` - Logos-specific  
3. Line 570: `semantics.verify(state, atom)` - Hyperintensional-specific
4. Line 576: `semantics.falsify(state, atom)` - Hyperintensional-specific
5. Line 530: `for state in range(2**semantics.N)` - Assumes bit vector states

**Impact**: These violations make adding new theories difficult and violate architectural principles.

## Implementation Dependencies

### Package Dependencies
```
model_checker/
├── builder/
│   ├── example.py (BuildExample - no changes needed)
│   └── ...
├── iterate/
│   ├── core.py (BaseModelIterator - major changes)
│   ├── build_example.py (NEW - IteratorBuildExample)
│   └── ...
├── models/
│   ├── constraints.py (ModelConstraints - add injection hook)
│   └── ...
└── theory_lib/
    ├── logos/
    │   └── semantic.py (add inject_z3_model_values)
    ├── exclusion/
    │   └── semantic.py (add inject_z3_model_values)
    └── ... (other theories)
```

### Import Dependencies
- No circular dependencies introduced
- Clean one-way flow: iterate → builder → models → theory_lib
- No backward references

## Performance Considerations

### Current Performance Profile
```bash
# Baseline measurement
time ./dev_cli.py -i 10 src/model_checker/theory_lib/logos/examples.py
# Average: 2.3 seconds
```

### Expected Impact
1. **Positive**: Reduced code paths, cleaner execution
2. **Neutral**: Same number of Z3 calls
3. **Risk**: Additional method calls (delegation)
4. **Mitigation**: Profile if >5% slowdown detected

### Performance Validation
```bash
# After each phase
time ./dev_cli.py -i 10 src/model_checker/theory_lib/logos/examples.py
# Target: < 2.5 seconds (within 10% of baseline)
```

## Documentation Requirements

### Files to Update

1. **iterate/README.md**
   - Add IteratorBuildExample section
   - Update architecture diagram
   - Document injection pattern

2. **docs/ARCHITECTURE.md**
   - Update component relationships
   - Add delegation pattern documentation

3. **theory_lib/README.md**
   - Add "Supporting Iteration" section
   - Document inject_z3_model_values requirement

4. **Each Theory README**
   - Document theory-specific injection implementation
   - Provide examples

### Documentation Template

```markdown
## Supporting Model Iteration

To support model iteration, theories must implement `inject_z3_model_values` in their semantics class:

```python
def inject_z3_model_values(self, z3_model, model_constraints):
    """Inject Z3 values for [Theory] iteration.
    
    This method extracts concrete values from a Z3 model and
    constrains the new model to match those values.
    """
    # Theory-specific implementation
```

See [theory]/semantic.py for the complete implementation.
```

## Detailed Implementation Breakdown

### Phase 1 Detailed Tasks

**File**: `src/model_checker/models/constraints.py`

1. **Add injection method** (15 minutes)
   - Add method after line ~150 (after constraint building methods)
   - Include comprehensive docstring
   - Ensure NO theory logic

2. **Write unit tests** (30 minutes)
   - Create test file if doesn't exist
   - Test delegation behavior
   - Test graceful handling when not supported
   - Verify no theory concepts

3. **Run tests** (15 minutes)
   - Execute new tests
   - Verify no regressions

### Phase 2 Detailed Tasks

**File**: `src/model_checker/iterate/build_example.py` (new)

1. **Create file structure** (10 minutes)
   - Create file with proper headers
   - Add imports

2. **Implement IteratorBuildExample** (45 minutes)
   - Empty __init__ method
   - Factory method create_with_z3_model
   - Helper methods _copy_from_original, _build_with_injection
   - Method _interpret_sentences

3. **Write comprehensive tests** (45 minutes)
   - Test factory method
   - Test attribute copying
   - Test Z3 injection delegation
   - Verify theory agnosticism

4. **Integration test** (30 minutes)
   - Test with actual BuildExample instance
   - Verify model creation works

### Phase 3 Detailed Tasks

**Logos Theory** - Primary Implementation

1. **Analyze current logic in core.py** (30 minutes)
   - Extract all Logos-specific code
   - Document state/world/verify/falsify usage

2. **Implement inject_z3_model_values** (45 minutes)
   - Create method in LogosSemantics
   - Port logic from core.py
   - Add proper error handling

3. **Write Logos-specific tests** (30 minutes)
   - Test world/possible constraints
   - Test verify/falsify relations
   - Test with actual Z3 models

4. **Integration test** (30 minutes)
   - Run with actual iterator
   - Verify correct behavior

**Other Theories** - Follow same pattern

### Phase 4 Detailed Tasks

1. **Add import** (5 minutes)
   - Add IteratorBuildExample import at top

2. **Replace method** (30 minutes)
   - Comment out old implementation
   - Add new simplified version
   - Ensure proper error handling

3. **Remove old code** (15 minutes)
   - Delete commented implementation
   - Clean up imports

4. **Verify theory isolation** (15 minutes)
   - Search for forbidden concepts
   - Run validation script

### Phase 5-6 Detailed Tasks

Similar breakdown for remaining theories and cleanup.

## Conclusion

This implementation plan addresses the core issues:
1. Eliminates code duplication (~600 lines)
2. Properly isolates theory-specific concepts
3. Maintains clean architecture
4. Improves maintainability and extensibility

The key insight is using delegation to push all theory knowledge into the theory packages where it belongs, keeping the core framework completely theory-agnostic.

## Appendix: Quick Reference

### Commands
```bash
# Test after Phase 1-2
./run_tests.py models iterate --verbose

# Test after Phase 3
./dev_cli.py -i 2 src/model_checker/theory_lib/logos/examples.py

# Test after Phase 4
grep -n "is_world\|possible\|verify\|falsify" src/model_checker/iterate/core.py

# Full validation
./run_tests.py --all
```

### Key Files
- `models/constraints.py` - Add injection hook
- `iterate/build_example.py` - New dependent class
- `theory_lib/*/semantic.py` - Add theory-specific injection
- `iterate/core.py` - Simplify to ~400 lines