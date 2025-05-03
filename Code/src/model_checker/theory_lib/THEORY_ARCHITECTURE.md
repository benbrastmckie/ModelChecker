# Theory Architecture in ModelChecker

This document provides a detailed overview of the standardized architecture used by all theories in the ModelChecker framework. Understanding this structure is essential for both using existing theories and developing new ones.

## Directory Structure

Each theory follows a consistent file organization:

```
theory_lib/
└── theory_name/
    ├── README.md           # Theory-specific documentation
    ├── __init__.py         # Public API and dependency management
    ├── semantic.py         # Core semantic framework implementation
    ├── operators.py        # Operator definitions and semantics
    ├── examples.py         # Test cases and examples
    ├── tests/              # Unit tests for the theory
    │   ├── __init__.py
    │   ├── test_theory_name.py
    │   └── test_iterate.py
    └── notebooks/          # Jupyter notebook demonstrations
        └── theory_name_demo.ipynb
```

## Module Architecture

### 1. `semantic.py` - Core Semantic Framework

This module implements the semantic foundation of the theory through three primary classes:

#### 1.1 Semantics Class

The Semantics class (e.g., `DefaultSemantics`, `BimodalSemantics`, `ExclusionSemantics`) provides the foundation of the semantic theory.
The following is based loosely on the `DefaultSemantics` to illustrate:

```python
class TheorySemantics(SemanticDefaults):
    """Core semantics for the theory."""
    
    # Settings management
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 3,                # Number of atomic states
        'max_time': 1,         # Maximum solver time
        'contingent': False,   # Theory-specific settings
    }
    
    DEFAULT_GENERAL_SETTINGS = {
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,
    }
    
    def __init__(self, settings=None):
        """Initialize semantic primitives and framework."""
        super().__init__(settings)
        self._initialize_sorts()
        self._initialize_primitives()
        
    def _initialize_sorts(self):
        """Initialize Z3 sorts, functions, and constants."""
        # Z3 sorts for basic types
        self.StateSort = self.z3.BitVecSort(self.settings['N'])
        # self.TimeSort = z3.IntSort()  # used in the bimodal_theory
        
    def _initialize_primitives(self):
        """Initialize Z3 sorts, functions, and constants."""
        # Z3 functions for primitive relations
        self.verify = self.z3.Function('verify', self.StateSort, self.z3.BoolSort())
        self.falsify = self.z3.Function('falsify', self.StateSort, self.z3.BoolSort())
        
        # Z3 constants for evaluation
        self.main_world = self.z3.Const('main_world', self.StateSort)
        self.main_point = {
            "world" : self.main_world
            # "time" : self.main_time  # used in the bimodal theory
        }
        
    def is_part_of(self, s1, s2):
        """Define part-of relation between states."""
        return self.z3.And(self.z3.BVAnd(s1, s2) == s1, s1 != 0)
        
    def fusion(self, s1, s2):
        """Compute fusion of two states."""
        # Theory-specific implementation

    # Include other definitions that draw on the primitives introduced above
        
    def true_at(self, sentence, point):
        """Evaluate truth of a sentence at evaluation point."""
        # Theory-specific implementation
        
    def false_at(self, sentence, point):
        """Evaluate falsity of a sentence at evaluation point."""
        # Theory-specific implementation
        
    def extended_verify(self, formula, s):
        """Determine if state s verifies formula."""
        # Theory-specific implementation (hyperintensional)
        
    def extended_falsify(self, formula, s):
        """Determine if state s falsifies formula."""
        # Theory-specific implementation (hyperintensional)
        
    def define_invalidity(self):
        """Define premise and conclusion evaluation for finding countermodels."""
        # Create functions for premise/conclusion evaluation
        premise_behavior = lambda premise: self.true_at(premise, self.main_point)
        conclusion_behavior = lambda conclusion: self.false_at(conclusion, self.main_point)
        
        return premise_behavior, conclusion_behavior
    
    def verify_model(self, model, premises, conclusions):
        """Verify that a model satisfies the invalidity conditions."""
        # Check that premises are true at main point
        # Check that conclusions are false at main point
        # Return verification status dictionary
    
    def extract_model_elements(self, model):
        """Extract semantic elements from a Z3 model."""
        # Extract basic elements
        all_states = self._extract_states(model)
        possible_states = self._extract_possible_states(model)
        world_states = self._extract_worlds(model)
        
        # Extract theory-specific elements
        # (compatibility, alternatives, accessibility, etc.)
        
        # Return semantic representation
        return {
            "states": all_states,
            "possible_states": possible_states,
            "worlds": world_states,
        }
        
    def get_frame_constraints(self):
        """Define theory-specific frame constraints."""
        constraints = []
        # Add theory-specific constraints
        return constraints
```

**Key Responsibilities:**

* Define Z3 sorts, functions and constants (state, verification functions, evaluation points)
* Implement semantic relations (part-of, compatibility, fusion)
* Define evaluation context (main evaluation point, frame constraints)
* Provide truth evaluation methods (true_at/false_at for sentences)
* Implement verification methods (extended_verify/extended_falsify for complex formulas)
* Manage theory-specific settings

#### 1.2 Proposition Class

The Proposition class (e.g., `DefaultProposition`, `BimodalProposition`) represents propositional content:

```python
class TheoryProposition(PropositionDefaults):
    """Proposition implementation for the theory."""
    
    def __init__(self, semantics, sentence, eval_point):
        """Initialize proposition with semantics and sentence."""
        super().__init__(semantics, sentence)
        
        self.eval_world = eval_point["world"]
        # self.eval_time = eval_point["time"]  # needed for bimodal theory
        self.verifiers, self.falsifiers = self.find_proposition()

    def __eq__(self, other):
        """Check equality with another proposition."""
        if not isinstance(other, TheoryProposition):
            return False
        return self.sentence == other.sentence
        
    def __repr__(self):
        """String representation of proposition."""
        return f"Proposition({self.sentence})"
        if self.settings.get('contingent', False):
            self._add_contingency_constraints(constraints)
            
        if self.settings.get('non_empty', False):
            self._add_non_empty_constraints(constraints)
            
        return constraints
        
    def get_constraints(self):
        """Generate constraints for proposition semantics."""

        def _get_basic_constraints():
            """Get constraints for atomic propositions."""
            # Return list of constraints for atomic semantics
        
        def _add_contingency_constraints():
            """Add constraints requiring propositions to be contingent."""
            # Theory-specific implementation

        # Basic constraints from atom semantics
        basic_constraints = self._get_basic_constraints()
        
        # Optional constraints based on settings
        optional_constraints = []
        
        # Add contingency constraints if requested
        if self.settings.get("contingent", False):
            optional_constraints.extend(self._get_contingency_constraints())
            
        # Combine all constraints
        return basic_constraints + optional_constraints
    
    def find_proposition(self, model):
        """Extract verifiers and falsifiers from Z3 model."""
        # Theory-specific implementation

    def print_proposition(self, eval_point, indent_num, use_colors):
        """Print the proposition with its truth value at the given evaluation point."""
        # Theory-specific implementation
```

**Key Responsibilities:**

* Represent propositional content with verifiers and falsifiers
* Provide equality and string representation methods
* Generate Z3 constraints for proposition semantics
* Implement optional constraints based on settings (contingency, non-emptiness)
* Extract proposition data from Z3 models and specify print pattern

#### 1.3 ModelStructure Class

The ModelStructure class (e.g., `DefaultStructure`, `BimodalStructure`) manages the overall semantic model:

```python
class TheoryStructure(ModelDefaults):
    """Model structure for the theory."""
    
    def __init__(self, model_constraints, settings=None):
        """Initialize model structure with constraints and settings."""

        super().__init__(model_constraints, settings)
        
        # Process model if available
        if self.z3_model_status and self.z3_model is not None:
            self._initialize_model_values()
            
    def _initialize_model_values(self):
        """Initialize model values from Z3 model."""
        self.z3_main_world = self.z3_model[self.main_world]
        self.main_point["world"] = self.z3_main_world
        self.z3_possible_states = [
            bit for bit in self.all_states
            if bool(self.z3_model.evaluate(self.semantics.possible(bit)))
        ]
        self.z3_world_states = [
            bit for bit in self.z3_possible_states
            if bool(self.z3_model.evaluate(self.semantics.is_world(bit)))
        ]
        
    def print_all(self, example_name, theory_name, output=sys.__stdout__):
        """Print a complete overview of the model structure and evaluation results."""

        # Print basic example information
        self.print_info(model_status, self.settings, example_name, theory_name, output)

        # Print complete model if it exists
        if self.z3_model_status:
            self.print_states(output)
            self.print_evaluation(output)
            self.print_input_sentences(output)
            self.print_model(output)
            self.print_footer(output)
            return

    def print_states(self, output=None):
        """Print all states in the model with their properties."""
        # Theory-specific implementation
        
    def print_evaluation(self, output=None):
        """Print the evaluation world and evaluate all sentence letters."""
        # Theory-specific implementation
        
    def print_input_sentences(self, world=None):
        """Prints the premises and conclusions with their semantic interpretations."""
        # Theory-specific implementation
        
    def print_model(self, output=None):
        """Print model structure with full details."""
        # Theory-specific implementation for model display

    def print_footer(self, output=None):
        """Print footer including the time taken to compute."""
        # Theory-specific implementation for model display

    def detect_model_differences(self, previous_structure):
        """Calculate differences between this model and a previous one."""
        # Theory-specific implementation for iteration (optional)
```

**Key Responsibilities:**

* Initialize and manage Z3 model data through `_initialize_model_values`
* Extract model elements (states, worlds, relations) from Z3 model
* Provide visualization methods (`print_states`, `print_evaluation`, `print_input_sentences`, `print_model`)
* Support model comparison through `detect_model_differences`
* Evaluate formulas at specific points in the model

#### 1.4 `semantic.py` API

Include the following to expose the defined classes to be imported elsewhere.

```python
# Define the public API for semantic.py
__all__ = [
    "TheorySemantics",        # Core semantic framework implementation
    "TheoryProposition",      # Proposition representation and evaluation
    "TheoryStructure",   # Model structure management
]
```

### 2. `operators.py` - Logical Operators

This module defines the logical operators used in the theory:

```python
from model_checker.syntactic import Operator, DefinedOperator, OperatorCollection

class SomeOperator(Operator):
    """A primitive logical operator in the theory."""

    name = "\\some_operator"
    arity = 2
    
    def __init__(self):
        """Initialize operator with name, symbol, and arity."""
        super().__init__("name", "\\symbol", arity)
        
    def true_at(self, leftarg, rightarg, eval_point):
        """Evaluate truth of operator at evaluation point."""
        # Theory-specific truth conditions
        
    def false_at(self, leftarg, rightarg, eval_point):
        """Evaluate falsity of operator at evaluation point."""
        # Theory-specific falsity conditions
        
    def extended_verify(self, state, leftarg, rightarg, eval_point):  # (hyperintensional only)
        """Determine verification conditions for operator."""
        # Theory-specific verification
        
    def extended_falsify(self, state, leftarg, rightarg, eval_point):  # (hyperintensional only)
        """Determine falsification conditions for operator."""
        # Theory-specific falsification
        
    def find_truth_condition(self, leftarg, rightarg, eval_point):
        """Gets truth-condition for the conjunction of two arguments."""

    def print_method(self, sentence, eval_point, indent_num, use_colors):
        """Custom printing for operator evaluation."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)
        # Other options can be imported from model_checker.syntactic
        
class SomeDerivedOperator(DefinedOperator):
    """A derived operator defined in terms of primitives."""
    
    def derived_definition(self, leftarg, rightarg): # type: ignore
        """Defines the material conditional A → B as ¬A ∨ B."""
        # Definition in prefix form
        
# Create operator collection with all operators
theory_operators = OperatorCollection(
    # Extensional operators
    NegationOperator,
    AndOperator,
    OrOperator,
    
    # Theory-specific operators
    ModalOperator,
    CounterfactualOperator,
)

# Export operators
__all__ = ["theory_operators"]
```

**Key Components:**

* **Primary Operator Classes**: Implementations of logical operators (inherit from `Operator`)
* **Derived Operator Classes**: Operators defined in terms of others (inherit from `DefinedOperator`)
* **Operator Collection**: Collection of operators used in the theory (using `OperatorCollection`)

**Common Operator Types:**

* **Truth-Functional Operators**: Negation, conjunction, disjunction, implication
* **Theory-Specific Operators**: Modal operators, counterfactual operators, etc.

### 3. `examples.py` - Test Cases and Examples

This module contains examples and test cases for the theory:

```python
# Import the theory components
from .semantic import TheorySemantics, TheoryProposition, TheoryStructure
from .operators import theory_operators

# Define examples with standardized naming conventions
# Countermodels (expectations=True, should find a countermodel)
ML_CM_1_premises = ['A']
ML_CM_1_conclusions = ['\\Box A']
ML_CM_1_settings = {
    'N': 3,
    'contingent': True,
    'non_empty': True,
    'disjoint': False,
    'max_time': 1,
    'expectation': True,  # Expect to find a countermodel
}
ML_CM_1_example = [
    ML_CM_1_premises,
    ML_CM_1_conclusions,
    ML_CM_1_settings,
]

# Theorems (expectation=False, should NOT find a countermodel)
CL_TH_2_premises = []
CL_TH_2_conclusions = ['((A = B) \\imp (A \\Ground B))']
CL_TH_2_settings = {
    'N': 3,
    'contingent': False,
    'non_empty': True, 
    'disjoint': False,
    'max_time': 1,
    'expectation': False,  # Expect no countermodel (theorem is valid)
}
CL_TH_2_example = [
    CL_TH_2_premises,
    CL_TH_2_conclusions,
    CL_TH_2_settings,
]

# Required module definitions
semantic_theories = {
    "TheoryName": {
        "semantics": TheorySemantics,
        "proposition": TheoryProposition,
        "model": TheoryStructure,
        "operators": theory_operators
    }
}

# Example range dictionary specifies which examples to include in manual testing
example_range = {
    "ML_CM_1": ML_CM_1_example,
    "CL_TH_2": CL_TH_2_example,
}

# Test example range for automated unit testing
test_example_range = {
    "ML_CM_1": ML_CM_1_example,
    "CL_TH_2": CL_TH_2_example,
}

# Global settings for all examples
general_settings = {
    "print_constraints": False,
    "print_impossible": True,
    "print_z3": False,
    "save_output": False,
}

# Export variables
__all__ = [
    'general_settings',
    'semantic_theories',
    'example_range',
    'test_example_range',
]
```

**Key Requirements:**

* **Example Categories**:
  * Countermodels (XX_CM_#): Invalid arguments expected to find countermodels
  * Theorems (XX_TH_#): Valid arguments expected to have no countermodels

* **Required Dictionaries**:
  * `semantic_theories`: Maps theory names to components (semantics, proposition, model, operators)
  * `example_range`: Specifies which examples to run in manual testing
  * `test_example_range`: Specifies examples for unit testing
  * `general_settings`: Global settings for all examples

* **Example Definition Format**:
  ```python
  EXAMPLE_NAME_premises = [premise1, premise2]
  EXAMPLE_NAME_conclusions = [conclusion1, conclusion2]
  EXAMPLE_NAME_settings = {settings_dict}
  EXAMPLE_NAME_example = [premises, conclusions, settings]
  ```

### 4. `__init__.py` - Public API

This module provides the public API for the theory:

```python
"""
TheoryName - A semantic theory for ModelChecker

This theory implements [brief description of theory].
"""

# Export public classes and functions
from .semantic import TheorySemantics, TheoryProposition, TheoryStructure
from .operators import theory_operators

# Optional: Export convenience functions
from .examples import example_range, test_example_range, general_settings

# Define exported symbols
__all__ = [
    'TheorySemantics', 
    'TheoryProposition', 
    'TheoryStructure',
    'theory_operators',
    'example_range', 
    'test_example_range', 
    'general_settings'
]

# Optional: Version and metadata
__version__ = '0.1.0'
__author__ = 'Author Name'
```

**Key Components:**

* **Import Management**: Expose classes and functions for public use
* **Dependency Management**: Import necessary components from other modules
* **API Construction**: Functions to build the theory's API
* **Convenience Functions**: Simplified access to common operations

### 5. `tests/` - Unit Tests

The tests directory contains unit tests for the theory:

```python
# test_theory_name.py
import unittest
from model_checker.builder import BuildExample
from model_checker.theory_lib import theory_name
from model_checker.theory_lib.theory_name.examples import test_example_range

class TestTheoryName(unittest.TestCase):
    """Test cases for TheoryName."""
    
    def test_countermodels(self):
        """Test that countermodels are found correctly."""
        for name, example in test_example_range.items():
            if name.startswith("ML_CM_"):
                with self.subTest(name=name):
                    # Create BuildExample with theory components
                    build = BuildExample(
                        name,
                        theory_name.semantic_theories["TheoryName"],
                        example[0],  # premises
                        example[1],  # conclusions
                        example[2],  # settings
                    )
                    # Run the example
                    result = build.run()
                    # Check expectation
                    if example[2].get("expectation", False):
                        self.assertTrue(result, f"Expected countermodel for {name}")
                    else:
                        self.assertFalse(result, f"Expected no countermodel for {name}")
                        
    def test_theorems(self):
        """Test that theorems are valid."""
        # Similar implementation for theorems
```

**Key Test Categories:**

* **Theory Tests**: Validate the theory's fundamental principles
* **Operator Tests**: Test individual operator behavior
* **Regression Tests**: Ensure specific bugs remain fixed
* **Iteration Tests**: Verify iterative model finding (in test_iterate.py)

### 6. `notebooks/` - Jupyter Notebooks

Jupyter notebooks provide interactive demonstrations of the theory:

```python
# Example notebook code cells
# Import theory components
from model_checker.theory_lib import theory_name
from model_checker import BuildExample

# Create a model
theory = theory_name.semantic_theories["TheoryName"]
model = BuildExample("example_name", theory)

# Test a formula
result = model.check_formula("\\Box A -> A")
print(f"Formula is {'valid' if not result else 'invalid'}")

# Visualize model
model.print_model()
```

**Key Notebook Types:**

* **Introduction Notebooks**: Basic theory concepts and examples
* **Operator Notebooks**: Demonstrate operator behavior
* **Countermodel Notebooks**: Showcase interesting countermodels
* **Feature Demonstration Notebooks**: Highlight unique theory features

## Theory API Flow

The API flow shows how components interact within and between theories:

### 1. Internal Module Dependencies

```
┌─────────────┐     ┌──────────────┐
│ semantic.py │<────│ operators.py │
└─────┬───────┘     └─────┬────────┘
      │                   │
      │                   │
      ▼                   ▼
┌─────────────┐     ┌──────────────┐
│ examples.py │<────│  __init__.py │
└─────────────┘     └──────────────┘
```

* `semantic.py` provides the foundation for operator implementation
* `operators.py` depends on semantic primitives from `semantic.py`
* `examples.py` imports and uses both semantics and operators
* `__init__.py` exports all components for external use

### 2. Theory Usage Pattern

```python
# Direct component access
from model_checker.theory_lib.theory_name import TheorySemantics, theory_operators

# High-level API (in model_checker/__init__.py)
from model_checker import get_theory
theory = get_theory("theory_name")

# Example running
from model_checker import BuildExample
model = BuildExample("example_name", get_theory("theory_name"))
```

### 3. Testing Integration

```python
# In tests/test_theory_name.py
from model_checker.theory_lib.theory_name.examples import test_example_range

# Run through BuildExample
for name, example in test_example_range.items():
    # Test code...
```

The `test_example_range` dictionary in `examples.py` specifies which examples to include in automated testing.

### 4. Jupyter Notebook Integration

```python
# In notebooks/theory_name_demo.ipynb
from model_checker.theory_lib import theory_name
from model_checker.jupyter import ModelExplorer, FormulaChecker

# Direct theory access
semantics = theory_name.TheorySemantics()
operators = theory_name.theory_operators

# High-level API
explorer = ModelExplorer(theory="theory_name")
explorer.display()

# Formula checking
result = FormulaChecker.check("A -> A", theory="theory_name")
```

Jupyter notebooks import from the theory's public API to create interactive demonstrations.

## Extension Points

When developing a new theory, these are the key extension points:

1. **Semantic Relations**:
   * Specify theory-specific primitives
   * Implement theory-specific semantics definitions

2. **Truth Conditions**:
   * Implement `true_at` and `false_at` with your theory's truth conditions
   * Include verification/falsification methods in hyperintensional

3. **Constraints**:
   * Implement theory-specific frame constraints
   * Add specialized model constraints

4. **Evaluation Point**:
   * Expand the `main_point` and `eval_point` dictionaries
   * For instance, the `bimodal/` theory includes worlds and times

5. **Operator Semantics**:
   * Implement operator classes with theory-specific semantics
   * Create an operator collection dictionary

6. **Model Visualization**:
   * Override `print_model` for theory-specific visualization
   * Add Jupyter notebook integration

7. **Unit Tests**:
   * Once a range of examples are working, add these to `test_example_range`
   * The unit testing for the theory will then run each of these examples

## Best Practices

1. **Follow Naming Conventions**:
   * Class names: `TheorySemantics`, `TheoryProposition`, `TheoryStructure`
   * Operators: `SomeOperator` (for primitive operators)
   * Examples: `ML_CM_1`, `CL_TH_2` (with standard prefixes)

2. **Complete Required Components**:
   * Implement all three core classes (Semantics, Proposition, Structure)
   * Provide standard operators (negation, conjunction, disjunction)
   * Include test examples in the required dictionaries

3. **Document Theory Specifics**:
   * Explain theory-specific operators and relations
   * Document theory-specific settings
   * Provide examples demonstrating key features

4. **Test Thoroughly**:
   * Include countermodels for important invalid arguments
   * Include theorems for fundamental valid principles
   * Test boundary cases and theory-specific features

5. **Use Jupyter Notebooks**:
   * Create demonstration notebooks
   * Showcase theory-specific features
   * Provide educational examples

By following this architecture, theories can be consistently implemented, compared, and extended within the ModelChecker framework.
