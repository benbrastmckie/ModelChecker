Programmatic Semantics Theory Library

## API

### Library Structure

The ModelChecker framework provides a modular API for implementing and working with different logical theories. The API is organized in several layers:

1. **Core Framework** (`model_checker`): Provides the foundational classes and utilities for model checking
2. **Theory Library** (`model_checker.theory_lib`): Contains specific implementations of logical theories
3. **Individual Theories**: Each theory implements its own semantic interpretation and operators

### Core Framework API

The core framework provides these key components:

```python
from model_checker import (
    # High-level builders
    BuildExample, BuildModule, BuildProject,
    
    # Core classes
    ModelConstraints, Syntax,
    
    # Utility functions
    ForAll, Exists, bitvec_to_substates,
    
    # Library access functions
    get_theory, get_example, run_test
)
```

#### Builder Functions

- `BuildExample(name, theory)`: Creates a model from a named example within a theory
- `BuildModule(module_name)`: Loads and runs examples from a specific module
- `BuildProject(name, settings)`: Creates new theory implementations from templates

#### Utility Functions

- `get_theory(name)`: Loads a theory module by name (e.g., "default", "exclusion")
- `get_example(name, theory)`: Retrieves a specific example from a theory
- `run_test(example, theory)`: Runs a specific test case with the given theory

### Theory Library API

The theory library (`model_checker.theory_lib`) exposes individual theories through lazy loading:

```python
from model_checker.theory_lib import default, exclusion, imposition
```

When accessed, each theory module is loaded on demand and cached for subsequent access.

#### Utility Functions

The theory library also provides utility functions for accessing examples:

```python
from model_checker.theory_lib import (
    get_examples,
    get_test_examples,
    get_semantic_theories
)

# Get examples from a specific theory
default_examples = get_examples('default')
exclusion_examples = get_examples('exclusion')

# Get test examples for unit testing
test_examples = get_test_examples('default')

# Get semantic theory implementations
semantic_theories = get_semantic_theories('default')
```

### Individual Theory APIs

Each theory follows a standardized API pattern while implementing its specific semantics:

#### Default Theory

```python
from model_checker.theory_lib.default import (
    # Core semantic classes
    Semantics, Proposition, ModelStructure,
    
    # Operators collection
    default_operators
)
```

#### Exclusion Theory

```python
from model_checker.theory_lib.exclusion import (
    # Core semantic classes
    ExclusionSemantics, UnilateralProposition, ExclusionStructure,
    
    # Operators collection
    exclusion_operators
)
```

#### Imposition Theory

```python
from model_checker.theory_lib.imposition import (
    # Core semantic classes
    ImpositionSemantics,
    
    # Operators collection
    imposition_operators
)
```

#### Bimodal Theory

```python
from model_checker.theory_lib.bimodal import (
    # Core semantic classes
    Semantics, ImpositionSemantics, Proposition,
    
    # Individual operators
    NegationOperator, AndOperator, OrOperator,
    TopOperator, BotOperator, IdentityOperator,
    CounterfactualOperator, ImpositionOperator, NecessityOperator,
    
    # Defined operators
    ConditionalOperator, BiconditionalOperator,
    MightCounterfactualOperator, MightImpositionOperator,
    DefPossibilityOperator
)
```

### Accessing Examples

The framework provides a unified way to access examples from any theory:

```python
# From theory_lib utils
from model_checker.theory_lib import get_examples
examples = get_examples('default')

# Directly from examples module (alternative approach)
from model_checker.theory_lib.default.examples import (
    example_range,
    test_example_range,
    semantic_theories
)
```

### Common API Pattern

Each theory implementation follows this pattern:

1. **Semantic Classes**:
   - Extend `model.SemanticDefaults` to implement theory-specific semantics
   - Extend `model.PropositionDefaults` for logical formula evaluation
   - Provide methods for semantic relations (fusion, part-of, exclusion, etc.)

2. **Operators**:
   - Define operators that implement the theory's logical connectives
   - Each operator implements truth conditions and verification/falsification relations
   - Operators are collected in a dictionary (e.g., `default_operators`)

3. **Examples**:
   - Define test cases as [premises, conclusions, settings]
   - Categorize as countermodels or theorems
   - Provide configuration settings for model checking
   - Access through utility functions to avoid circular imports

### Syntax Guidelines

A well-formed sentence in the model-checker follows specific syntactic rules that ensure correct parsing and evaluation. This section provides a comprehensive guide to constructing valid sentences across different logical theories.

#### Core Syntax Rules

1. **Notation Types**:
   - **Prefix notation**: Used for unary operators (operators that take a single argument)
   - **Infix notation**: Used for binary operators (operators that take two arguments)

2. **Operator Format**:
   - All operators start with a backslash `\` followed by their symbol
   - For example: `\\neg`, `\\wedge`, `\\boxright`, `\\Box`

#### Backslash Escaping in Python

When using logical operators in Python strings, you need to use double backslashes `\\` instead of single ones. This is because the backslash `\` is an escape character in Python strings:

```python
# INCORRECT - single backslash (will cause syntax errors)
formula = "(A \wedge B)"  # Python interprets \w as a special character

# CORRECT - double backslash for each operator
formula = "(A \\wedge B)"  # Python correctly passes \wedge to the model-checker

# Alternative - use raw strings
formula = r"(A \wedge B)"  # The 'r' prefix tells Python not to process escapes
```

This only applies when writing formulas in Python code. In documentation (like this README) and in other contexts, a single backslash is sufficient. The model-checker itself expects operators with single backslashes in the actual logical formulas.

Important use cases:
- In Python strings: Use `\\neg A` or r`\neg A`
- In function calls: `model.check_formula("\\Box p \\rightarrow p")`
- In docstrings: `"The formula \\Box A represents necessity"`
- In Jupyter notebooks: Same as Python strings, use double backslashes

3. **Parentheses Requirements**:
   - All binary operators (infix notation) must be wrapped in a single pair of parentheses
   - For example: `(A \\wedge B)`, `(C \\boxright D)`
   - Unary operators do not require parentheses around the entire expression
   - For example: `\\neg A`, `\\Box B`

4. **Atomic Propositions**:
   - Typically represented by uppercase letters (A, B, C, etc.)
   - Must be alphanumeric (letters and numbers only)

#### Well-Formed Examples by Theory

**Default Theory**:
- Basic propositions: `A`, `B`, `C`
- Negation: `\\neg A`
- Conjunction: `(A \\wedge B)`
- Disjunction: `(A \\vee B)` 
- Material implication: `(A \\rightarrow B)`
- Material biconditional: `(A \\leftrightarrow B)`
- Identity: `(A \\equiv B)`
- Counterfactual: `(A \\boxright B)`
- Might counterfactual: `(A \\diamondright B)`
- Modal operators: `\\Box A`, `\\Diamond A`
- Truth/falsity constants: `\\top`, `\\bot`

**Exclusion Theory**:
- Exclusion: `\\exclude A`
- Unilateral conjunction: `(A \\uniwedge B)`
- Unilateral disjunction: `(A \\univee B)`
- Unilateral equivalence: `(A \\uniequiv B)`

**Imposition Theory**:
- Imposition operator: `(A \\imposition B)`
- Could operator: `(A \\could B)`

**Bimodal Theory**:
- All operators from Default Theory, plus:
- Temporal operators: `\\Future A`, `\\past A`

#### Complex Expression Construction

1. **Nesting Expressions**:
   - Maintain parentheses around each binary operator
   - For example: `((A \\wedge B) \\boxright C)`, `(A \\boxright (B \\boxright C))`

2. **Combining Multiple Operators**:
   - Mix unary and binary operators: `(\\Box A \\vee \\Diamond B)`
   - Nest multiple layers: `(((A \\wedge B) \\wedge C) \\boxright D)`
   - Chain implications: `(A \\boxright (B \\boxright C))`

3. **Complex Examples**:
   - `(A \\wedge (B \\vee C))`
   - `((A \\rightarrow B) \\boxright (C \\rightarrow D))`
   - `\\Box ((A \\wedge B) \\rightarrow C)`
   - `(\\neg A \\vee (B \\wedge \\neg C))`

#### Theory Translation

The model-checker supports translation between theories through the `translate()` method in `BuildModule`. When comparing semantics across theories:

1. Sentences are converted from their original theory notation to the target theory
2. Operators are mapped to their equivalents in the target theory
3. Semantic evaluations can be performed on the same sentence across different theories

For example, a default theory sentence like `(A \\boxright B)` might be translated to an imposition theory sentence that uses the imposition operator: `(A \\imposition B)`.

#### Parsing Process

When processing sentences, the model-checker:
1. Converts infix notation to prefix notation internally (via the `prefix()` method)
2. Builds a sentence hierarchy with operator and argument linkages
3. Associates each sentence with appropriate semantic operators for evaluation
4. Recursively evaluates complex expressions based on their structure

### Usage Example

```python
from model_checker import BuildExample, get_theory
from model_checker.theory_lib import get_examples

# Load a theory
theory = get_theory("default")

# Create a model from an example
model = BuildExample("simple_modal", theory)

# Check a formula
result = model.check_formula("\\Box p \\rightarrow p")
print(result)

# Access examples
examples = get_examples("default")
for name, example in examples.items():
    print(f"Example {name}: {example[0]}")  # Premises
```

### Extending with New Theories

To create a new theory:

1. Create a new directory under `theory_lib/`
2. Implement `semantic.py` with your theory-specific semantics
3. Implement `operators.py` with your logical operators
4. Define `__init__.py` to export your public API
5. Add examples in `examples.py`
6. Register your theory in `theory_lib/__init__.py`
7. Add support for the new theory in `theory_lib/utils.py`

## API Refactoring Strategies

The following strategies propose different approaches to enhance the ModelChecker API architecture. These options vary in scope, complexity, and backward compatibility impact.

### Strategy 1: Standardized Theory Registry

**Goal**: Create a centralized registry system for theory implementations to reduce redundancy and simplify extension.

**Implementation**:
1. Create a `TheoryRegistry` class in model_checker.registry module:
```python
class TheoryRegistry:
    """Central registry for theory implementations."""
    def __init__(self):
        self._theories = {}
        
    def register(self, name, theory_module):
        """Register a theory implementation."""
        self._theories[name] = theory_module
        
    def get_theory(self, name):
        """Get a registered theory by name."""
        if name not in self._theories:
            self._load_theory(name)
        return self._theories[name]
        
    def get_examples(self, theory_name):
        """Get examples from a theory."""
        theory = self.get_theory(theory_name)
        return self._get_examples_from_theory(theory)
        
    def _load_theory(self, name):
        """Dynamic loading of theory implementations."""
        # Load theory dynamically
```

2. Update the `model_checker.__init__` to use the registry:
```python
from .registry import theory_registry

def get_theory(name):
    """Get a theory by name using the registry."""
    return theory_registry.get_theory(name)
    
def get_examples(theory_name):
    """Get examples from a theory."""
    return theory_registry.get_examples(theory_name)
```

**Benefits**:
- Centralized management of theories
- Standardized interface for all theories
- Automatic discovery of new theories
- Simplified extension process

**Drawbacks**:
- Requires significant refactoring
- May introduce compatibility issues with existing code
- Adds architectural complexity

### Strategy 2: Protocol-based Theory Interface

**Goal**: Define formal interfaces for theory implementations to ensure consistency.

**Implementation**:
1. Define protocols for theory components:
```python
from typing import Protocol, Dict, Any, List

class SemanticProtocol(Protocol):
    """Protocol for semantic implementations."""
    def __init__(self, settings: Dict[str, Any]) -> None: ...
    def compatible(self, a: Any, b: Any) -> bool: ...
    # Other required methods

class PropositionProtocol(Protocol):
    """Protocol for proposition implementations."""
    def __init__(self, formula: str, model: Any) -> None: ...
    def evaluate(self) -> bool: ...
    # Other required methods

class TheoryProtocol(Protocol):
    """Protocol for complete theory implementations."""
    semantics: type
    proposition: type
    model: type
    operators: Dict[str, Any]
```

2. Update existing theories to implement these protocols
3. Add validation in the API to ensure protocol compliance

**Benefits**:
- Clear contract for theory implementations
- Static type checking support
- Self-documenting interfaces
- Easier debugging of implementation issues

**Drawbacks**:
- Requires Python 3.8+ for full Protocol support
- May constrain flexibility for specialized theories
- Additional validation overhead

### Strategy 3: Composable Model Components

**Goal**: Refactor the core model checking engine to support more flexible composition of components.

**Implementation**:
1. Extract interfaces for core components:
```python
class ConstraintGenerator:
    """Generates Z3 constraints from logical formulas."""
    def generate_constraints(self, formula, context):
        """Generate constraints for a formula."""
        
class ModelSolver:
    """Solves constraint satisfaction problems."""
    def solve(self, constraints, settings):
        """Find a model satisfying constraints."""
        
class ResultInterpreter:
    """Interprets solver results into semantic terms."""
    def interpret(self, solver_result, context):
        """Interpret solver results."""
```

2. Refactor ModelConstraints to use these components:
```python
class ModelConstraints:
    """Coordinates model constraint generation and solving."""
    def __init__(self, settings, syntax, semantics, proposition,
                 constraint_generator=None, solver=None, interpreter=None):
        self.constraint_generator = constraint_generator or DefaultConstraintGenerator()
        self.solver = solver or DefaultModelSolver()
        self.interpreter = interpreter or DefaultResultInterpreter()
        # ...
```

**Benefits**:
- Greater flexibility in component replacement
- Easier testing of individual components
- Support for alternative constraint solvers beyond Z3
- More modular architecture

**Drawbacks**:
- Significant refactoring required
- May increase complexity for simple use cases
- Potential performance overhead from abstraction

### Strategy 4: Module-Level Configuration

**Goal**: Improve configuration management across the framework with a centralized approach.

**Implementation**:
1. Create a central configuration system:
```python
class Configuration:
    """Central configuration for ModelChecker."""
    _instance = None
    
    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
            cls._instance._init_defaults()
        return cls._instance
    
    def _init_defaults(self):
        self.settings = {
            "print_constraints": False,
            "print_impossible": False,
            "print_z3": False,
            "save_output": False,
            "maximize": False,
            # More settings
        }
        
    def configure(self, **kwargs):
        """Update configuration settings."""
        self.settings.update(kwargs)
        
    def get(self, key, default=None):
        """Get a configuration setting."""
        return self.settings.get(key, default)
```

2. Use throughout the codebase:
```python
from .config import config

class BuildExample:
    def __init__(self, name, theory):
        self.verbose = config.get("verbose", False)
        # ...

class ModelStructure:
    def __init__(self, constraints, settings=None):
        self.show_model = config.get("show_model", True)
        # ...
```

**Benefits**:
- Consistent configuration across components
- Global defaults with local overrides
- Simplified initialization code
- Centralized documentation of settings

**Drawbacks**:
- Potential for global state issues
- May hide dependencies between components
- Requires careful thread safety consideration

### Strategy 5: Simplified Theory Factory

**Goal**: Create a factory pattern for theory creation that simplifies the API without major refactoring.

**Implementation**:
1. Add a theory factory module:
```python
class TheoryFactory:
    """Factory for creating theory instances."""
    @staticmethod
    def create_theory(name, settings=None):
        """Create a theory instance by name."""
        settings = settings or {}
        if name == "default":
            from model_checker.theory_lib.default import (
                Semantics, Proposition, ModelStructure, default_operators
            )
            return {
                "semantics": Semantics(settings),
                "proposition": Proposition,
                "model": ModelStructure,
                "operators": default_operators,
            }
        elif name == "exclusion":
            # Similar structure for other theories
        else:
            raise ValueError(f"Unknown theory: {name}")
```

2. Use the factory in high-level API:
```python
def build_example(name, theory_name, settings=None):
    """Build an example with a specific theory."""
    theory = TheoryFactory.create_theory(theory_name, settings)
    return BuildExample(name, theory)
```

**Benefits**:
- Simplified API for common use cases
- No significant architectural changes
- Maintains backward compatibility
- Easier onboarding for new users

**Drawbacks**:
- Less flexibility than other approaches
- May not address deeper architectural issues
- Limited extensibility

### Strategy 6: Enhanced Operator System

**Goal**: Refactor the operator system to support more complex logical operators and reduce duplication.

**Implementation**:
1. Create an enhanced operator base with composition support:
```python
class EnhancedOperator:
    """Base class for logical operators with composition support."""
    def __init__(self, name, symbol, arity):
        self.name = name
        self.symbol = symbol
        self.arity = arity
        
    def compose(self, other_operator):
        """Create a new operator by composition."""
        return ComposedOperator(self, other_operator)
        
    # Core semantic methods
    
class ComposedOperator(EnhancedOperator):
    """An operator composed of multiple operators."""
    def __init__(self, outer, inner):
        self.outer = outer
        self.inner = inner
        super().__init__(
            f"{outer.name}_{inner.name}",
            f"{outer.symbol}({inner.symbol})",
            max(outer.arity, inner.arity)
        )
        
    # Implementation of semantic methods through composition
```

2. Create a centralized operator registry:
```python
class OperatorRegistry:
    """Central registry for operators across theories."""
    def __init__(self):
        self._operators = {}
        
    def register(self, operator, theory=None):
        """Register an operator, optionally with a theory."""
        key = (operator.name, theory)
        self._operators[key] = operator
        
    def get(self, name, theory=None):
        """Get an operator by name and optional theory."""
        return self._operators.get((name, theory)) or self._operators.get((name, None))
        
    def create_collection(self, theory=None):
        """Create an operator collection for a theory."""
        return {op.name: op for key, op in self._operators.items() 
                if key[1] == theory or key[1] is None}
```

**Benefits**:
- Reduced duplication across theory implementations
- Support for operator composition and transformation
- Centralized operator management
- Easier creation of derived operators

**Drawbacks**:
- Significant refactoring required
- Potential performance impact from abstraction
- May complicate simple theory implementations

### Strategy 7: Inheritance-Based Theory Structure

**Goal**: Refactor theories to use inheritance more effectively, allowing specialized theories to build on general ones.

**Implementation**:
1. Create a base theory module:
```python
class BaseSemantics:
    """Base semantics shared by all theories."""
    def __init__(self, settings):
        self.settings = settings
        # Common semantics implementation
        
class BaseProposition:
    """Base proposition logic shared by all theories."""
    def __init__(self, formula, model):
        self.formula = formula
        self.model = model
        # Common proposition implementation
```

2. Modify theories to inherit from base classes:
```python
# In default/semantic.py
from model_checker.base_theory import BaseSemantics, BaseProposition

class Semantics(BaseSemantics):
    """Default theory semantics."""
    def __init__(self, settings):
        super().__init__(settings)
        # Default-specific semantics
        
class Proposition(BaseProposition):
    """Default theory proposition logic."""
    def __init__(self, formula, model):
        super().__init__(formula, model)
        # Default-specific proposition logic
```

**Benefits**:
- Clear inheritance hierarchy
- Reduced code duplication
- Easier to create derivative theories
- Better code organization

**Drawbacks**:
- May force unnatural hierarchies in some cases
- Potential for "diamond problem" in multiple inheritance
- Requires careful design of base classes

### Strategy 8: API Facade Pattern

**Goal**: Create a simplified API facade that hides implementation details and provides a more intuitive interface.

**Implementation**:
1. Create a high-level API module:
```python
class ModelChecker:
    """High-level API for model checking."""
    def __init__(self, theory_name="default", settings=None):
        self.theory_name = theory_name
        self.settings = settings or {}
        self._theory = self._load_theory()
        
    def _load_theory(self):
        """Load the specified theory."""
        from model_checker.utils import get_theory
        from model_checker.theory_lib import get_examples
        theory = get_theory(self.theory_name)
        theory["examples"] = get_examples(self.theory_name)
        return theory
        
    def check_formula(self, formula, premises=None):
        """Check if a formula follows from premises."""
        example = self._create_example(premises, [formula])
        return self._check_example(example)
        
    def find_model(self, formulas):
        """Find a model satisfying all formulas."""
        example = self._create_example(formulas, [])
        return self._check_example(example)
        
    def _create_example(self, premises, conclusions):
        """Create an example from premises and conclusions."""
        premises = premises or []
        return [premises, conclusions, self.settings]
        
    def _check_example(self, example):
        """Check an example using BuildExample."""
        from model_checker import BuildExample
        model = BuildExample("custom", self._theory, example)
        return model.result
```

2. Use in simplified client code:
```python
from model_checker.api import ModelChecker

# Create a model checker with default theory
checker = ModelChecker()

# Check if a formula is valid
result = checker.check_formula("\\Box p -> p")
print(f"Formula is {'valid' if result else 'invalid'}")

# Find a model satisfying formulas
model = checker.find_model(["p", "q", "p -> q"])
print(f"Model found: {model}")
```

**Benefits**:
- Simplified API for common use cases
- Hides implementation details
- More intuitive for new users
- Can evolve independently of internal implementation

**Drawbacks**:
- Additional layer of abstraction
- May limit access to advanced features
- Potential duplication with existing BuildExample functionality

### Summary and Recommendations

The refactoring strategies above represent different approaches to improving the ModelChecker API, ranging from targeted enhancements to comprehensive architectural changes.

**Recommended short-term improvements:**
1. **Strategy 5 (Simplified Theory Factory)**: Provides immediate API improvements with minimal refactoring
2. **Strategy 4 (Module-Level Configuration)**: Addresses configuration inconsistencies without major structural changes
3. **Strategy 8 (API Facade Pattern)**: Creates a more user-friendly interface layer without changing internals

**Recommended medium-term improvements:**
1. **Strategy 1 (Standardized Theory Registry)**: Centralizes theory management and simplifies extension
2. **Strategy 6 (Enhanced Operator System)**: Reduces duplication in operator implementations
3. **Strategy 7 (Inheritance-Based Theory Structure)**: Improves code reuse between theories

**Recommended long-term improvements:**
1. **Strategy 2 (Protocol-based Theory Interface)**: Formalizes interfaces for more robust implementations
2. **Strategy 3 (Composable Model Components)**: Enables more flexible architecture for advanced use cases

For immediate API improvements with minimal disruption, implementing Strategy 5 (Simplified Theory Factory) alongside Strategy 8 (API Facade Pattern) would provide the best balance of improved usability and backward compatibility.

## NixOS Development Setup

When developing on NixOS, you may encounter issues with Python package imports and module resolution. Here are long-term solutions to improve the development experience:

### Development Environment Setup

Create a dedicated development environment that ensures your local source code is prioritized:

```python
# setup_dev.py
import os
import sys
import subprocess

# Get the absolute path to the src directory
src_path = os.path.abspath(os.path.join(os.path.dirname(__file__), 'src'))

# Create or modify .env file to set PYTHONPATH
with open('.env', 'w') as f:
    f.write(f'PYTHONPATH={src_path}:$PYTHONPATH\n')

# Try to create a development install
try:
    subprocess.run(['pip', 'install', '-e', '.', '--user'], check=True)
    print("Development installation successful")
except subprocess.CalledProcessError:
    print("Could not install package for development. You may need to run manually: pip install -e . --user")

print(f"Development environment set up. Run 'source .env' before development.")
print(f"Added {src_path} to PYTHONPATH")
```

### Development CLI Entry Point

Create a dedicated development CLI entry point that ensures it uses your local code:

```python
# dev_cli.py
#!/usr/bin/env python3
"""Development CLI entry point that ensures local code is used."""

import os
import sys

# Ensure local src is prioritized
src_path = os.path.abspath(os.path.join(os.path.dirname(__file__), 'src'))
sys.path.insert(0, src_path)

# Import all necessary modules explicitly from local source
try:
    from src.model_checker.__main__ import main
except ImportError as e:
    print(f"Error importing from local source: {e}")
    print(f"Current sys.path: {sys.path}")
    sys.exit(1)

if __name__ == "__main__":
    # Pass command line arguments
    sys.argv = [sys.argv[0]] + sys.argv[1:]
    main()
```

Make it executable:
```bash
chmod +x dev_cli.py
```

Usage:
```bash
./dev_cli.py path/to/example.py
```

### NixOS-specific Development Shell

Create a `shell.nix` file for a dedicated development environment:

```nix
{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = with pkgs; [
    python3
    python3Packages.z3
    python3Packages.pytest
    python3Packages.pip
    python3Packages.setuptools
    python3Packages.wheel
  ];
  
  shellHook = ''
    # Set up local development environment
    export PYTHONPATH="$PWD/src:$PYTHONPATH"
    export PATH="$PWD:$PATH"
    
    echo "ModelChecker development environment activated"
    echo "Run './dev_cli.py example.py' to use local source code"
  '';
}
```

Usage:
```bash
nix-shell  # Enter the development environment
./dev_cli.py examples.py  # Run with local source code
```

Combined with direnv, this provides a seamless development experience:

```bash
# .envrc
use_nix
```

Then:
```bash
direnv allow  # One-time setup
./dev_cli.py examples.py  # Automatically uses the correct environment
```

These solutions ensure that your local source code is always used during development, avoiding conflicts with installed packages.
