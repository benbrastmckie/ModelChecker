# Architecture: How Components Fit Together

[← Back to Docs](README.md) | [Workflow →](usage/WORKFLOW.md) | [Iterator →](methodology/ITERATOR.md) | [Technical Architecture →](../Code/docs/ARCHITECTURE.md)

> **Note**: This document provides a comprehensive educational overview of the ModelChecker's architecture and design philosophy. For a concise technical reference aimed at developers, see the [Technical Architecture Reference](../Code/docs/ARCHITECTURE.md).

## Table of Contents

1. [Introduction](#introduction)
2. [System Architecture Overview](#system-architecture-overview)
   - [Three-Tier Design](#three-tier-design)
   - [Component Responsibilities](#component-responsibilities)
   - [Data Flow Architecture](#data-flow-architecture)
   - [Extension Points](#extension-points)
3. [Core Components](#core-components)
   - [syntactic.py: AST and Operator System](#syntacticpy-ast-and-operator-system)
   - [model.py: Base Classes and Defaults](#modelpy-base-classes-and-defaults)
   - [builder/: Orchestration Layer](#builder-orchestration-layer)
   - [settings/: Configuration Management](#settings-configuration-management)
4. [Theory Architecture](#theory-architecture)
   - [Theory Module Structure](#theory-module-structure)
   - [Subtheory System](#subtheory-system)
   - [Operator Inheritance](#operator-inheritance)
   - [Settings Precedence](#settings-precedence)
5. [Iterator Architecture](#iterator-architecture)
   - [BaseModelIterator Framework](#basemodeliterator-framework)
   - [Theory-Specific Implementations](#theory-specific-implementations)
   - [Graph-Based Isomorphism](#graph-based-isomorphism)
   - [Progress and Statistics Subsystems](#progress-and-statistics-subsystems)
6. [Integration Points](#integration-points)
   - [CLI Command Structure](#cli-command-structure)
   - [Test Framework Hooks](#test-framework-hooks)
   - [Documentation Generation](#documentation-generation)
   - [Extension Mechanisms](#extension-mechanisms)
7. [Design Patterns](#design-patterns)
8. [Performance Architecture](#performance-architecture)
9. [References](#references)

## Introduction

The ModelChecker framework implements a sophisticated architecture for modal logic model checking, designed around principles of modularity, extensibility, and clean separation of concerns. The architecture supports arbitrary logical theories while maintaining a consistent computational pipeline from formula parsing through constraint generation to model solving.

This document explores the system's architectural design, component relationships, data flow patterns, and extension mechanisms that enable both framework users and developers to work effectively with the codebase.

## System Architecture Overview

### Three-Tier Design

The ModelChecker follows a three-tier architecture that cleanly separates concerns:

```
┌─────────────────────────────────────────────────────────┐
│                   Presentation Layer                    │
│                 (CLI, Output Formatting)                │
├─────────────────────────────────────────────────────────┤
│                    Business Logic Layer                 │
│          ┌────────────┬──────────────┬────────────┐     │
│          │   Syntax   │  Semantics   │   Solving  │     │
│          │  (Parsing) │ (Constraints)│    (Z3)    │     │
│          └────────────┴──────────────┴────────────┘     │
├─────────────────────────────────────────────────────────┤
│                      Data Layer                         │
│              (Theory Definitions, Examples)             │
└─────────────────────────────────────────────────────────┘
```

**Layer Responsibilities**:

1. **Presentation Layer**: Handles user interaction, command parsing, and result display
2. **Business Logic Layer**: Implements the core model checking pipeline
3. **Data Layer**: Stores theory implementations and example definitions

### Component Responsibilities

Each component has clearly defined responsibilities:

```
# Parsing Layer
syntactic.py      → Formula parsing and AST construction
operators.py      → Operator definitions and registry

# Semantic Layer  
model.py          → Base semantic classes and constraints
semantic.py       → Theory-specific semantic rules

# Solving Layer
model.py          → Z3 integration and solving
iterate/          → Multiple model generation

# Orchestration
builder/          → Pipeline coordination and execution
settings/         → Configuration management
```

### Data Flow Architecture

The system implements a unidirectional data flow:

```
Input Formula (string)
        ↓
[Tokenization] → Tokens
        ↓
[Parsing] → AST (prefix notation)
        ↓
[Sentence Creation] → Sentence objects
        ↓
[Operator Resolution] → Typed operators
        ↓
[Constraint Generation] → Z3 constraints
        ↓
[Solving] → Z3 model or unsat
        ↓
[Interpretation] → Evaluation results
        ↓
Output (formatted display)
```

### Extension Points

The architecture provides multiple extension points:

1. **New Theories**: Extend base semantic classes
2. **Custom Operators**: Implement Operator interface
3. **Output Formats**: Override display methods
4. **Constraint Types**: Add to proposition_constraints
5. **Settings**: Define theory-specific parameters

## Core Components

### syntactic.py: AST and Operator System

The syntactic module handles all parsing and AST operations:

```python
class Syntax:
    """Coordinates parsing and sentence management."""
    def __init__(self, premises, conclusions, operators):
        self.operators = operators
        self.sentence_letters = []  # Atomic propositions
        self.sentences = {}         # All sentence objects
        self.sentence_names = []    # Original formula strings
        
    def create_sentences(self):
        """Parse formulas and build sentence hierarchy."""
        # 1. Parse each formula to AST
        # 2. Create Sentence objects
        # 3. Identify atomic propositions
        # 4. Resolve operator references

class Sentence:
    """Represents a parsed formula with metadata."""
    def __init__(self, name=None, content=None, 
                 operator=None, operands=None):
        self.name = name              # Original string
        self.content = content        # Prefix notation
        self.complexity = 0           # Parse tree depth
        self.sentence_letter = None   # Z3 atom if atomic
        self.proposition = None       # Linked proposition
        
    def update_sentence_type(self, operator, operands):
        """Transform from atomic to complex sentence."""
        self.operator = operator
        self.operands = operands
        
class Operator:
    """Base class for all logical operators."""
    def __init__(self, semantics):
        self.semantics = semantics
        
    @abstractmethod
    def true_at(self, world, sentence, eval_point):
        """Define truth conditions."""
        pass
```

**Key Design Decisions**:
- Lazy operator binding (resolved after parsing)
- Sentence lifecycle with phased updates
- Operator registry pattern for extensibility

### model.py: Base Classes and Defaults

The model module provides semantic foundations:

```python
class SemanticDefaults:
    """Base semantic operations for all theories."""
    def __init__(self, settings):
        self.N = settings['N']
        self.setup_z3_primitives()
        
    def setup_z3_primitives(self):
        """Define core Z3 functions."""
        # State representation
        self.bv_sort = BitVecSort(self.N)
        
        # Core predicates
        self.possible = Function('possible', self.bv_sort, BoolSort())
        self.is_world = Function('is_world', self.bv_sort, BoolSort())
        
        # Mereological operations
        self.fusion = Function('fusion', self.bv_sort, self.bv_sort, self.bv_sort)
        self.is_part_of = Function('part', self.bv_sort, self.bv_sort, BoolSort())

class PropositionDefaults:
    """Manages atomic proposition constraints."""
    def proposition_constraints(self, sentence_letter):
        """Generate constraints for atomic propositions."""
        constraints = []
        
        # Classical logic (always applied)
        constraints.extend(self.get_classical_constraints())
        
        # Setting-dependent constraints
        if self.settings.get('contingent'):
            constraints.extend(self.get_contingent_constraints())
            
        return And(constraints)

class ModelConstraints:
    """Bridges syntax and semantics."""
    def __init__(self, settings, syntax, semantics, proposition_class):
        self.generate_all_constraints()
        
    def generate_all_constraints(self):
        """Create complete constraint set."""
        self.all_constraints = (
            self.frame_constraints +
            self.proposition_constraints +
            self.evaluation_constraints
        )

class ModelDefaults:
    """Handles solving and result interpretation."""
    def __init__(self, model_constraints, settings):
        self.setup_solver()
        self.solve()
        
    def solve(self):
        """Run Z3 solver with constraints."""
        self.solver.set("timeout", self.max_time * 1000)
        result = self.solver.check()
        
        if result == sat:
            self.z3_model = self.solver.model()
            self.extract_model_data()
```

**Key Design Patterns**:
- Template method pattern for constraint generation
- Strategy pattern for theory-specific behavior
- Clear separation of concerns

### builder/: Orchestration Layer

The builder package orchestrates the entire pipeline:

```python
# builder/module.py
class BuildModule:
    """Manages example execution across theories."""
    def __init__(self, module_flags):
        self.load_module()
        self.merge_settings()
        
    def process_example(self, name, case, theory_name, theory):
        """Execute single example through pipeline."""
        # 1. Create BuildExample
        # 2. Handle iteration if requested
        # 3. Display results
        # 4. Track statistics

# builder/example.py
class BuildExample:
    """Executes individual model checking example."""
    def __init__(self, build_module, semantic_theory, case, theory_name):
        self.validate_theory()
        self.extract_components()
        self.build_pipeline()
        
    def build_pipeline(self):
        """Construct processing pipeline."""
        # 1. Create SettingsManager
        # 2. Initialize Syntax
        # 3. Build ModelConstraints
        # 4. Solve with ModelStructure
        # 5. Interpret results

# builder/project.py
class BuildProject:
    """Generates new theory implementations."""
    def generate(self, project_name):
        # Copy template files
        # Customize for new theory
        # Set up test structure
```

**Orchestration Features**:
- Module loading and theory discovery
- Settings cascade and validation  
- Progress tracking and reporting
- Error handling and recovery

### settings/: Configuration Management

The settings system manages configuration hierarchy:

```python
class SettingsManager:
    """Validates and merges settings from multiple sources."""
    def __init__(self, semantic_defaults, general_settings, 
                 theory_name=None, is_comparison=False):
        self.determine_valid_settings()
        
    def get_complete_settings(self, raw_settings, example_settings, flags):
        """Merge settings with proper precedence."""
        # Priority (highest to lowest):
        # 1. Command-line flags
        # 2. Example-specific settings
        # 3. Module general_settings
        # 4. Theory defaults
        # 5. System defaults

# Setting validation
COMMON_SETTINGS = {
    'N': int,                  # State space size
    'max_time': float,         # Solver timeout
    'verbose': bool,           # Output verbosity
    'iterate': int,            # Model iteration count
}

THEORY_SPECIFIC = {
    'logos': {
        'contingent': bool,    # Contingent propositions
        'non_empty': bool,     # Non-empty verifiers
        'disjoint': bool,      # Disjoint verifier/falsifier
    },
    'exclusion': {
        'witness': bool,       # Witness predicates
        'coherence': bool,     # Coherence constraints
    }
}
```

## Theory Architecture

### Theory Module Structure

Each theory follows a standard structure:

```
theory_lib/logos/
├── __init__.py           # Theory registration
├── semantic.py           # Core semantic implementation
├── operators.py          # Operator definitions
├── examples.py           # Standard examples
├── tests/               # Unit tests
│   ├── test_semantic.py
│   ├── test_operators.py
│   └── test_examples.py
├── docs/                # Theory documentation
│   ├── README.md
│   ├── API_REFERENCE.md
│   └── USER_GUIDE.md
├── subtheories/         # Optional extensions
│   ├── modal/
│   ├── counterfactual/
│   └── constitutive/
└── iterate.py           # Model iteration logic
```

### Subtheory System

Theories can be composed from subtheories:

```python
# logos/__init__.py
def get_theory(subtheories=None):
    """Load theory with specified subtheories."""
    if subtheories is None:
        subtheories = ['modal', 'constitutive', 'counterfactual']
    
    # Create operator registry
    registry = LogosOperatorRegistry()
    registry.load_subtheories(subtheories)
    
    return {
        'semantics': LogosSemantics,
        'proposition': LogosProposition,
        'model': LogosModelStructure,
        'operators': registry.operators
    }

# Subtheory structure
subtheories/modal/
├── __init__.py
├── operators.py    # Modal operators (□, ◇)
└── examples.py     # Modal-specific examples
```

**Subtheory Benefits**:
- Modular operator loading
- Reduced complexity for simple uses
- Clear dependency management
- Easier testing and validation

### Operator Inheritance

Operators follow an inheritance hierarchy:

```python
# Base operator
class Operator(ABC):
    """Abstract base for all operators."""
    @abstractmethod
    def true_at(self, world, sentence, eval_point):
        pass

# Primitive operator
class NecessityOperator(Operator):
    """Box operator implementation."""
    def __init__(self, semantics):
        self.semantics = semantics
        self.symbol = "\\Box"
        
    def true_at(self, world, sentence, eval_point):
        # Check all accessible worlds
        return ForAll(w2, Implies(
            self.semantics.R(world, w2),
            sentence.operands[0].true_at(w2, eval_point)
        ))

# Defined operator
class StrictImplicationOperator(DefinedOperator):
    """A ⥽ B ≡ □(A → B)"""
    def __init__(self, semantics):
        super().__init__(
            symbol="\\strictimplies",
            definition="\\Box (A \\rightarrow B)",
            semantics=semantics
        )
```

### Settings Precedence

Settings follow a clear precedence hierarchy:

```
1. Command-line flags (highest priority)
   model-checker example.py --N=5 --verbose

2. Example-specific settings
   EXAMPLE_settings = {'N': 4, 'contingent': True}

3. Module general settings
   general_settings = {'max_time': 10}

4. Theory-specific defaults
   class LogosSemantics:
       default_settings = {'non_empty': False}

5. System defaults (lowest priority)
   DEFAULT_GENERAL_SETTINGS = {'N': 3, 'max_time': 1}
```

## Iterator Architecture

### BaseModelIterator Framework

The iterator system finds multiple distinct models:

```python
class BaseModelIterator:
    """Theory-agnostic iteration framework."""
    def __init__(self, build_example):
        self.validate_initial_model()
        self.setup_solver()
        
    def iterate(self):
        """Main iteration loop."""
        while self.current_iteration < self.max_iterations:
            # 1. Create difference constraints
            # 2. Solve for new model
            # 3. Check for isomorphism
            # 4. Handle invalid models
            # 5. Track progress
            
    # Abstract methods for theories
    @abstractmethod
    def _create_difference_constraint(self, previous_models):
        """Ensure new model differs semantically."""
        
    @abstractmethod
    def _calculate_differences(self, new_model, previous_model):
        """Identify semantic differences."""
```

### Theory-Specific Implementations

Each theory customizes iteration behavior:

```python
class LogosModelIterator(BaseModelIterator):
    """Logos-specific iteration logic."""
    
    def _create_difference_constraint(self, previous_models):
        """Focus on verification/falsification differences."""
        constraints = []
        for prev_model in previous_models:
            differences = []
            # Require different verification
            for state in self.all_states:
                for atom in self.atoms:
                    prev_verify = prev_model.eval(
                        self.semantics.verify(state, atom)
                    )
                    differences.append(
                        self.semantics.verify(state, atom) != prev_verify
                    )
            constraints.append(Or(differences))
        return And(constraints)

class ExclusionModelIterator(LogosModelIterator):
    """Adds exclusion-specific constraints."""
    
    def _create_difference_constraint(self, previous_models):
        # Include parent constraints
        base_constraints = super()._create_difference_constraint(previous_models)
        
        # Add exclusion differences
        exclusion_constraints = self._create_exclusion_constraints(previous_models)
        
        return And(base_constraints, exclusion_constraints)
```

### Graph-Based Isomorphism

Models are checked for structural equivalence:

```python
class ModelGraph:
    """Graph representation for isomorphism checking."""
    def __init__(self, model_structure, z3_model):
        self.graph = self._create_graph()
        
    def _create_graph(self):
        """Build NetworkX graph from model."""
        G = nx.DiGraph()
        
        # Add worlds as nodes
        for i, world in enumerate(self.world_states):
            properties = self._get_world_properties(world)
            G.add_node(i, **properties)
            
        # Add accessibility as edges
        for w1, w2 in self.accessibility_pairs:
            G.add_edge(w1, w2)
            
        return G
        
    def is_isomorphic(self, other_graph):
        """Check structural equivalence."""
        return nx.is_isomorphic(
            self.graph, 
            other_graph.graph,
            node_match=self._node_match
        )
```

### Progress and Statistics Subsystems

The iterator tracks progress and statistics:

```python
class IterationProgress:
    """Real-time progress display."""
    def update(self, found, checked):
        progress = found / self.total
        bar = self._create_progress_bar(progress)
        elapsed = time.time() - self.start_time
        print(f"\r{self.desc}: [{bar}] {found}/{self.total} "
              f"(checked {checked}) {elapsed:.1f}s", end="")

class IterationStatistics:
    """Collect model diversity metrics."""
    def add_model(self, model_structure, differences):
        self.model_stats.append({
            'world_count': len(model_structure.worlds),
            'difference_count': self._count_differences(differences),
            'timestamp': time.time()
        })
        
    def get_summary(self):
        return {
            'total_models': len(self.model_stats),
            'avg_worlds': statistics.mean(world_counts),
            'diversity': len(set(world_counts))
        }
```

## Integration Points

### CLI Command Structure

The CLI provides a clean interface:

```python
# __main__.py command routing
def main():
    parser = create_parser()
    args = parser.parse_args()
    
    if args.load_theory:
        # Generate new project
        BuildProject().generate(args.load_theory)
    else:
        # Run examples
        BuildModule(args).run()

# CLI argument structure
# Commands:
#   model-checker FILE            # Run example file
#   model-checker -l THEORY      # Generate project
#
# Options:
#   --N INT                      # State space size
#   --theory THEORY              # Select theory
#   --verbose                    # Detailed output
#   --iterate INT                # Find N models
#   --print-constraints          # Show Z3 constraints
```

### Test Framework Hooks

Testing integrates at multiple levels:

```python
# run_tests.py coordination
class TestRunner:
    """Unified test execution."""
    def run_all_tests(self):
        # 1. Example tests (integration)
        self.run_example_tests()
        
        # 2. Unit tests (components)
        self.run_unit_tests()
        
        # 3. Package tests (infrastructure)
        self.run_package_tests()

# Theory test structure
def test_theory_examples():
    """Validate theory against standard examples."""
    theory = get_theory()
    for example_name, example in unit_tests.items():
        result = check_example(theory, example)
        assert result.matches_expectation()

# Component testing
class TestSemantics:
    """Test semantic operations."""
    def test_fusion_associativity(self):
        # Verify mereological properties
        assert fusion(a, fusion(b, c)) == fusion(fusion(a, b), c)
```

### Documentation Generation

Documentation follows code structure:

```python
# Auto-generate API docs
def generate_api_docs(theory_path):
    """Extract docstrings and signatures."""
    for module in find_python_files(theory_path):
        classes = extract_classes(module)
        for cls in classes:
            doc = {
                'name': cls.__name__,
                'docstring': cls.__doc__,
                'methods': extract_methods(cls)
            }
            write_api_section(doc)

# Example documentation
def document_examples(theory):
    """Create example reference."""
    for name, example in examples.items():
        doc = analyze_example(example)
        write_example_doc(name, doc)
```

### Extension Mechanisms

The framework provides multiple extension points:

```python
# 1. Custom operators
class MyOperator(Operator):
    def true_at(self, world, sentence, eval_point):
        # Custom truth conditions
        pass

# 2. New constraint types
class MyProposition(PropositionDefaults):
    def proposition_constraints(self, letter):
        base = super().proposition_constraints(letter)
        custom = self.my_custom_constraints(letter)
        return And(base, custom)

# 3. Display customization
class MyModel(ModelDefaults):
    def print_model_structure(self, output):
        # Custom visualization
        pass

# 4. Settings extension
MY_THEORY_SETTINGS = {
    'my_parameter': bool,
    'my_threshold': int,
}
```

## Design Patterns

The architecture employs several design patterns:

### Template Method Pattern
```python
class ModelDefaults:
    def solve(self):
        """Template method for solving."""
        self.setup_solver()      # Hook
        self.add_constraints()   # Hook
        result = self.run_solver()
        self.process_result()    # Hook
```

### Strategy Pattern
```python
# Different semantic strategies
semantics_strategy = {
    'logos': LogosSemantics,
    'exclusion': ExclusionSemantics,
    'imposition': ImpositionSemantics
}
```

### Registry Pattern
```python
class OperatorRegistry:
    """Central operator registration."""
    def register(self, symbol, operator_class):
        self.operators[symbol] = operator_class
        
    def get(self, symbol):
        return self.operators[symbol]
```

### Builder Pattern
```python
class BuildExample:
    """Constructs model checking pipeline."""
    def __init__(self):
        self.with_settings()
        self.with_syntax()
        self.with_constraints()
        self.build()
```

## Performance Architecture

### Memory Management

The framework manages memory efficiently:

```python
# Lazy loading
def get_theory(name):
    """Load theory only when needed."""
    if name not in _loaded_theories:
        _loaded_theories[name] = import_theory(name)
    return _loaded_theories[name]

# Resource cleanup
class ModelDefaults:
    def __del__(self):
        """Clean up Z3 resources."""
        if hasattr(self, 'solver'):
            del self.solver
```

### Computation Optimization

Key optimizations include:

```python
# State space pruning
def generate_states(self):
    """Generate only reachable states."""
    reachable = set([self.initial_state])
    frontier = [self.initial_state]
    
    while frontier:
        state = frontier.pop()
        for next_state in self.successors(state):
            if next_state not in reachable:
                reachable.add(next_state)
                frontier.append(next_state)

# Constraint ordering
def order_constraints(constraints):
    """Place simple constraints first."""
    return sorted(constraints, key=constraint_complexity)

# Incremental solving
def solve_incrementally(self):
    """Add constraints gradually."""
    self.solver.push()
    for constraint in self.constraints:
        self.solver.add(constraint)
        if self.solver.check() == unsat:
            break
```

### Parallel Processing

Where applicable, use parallelism:

```python
# Parallel theory comparison
def compare_theories_parallel(theories, examples):
    with multiprocessing.Pool() as pool:
        results = pool.starmap(
            check_theory_example,
            [(t, e) for t in theories for e in examples]
        )
    return aggregate_results(results)
```

## References

### Design Influences
- **Clean Architecture** (Robert C. Martin) - Layer separation
- **Domain-Driven Design** (Eric Evans) - Theory as domain
- **SOLID Principles** - Interface design

### Implementation Patterns
- **Z3 Tutorial** - Constraint generation patterns
- **NetworkX Documentation** - Graph algorithms
- **Python Design Patterns** - Architectural patterns

### Related Documentation
- [Builder Pattern](methodology/BUILDER.md) - Detailed orchestration with component integration flowcharts
- [Iterator System](methodology/ITERATOR.md) - Model iteration architecture
- [Theory Architecture](../../Code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md) - Theory design

---

[← Back to Docs](README.md) | [Workflow →](usage/WORKFLOW.md) | [Iterator →](methodology/ITERATOR.md)
