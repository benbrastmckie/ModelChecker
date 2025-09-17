# Theory Framework Architecture

[← Back to Architecture](README.md) | [Jupyter →](JUPYTER.md) | [Utils →](UTILS.md)

## Overview

The Theory Library provides a modular framework for implementing different semantic theories as computational programs. Each theory translates logical operators and their truth conditions into Z3 constraints, enabling automated model checking across diverse semantic approaches including modal, counterfactual, and hyperintensional logic.

## Framework Architecture

```mermaid
graph TB
    subgraph "Theory Interface Layer"
        BaseTheory[Base Theory Interface]
        TheoryRegistry[Theory Registry]
        TheoryLoader[Theory Loader]
    end
    
    subgraph "Theory Implementations"
        Logos[Logos Theory]
        Exclusion[Exclusion Theory]
        Imposition[Imposition Theory]
        Bimodal[Bimodal Theory]
    end
    
    subgraph "Semantic Components"
        Operators[Operator Definitions]
        Constraints[Constraint Generators]
        ModelStructure[Model Structures]
    end
    
    subgraph "Z3 Integration"
        Variables[Z3 Variables]
        Assertions[Z3 Assertions]
        Solver[Z3 Solver]
    end
    
    BaseTheory --> TheoryRegistry
    TheoryRegistry --> TheoryLoader
    TheoryLoader --> Logos
    TheoryLoader --> Exclusion
    TheoryLoader --> Imposition
    TheoryLoader --> Bimodal
    
    Logos --> Operators
    Exclusion --> Operators
    Imposition --> Operators
    Bimodal --> Operators
    
    Operators --> Constraints
    Constraints --> ModelStructure
    ModelStructure --> Variables
    Variables --> Assertions
    Assertions --> Solver
```

## Theory Design Patterns

### Simple Theory Pattern

Used for focused theories with cohesive operator sets:

```mermaid
classDiagram
    class SimpleTheory {
        +name: str
        +operators: dict
        +defaults: dict
        +generate_constraints()
        +validate_settings()
        +get_operators()
    }
    
    class ExclusionTheory {
        +witness_constraints()
        +exclusion_operators()
        +negation_semantics()
    }
    
    class ImpositionTheory {
        +imposition_operator()
        +could_operator()
        +counterfactual_semantics()
    }
    
    SimpleTheory <|-- ExclusionTheory
    SimpleTheory <|-- ImpositionTheory
```

### Modular Theory Pattern

Used for complex theories with multiple subtheories:

```mermaid
graph TD
    subgraph "Logos Modular Architecture"
        LogosBase[Logos Base]
        
        subgraph "Subtheories"
            Extensional[Extensional Module]
            Modal[Modal Module]
            Constitutive[Constitutive Module]
            Counterfactual[Counterfactual Module]
            Relevance[Relevance Module]
        end
        
        LogosBase --> Extensional
        LogosBase --> Modal
        LogosBase --> Constitutive
        LogosBase --> Counterfactual
        LogosBase --> Relevance
    end
    
    subgraph "Selective Loading"
        LoadRequest["logos.get_theory(['modal', 'extensional'])"]
        ModuleSelector[Module Selector]
        CombinedTheory[Combined Theory]
    end
    
    LoadRequest --> ModuleSelector
    ModuleSelector --> Modal
    ModuleSelector --> Extensional
    Modal --> CombinedTheory
    Extensional --> CombinedTheory
```

## Operator Architecture

### Operator Definition Flow

```mermaid
flowchart LR
    subgraph "Operator Definition"
        Name[Operator Name]
        Symbol[Symbol/Notation]
        Arity[Arity/Type]
        Precedence[Precedence]
    end
    
    subgraph "Semantic Rules"
        TruthConditions[Truth Conditions]
        Constraints[Z3 Constraints]
        ModelRequirements[Model Requirements]
    end
    
    subgraph "Implementation"
        Method[Theory Method]
        Variables[Variable Creation]
        Assertions[Assert Generation]
    end
    
    Name --> Method
    Symbol --> Method
    Arity --> Method
    Precedence --> Method
    
    Method --> TruthConditions
    TruthConditions --> Constraints
    Constraints --> Variables
    Variables --> Assertions
    ModelRequirements --> Assertions
```

### Operator Types

```mermaid
graph TB
    subgraph "Operator Categories"
        Propositional[Propositional<br/>∧, ∨, →, ¬]
        Modal[Modal<br/>□, ◇, ○, ●]
        Counterfactual[Counterfactual<br/>⇒, ⇏, ∈, ∉]
        Hyperintensional[Hyperintensional<br/>≈, ≺, ⊑, ⊒]
        Temporal[Temporal<br/>G, F, X, U]
    end
    
    subgraph "Semantic Properties"
        Unary[Unary Operators]
        Binary[Binary Operators]
        Quantified[Quantified Forms]
        Indexed[Indexed Operators]
    end
    
    Propositional --> Binary
    Modal --> Unary
    Counterfactual --> Binary
    Hyperintensional --> Binary
    Temporal --> Unary
    Temporal --> Binary
    Modal --> Quantified
    Counterfactual --> Indexed
```

## Constraint Generation

### From Formula to Constraints

```mermaid
sequenceDiagram
    participant Formula
    participant Parser
    participant Theory
    participant ConstraintGen
    participant Z3Builder
    participant Solver
    
    Formula->>Parser: Parse formula
    Parser->>Theory: Get operator semantics
    Theory->>ConstraintGen: Generate constraints
    
    loop For each operator
        ConstraintGen->>Theory: Get truth conditions
        Theory-->>ConstraintGen: Semantic rules
        ConstraintGen->>Z3Builder: Create Z3 expressions
    end
    
    Z3Builder->>Solver: Add assertions
    Solver-->>Theory: SAT/UNSAT result
```

### Constraint Types

```mermaid
graph TD
    subgraph "Structural Constraints"
        States[State Structure]
        Accessibility[Accessibility Relations]
        Valuations[Atomic Valuations]
    end
    
    subgraph "Semantic Constraints"
        TruthConditions[Truth Conditions]
        ModalConditions[Modal Conditions]
        CounterfactualConditions[Counterfactual Rules]
    end
    
    subgraph "Theory-Specific"
        Witnesses[Witness Predicates]
        Truthmakers[Truthmaker Relations]
        Exclusions[Exclusion Operations]
    end
    
    States --> TruthConditions
    Accessibility --> ModalConditions
    Valuations --> TruthConditions
    
    TruthConditions --> Witnesses
    ModalConditions --> Truthmakers
    CounterfactualConditions --> Exclusions
```

## Model Structure Integration

### Theory-Model Interface

```mermaid
classDiagram
    class Model {
        +states: Set
        +relations: Dict
        +valuations: Dict
        +verify_constraints()
    }
    
    class TheoryModel {
        <<interface>>
        +add_theory_constraints()
        +validate_structure()
        +interpret_results()
    }
    
    class LogosModel {
        +verifiers: Dict
        +falsifiers: Dict
        +add_truthmaker_constraints()
    }
    
    class ExclusionModel {
        +witnesses: Dict
        +add_witness_constraints()
    }
    
    class BimodalModel {
        +histories: Dict
        +times: Set
        +add_temporal_constraints()
    }
    
    Model <|-- TheoryModel
    TheoryModel <|-- LogosModel
    TheoryModel <|-- ExclusionModel
    TheoryModel <|-- BimodalModel
```

## Theory Registration

### Dynamic Theory Loading

```mermaid
flowchart TD
    Start[Application Start] --> Registry[Initialize Registry]
    Registry --> Scan[Scan Theory Modules]
    
    Scan --> Found{Theory Found?}
    Found -->|Yes| Validate[Validate Interface]
    Found -->|No| Continue[Continue Scan]
    
    Validate --> Valid{Valid Theory?}
    Valid -->|Yes| Register[Register Theory]
    Valid -->|No| Log[Log Warning]
    
    Register --> Store[Store in Registry]
    Log --> Continue
    Continue --> More{More Modules?}
    More -->|Yes| Scan
    More -->|No| Complete[Registry Complete]
    
    Complete --> Available[Available for Use]
```

### Theory Discovery

```mermaid
graph LR
    subgraph "Discovery Process"
        ModuleImport[Import Modules]
        InterfaceCheck[Check Interface]
        CapabilityDetect[Detect Capabilities]
        Register[Register Theory]
    end
    
    subgraph "Registry Storage"
        TheoryMap[Theory Name Map]
        OperatorIndex[Operator Index]
        DefaultsCache[Defaults Cache]
        ValidationRules[Validation Rules]
    end
    
    ModuleImport --> InterfaceCheck
    InterfaceCheck --> CapabilityDetect
    CapabilityDetect --> Register
    
    Register --> TheoryMap
    Register --> OperatorIndex
    Register --> DefaultsCache
    Register --> ValidationRules
```

## Extension Architecture

### Adding New Theories

```mermaid
flowchart TB
    subgraph "Implementation Steps"
        Define[Define Theory Class]
        Implement[Implement Interface]
        Operators[Add Operators]
        Constraints[Define Constraints]
        Test[Write Tests]
        Document[Create Documentation]
    end
    
    subgraph "Interface Requirements"
        BaseClass[Inherit Base Theory]
        RequiredMethods[Implement Required Methods]
        OperatorDict[Define Operator Dictionary]
        DefaultSettings[Provide Defaults]
    end
    
    subgraph "Integration"
        AutoDiscovery[Auto-Discovery]
        Registration[Manual Registration]
        Validation[Validation Tests]
    end
    
    Define --> BaseClass
    Implement --> RequiredMethods
    Operators --> OperatorDict
    Constraints --> RequiredMethods
    Test --> Validation
    Document --> Registration
    
    RequiredMethods --> AutoDiscovery
    OperatorDict --> AutoDiscovery
    DefaultSettings --> AutoDiscovery
```

## Theory Comparison

### Cross-Theory Analysis

```mermaid
graph TB
    subgraph "Comparison Framework"
        FormulaInput[Common Formula]
        TheoryA[Theory A]
        TheoryB[Theory B]
        TheoryC[Theory C]
    end
    
    subgraph "Analysis"
        ModelA[Models from A]
        ModelB[Models from B]
        ModelC[Models from C]
        Compare[Comparison Engine]
    end
    
    subgraph "Results"
        Differences[Semantic Differences]
        Agreements[Common Results]
        Insights[Theoretical Insights]
    end
    
    FormulaInput --> TheoryA
    FormulaInput --> TheoryB
    FormulaInput --> TheoryC
    
    TheoryA --> ModelA
    TheoryB --> ModelB
    TheoryC --> ModelC
    
    ModelA --> Compare
    ModelB --> Compare
    ModelC --> Compare
    
    Compare --> Differences
    Compare --> Agreements
    Compare --> Insights
```

## Performance Optimization

### Theory-Specific Optimizations

```mermaid
graph LR
    subgraph "Optimization Strategies"
        ConstraintOrder[Constraint Ordering]
        VariableReduction[Variable Reduction]
        SymmetryBreaking[Symmetry Breaking]
        IncrementalSolving[Incremental Solving]
    end
    
    subgraph "Theory Adaptations"
        LogosOpt[Logos: Verifier Grouping]
        ExclusionOpt[Exclusion: Witness Caching]
        BimodalOpt[Bimodal: Time Indexing]
        ImpositionOpt[Imposition: State Pruning]
    end
    
    ConstraintOrder --> LogosOpt
    VariableReduction --> ExclusionOpt
    SymmetryBreaking --> BimodalOpt
    IncrementalSolving --> ImpositionOpt
```

## Testing Architecture

### Theory Test Framework

```mermaid
graph TD
    subgraph "Test Categories"
        UnitTests[Unit Tests]
        IntegrationTests[Integration Tests]
        SemanticTests[Semantic Tests]
        PerformanceTests[Performance Tests]
    end
    
    subgraph "Test Data"
        ValidFormulas[Valid Formulas]
        InvalidFormulas[Invalid Formulas]
        EdgeCases[Edge Cases]
        Benchmarks[Benchmark Sets]
    end
    
    subgraph "Validation"
        OperatorTests[Operator Behavior]
        ConstraintTests[Constraint Generation]
        ModelTests[Model Validity]
        ComparisonTests[Theory Comparison]
    end
    
    ValidFormulas --> UnitTests
    InvalidFormulas --> IntegrationTests
    EdgeCases --> SemanticTests
    Benchmarks --> PerformanceTests
    
    UnitTests --> OperatorTests
    IntegrationTests --> ConstraintTests
    SemanticTests --> ModelTests
    PerformanceTests --> ComparisonTests
```

## Best Practices

### Theory Implementation Guidelines

1. **Interface Compliance**: Implement all required base theory methods
2. **Operator Consistency**: Maintain consistent operator naming and behavior
3. **Constraint Efficiency**: Optimize constraint generation for solver performance
4. **Documentation**: Provide clear semantic descriptions and examples
5. **Testing Coverage**: Include comprehensive test cases for all operators

### Design Principles

1. **Modularity**: Keep theories independent and composable
2. **Extensibility**: Design for easy addition of new operators
3. **Performance**: Balance semantic completeness with computational efficiency
4. **Clarity**: Prioritize clear semantic definitions over implementation cleverness
5. **Compatibility**: Ensure theories work with the full ModelChecker pipeline

## Technical Implementation

For detailed implementation information, see:
- [Theory Library Documentation](../../Code/src/model_checker/theory_lib/README.md)
- [Theory Architecture Guide](../../Code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md)
- [Contributing Guide](../../Code/src/model_checker/theory_lib/docs/CONTRIBUTING.md)

## See Also

- [Semantic Framework](SEMANTICS.md) - Core semantic processing
- [Model Structure](MODELS.md) - Model representation architecture
- [Builder Pipeline](BUILDER.md) - Theory integration in pipeline

---

[← Back to Architecture](README.md) | [Jupyter →](JUPYTER.md) | [Utils →](UTILS.md)