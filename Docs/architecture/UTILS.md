# Shared Utilities & Patterns Architecture

[← Back to Architecture](README.md) | [Theory Framework →](THEORY_LIB.md) | [Pipeline →](PIPELINE.md)

## Overview

The Utils package provides foundational utilities and shared patterns that support the entire ModelChecker framework. These utilities handle critical cross-cutting concerns including expression parsing, bit vector operations, Z3 context management, output formatting, and type safety enforcement throughout the system.

## Utility Architecture

```mermaid
graph TB
    subgraph "Core Utilities"
        Types[Type Definitions]
        Parsing[Expression Parser]
        BitVector[Bit Vector Ops]
        Context[Z3 Context Manager]
    end
    
    subgraph "Support Utilities"
        Formatting[Output Formatter]
        API[API Functions]
        Testing[Test Runner]
        Version[Version Manager]
    end
    
    subgraph "Helper Functions"
        Z3Helpers[Z3 Helpers]
        ErrorHandling[Error Handlers]
        Validation[Validators]
    end
    
    subgraph "Consumer Modules"
        Syntactic[Syntactic Module]
        Semantic[Semantic Theories]
        Builder[Builder Module]
        Output[Output Module]
    end
    
    Types --> Parsing
    Types --> BitVector
    Types --> Context
    
    Parsing --> Syntactic
    BitVector --> Semantic
    Context --> Builder
    Formatting --> Output
    
    Z3Helpers --> Context
    ErrorHandling --> API
    Validation --> Testing
```

## Type System Architecture

### Type Safety Framework

```mermaid
classDiagram
    class TypeDefinitions {
        <<module>>
        +Z3Expr: Union[BoolRef, ArithRef, ...]
        +Z3Sort: Union[BoolSort, BitVecSort, ...]
        +PathLike: Union[str, Path]
        +ConfigDict: Dict[str, Any]
        +TableRow: List[str]
        +TableData: List[TableRow]
        +VersionTuple: Tuple[int, int, int]
    }
    
    class TypedFunctions {
        <<pattern>>
        +parse_expression(tokens: List[str]) -> Tuple[List, int]
        +bitvector_to_dict(bitvec: BitVecRef) -> Dict[int, bool]
        +format_set(items: Set) -> str
    }
    
    class TypeValidation {
        <<utilities>>
        +validate_z3_expr(expr: Any) -> Z3Expr
        +ensure_path(path: PathLike) -> Path
        +check_config(config: ConfigDict) -> bool
    }
    
    TypeDefinitions --> TypedFunctions
    TypedFunctions --> TypeValidation
```

## Expression Parsing Architecture

### Parser Pipeline

```mermaid
flowchart LR
    subgraph "Input Processing"
        InfixExpr[Infix Expression<br/>"A ∧ B → C"]
        Tokenizer[Tokenizer]
        TokenList[Token List<br/>['A', '∧', 'B', '→', 'C']]
    end
    
    subgraph "Parsing Engine"
        ShuntingYard[Shunting Yard Algorithm]
        PrefixConverter[Prefix Converter]
        ComplexityCalc[Complexity Calculator]
    end
    
    subgraph "Output Generation"
        PrefixNotation[Prefix Notation<br/>['→', ['∧', 'A', 'B'], 'C']]
        Complexity[Complexity Score<br/>2]
    end
    
    InfixExpr --> Tokenizer
    Tokenizer --> TokenList
    TokenList --> ShuntingYard
    ShuntingYard --> PrefixConverter
    PrefixConverter --> ComplexityCalc
    ComplexityCalc --> PrefixNotation
    ComplexityCalc --> Complexity
```

### Operator Precedence Handling

```mermaid
graph TD
    subgraph "Precedence Levels"
        Level1["Level 1 (Highest)<br/>¬, □, ◇"]
        Level2["Level 2<br/>∧, ∨"]
        Level3["Level 3<br/>→, ↔"]
        Level4["Level 4 (Lowest)<br/>⇒, ⇏"]
    end
    
    subgraph "Parsing Rules"
        LeftAssoc[Left Associative]
        RightAssoc[Right Associative]
        Unary[Unary Prefix]
    end
    
    Level1 --> Unary
    Level2 --> LeftAssoc
    Level3 --> RightAssoc
    Level4 --> RightAssoc
```

## Bit Vector Operations

### State Representation

```mermaid
graph LR
    subgraph "State Encoding"
        StateIndex[State Index<br/>e.g., 5]
        BitVector[Bit Vector<br/>0b0101]
        BitPositions[Bit Positions<br/>[0,2]]
    end
    
    subgraph "Operations"
        Extract[Extract Bits]
        Combine[Combine States]
        Test[Test Membership]
        Convert[Convert Format]
    end
    
    subgraph "Applications"
        Verifiers[Verifier Sets]
        Falsifiers[Falsifier Sets]
        Relations[Accessibility Relations]
    end
    
    StateIndex --> BitVector
    BitVector --> Extract
    Extract --> BitPositions
    
    BitPositions --> Combine
    Combine --> Verifiers
    Combine --> Falsifiers
    Test --> Relations
    Convert --> BitPositions
```

### Bit Vector Utilities

```mermaid
flowchart TB
    subgraph "Core Functions"
        ToDict["bitvector_to_dict()<br/>Convert to dictionary"]
        ToSet["bitvector_to_set()<br/>Convert to set"]
        Extract["extract_bitvector_const()<br/>Extract constant value"]
    end
    
    subgraph "Helper Functions"
        TestBit["test_bit()<br/>Check bit position"]
        SetBit["set_bit()<br/>Set bit value"]
        CountBits["count_bits()<br/>Count set bits"]
    end
    
    subgraph "Advanced Operations"
        Intersect["intersect_bitvectors()<br/>Set intersection"]
        Union["union_bitvectors()<br/>Set union"]
        Diff["diff_bitvectors()<br/>Set difference"]
    end
    
    ToDict --> TestBit
    ToSet --> CountBits
    Extract --> TestBit
    
    Intersect --> SetBit
    Union --> SetBit
    Diff --> SetBit
```

## Z3 Context Management

### Context Isolation Architecture

```mermaid
sequenceDiagram
    participant User
    participant ContextManager
    participant Z3Context
    participant Solver
    participant Cleanup
    
    User->>ContextManager: Request new context
    ContextManager->>Z3Context: Create isolated context
    Z3Context-->>ContextManager: Context handle
    ContextManager-->>User: Context ready
    
    User->>Solver: Add constraints
    Solver->>Z3Context: Use isolated context
    Z3Context-->>Solver: Execute in context
    Solver-->>User: Return results
    
    User->>ContextManager: Release context
    ContextManager->>Cleanup: Clean up resources
    Cleanup->>Z3Context: Destroy context
    Z3Context-->>ContextManager: Context freed
```

### Resource Management

```mermaid
graph TD
    subgraph "Context Lifecycle"
        Create[Create Context]
        Configure[Configure Solver]
        Use[Use for Solving]
        Release[Release Resources]
    end
    
    subgraph "Isolation Guarantees"
        ThreadSafe[Thread Safety]
        MemoryIsolation[Memory Isolation]
        SolverIndependence[Solver Independence]
    end
    
    subgraph "Performance"
        ContextPool[Context Pool]
        Reuse[Context Reuse]
        GarbageCollection[Garbage Collection]
    end
    
    Create --> Configure
    Configure --> Use
    Use --> Release
    
    ThreadSafe --> Create
    MemoryIsolation --> Use
    SolverIndependence --> Configure
    
    Release --> ContextPool
    ContextPool --> Reuse
    Reuse --> GarbageCollection
```

## Output Formatting System

### Formatting Pipeline

```mermaid
flowchart LR
    subgraph "Input Data"
        RawData[Raw Data<br/>Sets, Models, Results]
        Metadata[Metadata<br/>Settings, Context]
    end
    
    subgraph "Formatting Engine"
        Detector[Type Detector]
        Formatter[Format Selector]
        Renderer[Render Engine]
    end
    
    subgraph "Output Formats"
        PlainText[Plain Text]
        Markdown[Markdown]
        JSON[JSON]
        LaTeX[LaTeX]
        HTML[HTML Tables]
    end
    
    RawData --> Detector
    Metadata --> Detector
    Detector --> Formatter
    Formatter --> Renderer
    
    Renderer --> PlainText
    Renderer --> Markdown
    Renderer --> JSON
    Renderer --> LaTeX
    Renderer --> HTML
```

### Pretty Printing Architecture

```mermaid
graph TB
    subgraph "Data Types"
        Sets[Set Objects]
        Dicts[Dictionaries]
        Lists[Lists/Arrays]
        Models[Model Objects]
    end
    
    subgraph "Formatting Rules"
        Indentation[Indentation Logic]
        LineBreaking[Line Breaking]
        Alignment[Column Alignment]
        Coloring[Color Coding]
    end
    
    subgraph "Output Styles"
        Compact[Compact Format]
        Verbose[Verbose Format]
        Table[Tabular Format]
        Tree[Tree Format]
    end
    
    Sets --> Indentation
    Dicts --> LineBreaking
    Lists --> Alignment
    Models --> Coloring
    
    Indentation --> Compact
    LineBreaking --> Verbose
    Alignment --> Table
    Coloring --> Tree
```

## API Function Architecture

### Theory and Example Access

```mermaid
graph TD
    subgraph "API Layer"
        GetTheory[get_theory()]
        GetExample[get_example()]
        ListTheories[list_theories()]
        ListExamples[list_examples()]
    end
    
    subgraph "Registry Access"
        TheoryRegistry[Theory Registry]
        ExampleRegistry[Example Registry]
        ModuleLoader[Module Loader]
    end
    
    subgraph "Validation"
        ValidateTheory[Validate Theory]
        ValidateExample[Validate Example]
        CheckDependencies[Check Dependencies]
    end
    
    GetTheory --> TheoryRegistry
    GetExample --> ExampleRegistry
    ListTheories --> TheoryRegistry
    ListExamples --> ExampleRegistry
    
    TheoryRegistry --> ValidateTheory
    ExampleRegistry --> ValidateExample
    ModuleLoader --> CheckDependencies
```

## Testing Utilities

### Test Runner Architecture

```mermaid
flowchart TB
    subgraph "Test Discovery"
        ScanModules[Scan Test Modules]
        CollectTests[Collect Test Cases]
        FilterTests[Apply Filters]
    end
    
    subgraph "Test Execution"
        SetupFixtures[Setup Fixtures]
        RunTest[Run Test Case]
        CaptureOutput[Capture Output]
        ValidateResult[Validate Result]
    end
    
    subgraph "Result Analysis"
        CompareExpected[Compare Expected]
        GenerateReport[Generate Report]
        CalculateMetrics[Calculate Metrics]
    end
    
    ScanModules --> CollectTests
    CollectTests --> FilterTests
    FilterTests --> SetupFixtures
    
    SetupFixtures --> RunTest
    RunTest --> CaptureOutput
    CaptureOutput --> ValidateResult
    
    ValidateResult --> CompareExpected
    CompareExpected --> GenerateReport
    GenerateReport --> CalculateMetrics
```

## Error Handling Patterns

### Error Processing Flow

```mermaid
flowchart TD
    subgraph "Error Detection"
        TryCatch[Try-Catch Block]
        Validation[Input Validation]
        Assertion[Assertions]
    end
    
    subgraph "Error Classification"
        ParseError[Parse Errors]
        Z3Error[Z3 Solver Errors]
        ValidationError[Validation Errors]
        TimeoutError[Timeout Errors]
    end
    
    subgraph "Error Response"
        LogError[Log Error]
        FormatMessage[Format Message]
        RecoveryAction[Recovery Action]
        UserFeedback[User Feedback]
    end
    
    TryCatch --> ParseError
    Validation --> ValidationError
    Assertion --> Z3Error
    
    ParseError --> LogError
    Z3Error --> FormatMessage
    ValidationError --> RecoveryAction
    TimeoutError --> UserFeedback
```

## Version Management

### Version Control System

```mermaid
graph LR
    subgraph "Version Components"
        Major[Major Version]
        Minor[Minor Version]
        Patch[Patch Version]
        Build[Build Number]
    end
    
    subgraph "Version Operations"
        Parse[Parse Version]
        Compare[Compare Versions]
        Increment[Increment Version]
        Format[Format String]
    end
    
    subgraph "Compatibility"
        CheckCompat[Check Compatibility]
        MinVersion[Minimum Version]
        MaxVersion[Maximum Version]
    end
    
    Major --> Parse
    Minor --> Parse
    Patch --> Parse
    Build --> Parse
    
    Parse --> Compare
    Compare --> CheckCompat
    Increment --> Format
    CheckCompat --> MinVersion
    CheckCompat --> MaxVersion
```

## Integration Patterns

### Cross-Module Dependencies

```mermaid
graph TB
    subgraph "Utils Dependencies"
        UtilTypes[Types Module]
        UtilParsing[Parsing Module]
        UtilBitVector[BitVector Module]
        UtilContext[Context Module]
    end
    
    subgraph "Framework Modules"
        Syntactic[Syntactic]
        Semantic[Semantic]
        Builder[Builder]
        Output[Output]
        Iterate[Iterate]
    end
    
    UtilTypes --> Syntactic
    UtilTypes --> Semantic
    UtilTypes --> Builder
    
    UtilParsing --> Syntactic
    UtilBitVector --> Semantic
    UtilBitVector --> Iterate
    
    UtilContext --> Builder
    UtilContext --> Iterate
```

## Performance Considerations

### Optimization Strategies

```mermaid
graph TD
    subgraph "Caching"
        ParseCache[Parse Result Cache]
        FormatCache[Format Cache]
        ContextCache[Context Pool]
    end
    
    subgraph "Lazy Evaluation"
        LazyImport[Lazy Module Import]
        LazyCompute[Lazy Computation]
        LazyFormat[Lazy Formatting]
    end
    
    subgraph "Resource Management"
        PooledContexts[Pooled Contexts]
        RecycledObjects[Recycled Objects]
        MemoryLimits[Memory Limits]
    end
    
    ParseCache --> LazyCompute
    FormatCache --> LazyFormat
    ContextCache --> PooledContexts
    
    LazyImport --> MemoryLimits
    RecycledObjects --> MemoryLimits
```

## Best Practices

### Design Principles

1. **Type Safety First**: Use comprehensive type hints for all functions
2. **Fail Fast**: Validate inputs early and provide clear error messages
3. **Resource Efficiency**: Pool and reuse expensive resources like Z3 contexts
4. **Clear Interfaces**: Provide simple, intuitive APIs for common operations
5. **Extensibility**: Design utilities to be easily extended or customized

### Implementation Guidelines

1. **Single Responsibility**: Each utility function should do one thing well
2. **Pure Functions**: Prefer pure functions without side effects where possible
3. **Error Handling**: Provide informative error messages with recovery suggestions
4. **Documentation**: Include usage examples in all function docstrings
5. **Testing**: Maintain comprehensive test coverage for all utilities

## Technical Implementation

For detailed implementation information, see:
- [Utils Package Documentation](../../Code/src/model_checker/utils/README.md)
- [Type Definitions](../../Code/src/model_checker/utils/types.py)
- [API Reference](../../Code/src/model_checker/utils/api.py)

## See Also

- [Pipeline Architecture](PIPELINE.md) - System-wide data flow
- [Builder Architecture](BUILDER.md) - Pipeline orchestration
- [Settings Management](SETTINGS.md) - Configuration utilities

---

[← Back to Architecture](README.md) | [Theory Framework →](THEORY_LIB.md) | [Pipeline →](PIPELINE.md)