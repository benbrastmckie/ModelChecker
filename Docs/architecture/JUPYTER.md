# Interactive Exploration Architecture

[← Back to Architecture](README.md) | [Theory Framework →](THEORY_LIB.md) | [Utils →](UTILS.md)

## Overview

The Jupyter integration provides an interactive environment for exploring logical models, testing formulas, and visualizing semantic structures. This architecture enables researchers and students to experiment with model theory concepts through intuitive interfaces and real-time feedback.

## System Architecture

```mermaid
graph TB
    subgraph "User Interface Layer"
        Notebook[Jupyter Notebook]
        Widgets[IPython Widgets]
        Explorer[Interactive Explorer]
    end
    
    subgraph "Integration Layer"
        API[High-Level API]
        Adapters[Theory Adapters]
        Display[Display Formatters]
    end
    
    subgraph "Core Framework"
        Builder[Builder Pipeline]
        Theory[Theory Engine]
        Models[Model Generator]
    end
    
    subgraph "Visualization"
        Graphs[Graph Rendering]
        Tables[Truth Tables]
        LaTeX[LaTeX Output]
    end
    
    Notebook --> API
    Widgets --> Explorer
    Explorer --> API
    API --> Adapters
    Adapters --> Builder
    Builder --> Theory
    Theory --> Models
    Models --> Display
    Display --> Graphs
    Display --> Tables
    Display --> LaTeX
```

## Component Structure

### Interactive Explorer Framework

```mermaid
graph LR
    subgraph "Explorer Components"
        UI[UI Controls]
        State[State Manager]
        Handler[Event Handler]
        Renderer[Result Renderer]
    end
    
    subgraph "User Inputs"
        Formulas[Formula Input]
        Settings[Settings Panel]
        TheorySelect[Theory Selector]
    end
    
    subgraph "Processing"
        Validate[Input Validation]
        Build[Model Building]
        Format[Output Formatting]
    end
    
    Formulas --> UI
    Settings --> UI
    TheorySelect --> UI
    UI --> State
    State --> Handler
    Handler --> Validate
    Validate --> Build
    Build --> Format
    Format --> Renderer
    Renderer --> UI
```

## Interaction Flow

### Formula Checking Sequence

```mermaid
sequenceDiagram
    participant User
    participant Notebook
    participant API
    participant Adapter
    participant Builder
    participant Theory
    participant Display
    
    User->>Notebook: check("A → B", premises=["A"])
    Notebook->>API: Process request
    API->>Adapter: Get theory adapter
    Adapter->>Builder: Build with settings
    Builder->>Theory: Generate constraints
    Theory-->>Builder: Model or countermodel
    Builder-->>Adapter: Results
    Adapter-->>API: Formatted results
    API->>Display: Render output
    Display-->>Notebook: Display to user
    Notebook-->>User: Visual feedback
```

### Interactive Explorer Session

```mermaid
stateDiagram-v2
    [*] --> Initialize: Launch Explorer
    Initialize --> Ready: Load UI
    Ready --> InputFormula: Enter formula
    InputFormula --> SelectTheory: Choose theory
    SelectTheory --> ConfigureSettings: Adjust parameters
    ConfigureSettings --> Processing: Submit
    Processing --> DisplayResults: Model found
    Processing --> DisplayCountermodel: Invalid
    DisplayResults --> Ready: New query
    DisplayCountermodel --> Ready: Revise formula
    Ready --> [*]: Close session
```

## API Architecture

### High-Level Functions

```mermaid
graph TD
    subgraph "Public API"
        check[check()]
        explore[explore()]
        visualize[visualize()]
        load_examples[load_examples()]
    end
    
    subgraph "Core Functions"
        validate_formula[validate_formula()]
        build_model[build_model()]
        find_countermodel[find_countermodel()]
        format_output[format_output()]
    end
    
    subgraph "Helper Functions"
        parse_input[parse_input()]
        get_theory[get_theory()]
        apply_settings[apply_settings()]
        render_display[render_display()]
    end
    
    check --> validate_formula
    check --> build_model
    explore --> validate_formula
    explore --> find_countermodel
    visualize --> format_output
    load_examples --> get_theory
    
    validate_formula --> parse_input
    build_model --> apply_settings
    find_countermodel --> get_theory
    format_output --> render_display
```

## Theory Adapter Pattern

### Adapter Architecture

```mermaid
classDiagram
    class TheoryAdapter {
        <<interface>>
        +get_defaults()
        +validate_settings()
        +build_with_theory()
        +format_results()
    }
    
    class ClassicalAdapter {
        +get_defaults()
        +validate_settings()
        +build_with_theory()
        +format_results()
    }
    
    class ManyValuedAdapter {
        +get_defaults()
        +validate_settings()
        +build_with_theory()
        +format_results()
    }
    
    class ModalAdapter {
        +get_defaults()
        +validate_settings()
        +build_with_theory()
        +format_results()
    }
    
    TheoryAdapter <|-- ClassicalAdapter
    TheoryAdapter <|-- ManyValuedAdapter
    TheoryAdapter <|-- ModalAdapter
    
    class AdapterFactory {
        +get_adapter(theory_name)
        +list_available()
        +register_adapter()
    }
    
    AdapterFactory --> TheoryAdapter
```

## Widget Architecture

### Interactive UI Components

```mermaid
graph TB
    subgraph "Input Widgets"
        FormulaText[Formula Text Area]
        PremiseList[Premise List Editor]
        TheoryDropdown[Theory Dropdown]
        SettingsPanel[Settings Controls]
    end
    
    subgraph "Control Widgets"
        SubmitButton[Submit Button]
        ClearButton[Clear Button]
        SaveButton[Save Results]
        LoadButton[Load Example]
    end
    
    subgraph "Output Widgets"
        ResultDisplay[Result Display]
        ModelViewer[Model Viewer]
        CountermodelViewer[Countermodel Display]
        ProgressBar[Progress Indicator]
    end
    
    subgraph "State Management"
        SessionState[Session State]
        HistoryTracker[History Tracker]
        SettingsCache[Settings Cache]
    end
    
    FormulaText --> SessionState
    PremiseList --> SessionState
    TheoryDropdown --> SettingsCache
    SettingsPanel --> SettingsCache
    
    SubmitButton --> SessionState
    SessionState --> ResultDisplay
    SessionState --> ModelViewer
    SessionState --> CountermodelViewer
    
    ClearButton --> SessionState
    SaveButton --> HistoryTracker
    LoadButton --> FormulaText
```

## Visualization Pipeline

### Model Visualization Flow

```mermaid
graph LR
    subgraph "Model Data"
        States[State Graph]
        Relations[Relations]
        Valuations[Valuations]
    end
    
    subgraph "Graph Generation"
        NetworkX[NetworkX Graph]
        Layout[Layout Algorithm]
        Styling[Visual Styling]
    end
    
    subgraph "Rendering"
        Matplotlib[Matplotlib Figure]
        SVG[SVG Export]
        Interactive[Interactive View]
    end
    
    States --> NetworkX
    Relations --> NetworkX
    Valuations --> NetworkX
    NetworkX --> Layout
    Layout --> Styling
    Styling --> Matplotlib
    Matplotlib --> SVG
    Matplotlib --> Interactive
```

## Display Formatting

### Output Format Selection

```mermaid
flowchart TD
    Model[Model Result] --> FormatCheck{Format Type?}
    
    FormatCheck -->|Text| TextFormatter[Text Formatter]
    FormatCheck -->|LaTeX| LaTeXFormatter[LaTeX Formatter]
    FormatCheck -->|HTML| HTMLFormatter[HTML Formatter]
    FormatCheck -->|Graph| GraphFormatter[Graph Formatter]
    
    TextFormatter --> PlainText[Plain Text Output]
    LaTeXFormatter --> LaTeXDisplay[LaTeX Display]
    HTMLFormatter --> HTMLTable[HTML Tables]
    GraphFormatter --> NetworkDiagram[Network Diagram]
    
    PlainText --> JupyterCell[Jupyter Cell]
    LaTeXDisplay --> JupyterCell
    HTMLTable --> JupyterCell
    NetworkDiagram --> JupyterCell
```

## Session Management

### Explorer Session Lifecycle

```mermaid
stateDiagram-v2
    [*] --> Created: Initialize Explorer
    
    Created --> Configured: Load Settings
    Configured --> Active: Start Session
    
    Active --> Processing: Submit Query
    Processing --> Active: Display Results
    
    Active --> Saving: Save Session
    Saving --> Active: Continue
    
    Active --> Paused: Background Task
    Paused --> Active: Resume
    
    Active --> Cleanup: Close Explorer
    Cleanup --> [*]: Session Ended
    
    note right of Active
        Main interaction state
        - Accept inputs
        - Display results
        - Track history
    end note
    
    note right of Processing
        Model checking
        - Parse formulas
        - Build models
        - Find solutions
    end note
```

## Error Handling

### Error Flow Architecture

```mermaid
flowchart TB
    UserInput[User Input] --> Validation{Valid?}
    Validation -->|No| SyntaxError[Syntax Error]
    Validation -->|Yes| Processing[Process Formula]
    
    Processing --> BuildAttempt{Build Success?}
    BuildAttempt -->|No| SemanticError[Semantic Error]
    BuildAttempt -->|Yes| SolverCheck{Solver Success?}
    
    SolverCheck -->|No| TimeoutError[Timeout/Resource Error]
    SolverCheck -->|Yes| Results[Display Results]
    
    SyntaxError --> ErrorDisplay[Error Message]
    SemanticError --> ErrorDisplay
    TimeoutError --> ErrorDisplay
    
    ErrorDisplay --> Suggestions[Provide Suggestions]
    Suggestions --> UserInput
```

## Performance Optimization

### Caching Strategy

```mermaid
graph TD
    subgraph "Cache Layers"
        FormulaCache[Formula Parse Cache]
        ModelCache[Model Cache]
        DisplayCache[Display Cache]
    end
    
    subgraph "Cache Keys"
        FormulaKey[Formula + Theory]
        ModelKey[Constraints + Settings]
        DisplayKey[Model + Format]
    end
    
    subgraph "Cache Management"
        LRU[LRU Eviction]
        TTL[Time-based Expiry]
        Manual[Manual Clear]
    end
    
    FormulaKey --> FormulaCache
    ModelKey --> ModelCache
    DisplayKey --> DisplayCache
    
    FormulaCache --> LRU
    ModelCache --> TTL
    DisplayCache --> Manual
```

## Extension Points

### Plugin Architecture

```mermaid
graph TB
    subgraph "Core System"
        ExplorerCore[Explorer Core]
        PluginManager[Plugin Manager]
        ExtensionAPI[Extension API]
    end
    
    subgraph "Plugin Types"
        VisualizationPlugin[Visualization Plugins]
        TheoryPlugin[Theory Plugins]
        ExportPlugin[Export Plugins]
        ValidationPlugin[Validation Plugins]
    end
    
    subgraph "Plugin Lifecycle"
        Register[Register]
        Initialize[Initialize]
        Execute[Execute]
        Cleanup[Cleanup]
    end
    
    ExplorerCore --> PluginManager
    PluginManager --> ExtensionAPI
    
    VisualizationPlugin --> Register
    TheoryPlugin --> Register
    ExportPlugin --> Register
    ValidationPlugin --> Register
    
    Register --> Initialize
    Initialize --> Execute
    Execute --> Cleanup
```

## Integration Examples

### Notebook Workflow

```mermaid
sequenceDiagram
    participant Student
    participant Notebook
    participant Explorer
    participant ModelChecker
    participant Visualization
    
    Student->>Notebook: Import model_checker
    Notebook->>Explorer: Initialize explorer()
    Explorer-->>Student: Display UI
    
    loop Interactive Session
        Student->>Explorer: Enter formula
        Explorer->>ModelChecker: Check validity
        ModelChecker-->>Explorer: Return results
        Explorer->>Visualization: Generate display
        Visualization-->>Student: Show model/countermodel
        
        Student->>Explorer: Adjust settings
        Explorer->>ModelChecker: Rebuild with new settings
        ModelChecker-->>Explorer: Updated results
        Explorer-->>Student: Refreshed display
    end
    
    Student->>Explorer: Save session
    Explorer-->>Notebook: Export to .ipynb
```

## Best Practices

### Design Principles

1. **Immediate Feedback**: Provide instant validation and results
2. **Progressive Disclosure**: Show basic options first, advanced on demand
3. **Error Recovery**: Guide users to fix issues with helpful suggestions
4. **State Persistence**: Maintain session state across cell executions
5. **Theory Agnostic**: Adapt interface to theory capabilities

### Performance Guidelines

1. **Lazy Loading**: Load components only when needed
2. **Result Caching**: Cache expensive computations
3. **Incremental Updates**: Update only changed portions of display
4. **Resource Limits**: Set timeouts and memory limits for solver
5. **Background Processing**: Use async for long-running operations

## Technical Implementation

For detailed implementation information, see:
- [Jupyter Package Documentation](../../Code/src/model_checker/jupyter/README.md)
- [UI Components](../../Code/src/model_checker/jupyter/ui_components.py)
- [Theory Adapters](../../Code/src/model_checker/jupyter/adapters.py)

## See Also

- [Builder Architecture](BUILDER.md) - Core pipeline orchestration
- [Output Generation](OUTPUT.md) - Display formatting systems
- [Theory Framework](THEORY_LIB.md) - Theory implementation architecture

---

[← Back to Architecture](README.md) | [Theory Framework →](THEORY_LIB.md) | [Utils →](UTILS.md)