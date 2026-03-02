# Subagent Refactoring Guide for Theory Libraries

## Overview

This guide demonstrates how to use Claude Code's subagent capabilities to refactor multiple theory modules in parallel. We'll orchestrate multiple specialized agents to refactor the theories in `code/src/model_checker/theory_lib/`, excluding the `bimodal/` directory which is under construction.

## Target Theories for Refactoring

Based on the current codebase structure, we have three main theories to refactor:

1. **Exclusion Theory** (`theory_lib/exclusion/`)
   - Implements witness negation semantics
   - Contains: `semantic.py`, `operators.py`, `iterate.py`, `examples.py`

2. **Imposition Theory** (`theory_lib/imposition/`)
   - Implements imposition-based semantics
   - Contains: `semantic.py`, `operators.py`, `iterate.py`, `examples.py`

3. **Logos Theory** (`theory_lib/logos/`)
   - Implements logos-based semantics
   - Contains: `semantic.py`, `operators.py`, `iterate.py`, `examples.py`

## Subagent Architecture

### Main Agent Orchestrator

The main agent acts as the conductor, responsible for:
- Dispatching refactoring tasks to specialized subagents
- Running all subagents in parallel for maximum efficiency
- Collecting and consolidating results
- Creating a final report

### Specialized Subagents

Each subagent focuses on a specific theory module and performs:
- Code analysis and understanding
- Refactoring operations
- Testing and validation
- Progress reporting

## Implementation Strategy

### Step 1: Generic Refactoring Instructions

Create a template instruction set that each subagent will follow:

```markdown
## Refactoring Instructions for Theory Module

1. **Analysis Phase**
   - Analyze the current code structure
   - Identify code smells and improvement opportunities
   - Document dependencies and interfaces

2. **Refactoring Operations**
   - Improve type hints and annotations
   - Extract common patterns into utilities
   - Optimize performance bottlenecks
   - Enhance error handling
   - Improve documentation and docstrings
   - Ensure consistent naming conventions

3. **Validation Phase**
   - Run existing tests
   - Ensure backward compatibility
   - Verify no functionality is broken

4. **Reporting**
   - Document all changes made
   - Note any issues encountered
   - Provide recommendations for future improvements
```

### Step 2: Parallel Subagent Dispatch

The main agent launches all subagents simultaneously using parallel tool calls:

```python
# Conceptual example - actual implementation uses Task tool
subagents = [
    {
        "type": "general-purpose",
        "theory": "exclusion",
        "path": "code/src/model_checker/theory_lib/exclusion/"
    },
    {
        "type": "general-purpose",
        "theory": "imposition",
        "path": "code/src/model_checker/theory_lib/imposition/"
    },
    {
        "type": "general-purpose",
        "theory": "logos",
        "path": "code/src/model_checker/theory_lib/logos/"
    }
]
```

### Step 3: Subagent Task Prompts

Each subagent receives a detailed, autonomous task description:

#### Example Prompt Template:

```
You are refactoring the [THEORY_NAME] theory module located at [PATH].

Your task is to autonomously refactor this theory module following these guidelines:

1. First, read and analyze all Python files in the module:
   - semantic.py - Core semantic implementations
   - operators.py - Theory-specific operators
   - iterate.py - Model iteration utilities
   - examples.py - Example implementations
   - __init__.py - Module initialization

2. Perform the following refactoring operations:
   a) Type Safety Improvements:
      - Add comprehensive type hints to all functions
      - Use Protocol classes where appropriate
      - Add TypeVar for generic types

   b) Code Organization:
      - Extract repeated patterns into helper functions
      - Create base classes for common functionality
      - Improve module cohesion

   c) Performance Optimization:
      - Cache expensive computations
      - Optimize loops and iterations
      - Remove redundant operations

   d) Error Handling:
      - Add proper exception handling
      - Improve error messages
      - Add validation for inputs

   e) Documentation:
      - Add/update docstrings for all public functions
      - Include examples in docstrings
      - Document complex algorithms

3. Testing and Validation:
   - Run any existing tests in the tests/ subdirectory
   - Ensure all refactoring maintains backward compatibility
   - Do not break any existing functionality

4. Create a detailed report including:
   - Summary of changes made
   - Files modified
   - Any issues encountered
   - Recommendations for future improvements
   - Performance impact assessment

Return a structured JSON report with your findings and changes.
```

### Step 4: Result Consolidation

The main agent collects results from all subagents and creates a comprehensive report:

```markdown
# Refactoring Results Report

## Executive Summary
- Total theories refactored: 3
- Total files modified: X
- Success rate: 100%

## Theory-Specific Results

### Exclusion Theory
[Subagent 1 results]

### Imposition Theory
[Subagent 2 results]

### Logos Theory
[Subagent 3 results]

## Common Patterns Identified
[Cross-theory insights]

## Recommendations
[Future improvement suggestions]
```

## Practical Example Code

Here's how you would execute this refactoring using Claude Code:

### Main Orchestrator Prompt:

```
I want to refactor all theory modules in theory_lib/ (excluding bimodal/).
Launch parallel subagents for each theory (exclusion, imposition, logos).

Each subagent should:
1. Analyze the theory's code structure
2. Perform comprehensive refactoring (type hints, performance, documentation)
3. Test the changes
4. Report results

Run all subagents in parallel and compile a final report when complete.
```

### Claude Code Response Pattern:

The assistant will:
1. Use the Task tool with multiple parallel invocations
2. Each Task call will specify `subagent_type: "general-purpose"`
3. Wait for all subagents to complete
4. Consolidate and present the results

## Benefits of This Approach

1. **Parallelization**: All theories are refactored simultaneously, reducing total time
2. **Consistency**: Each subagent follows the same refactoring guidelines
3. **Autonomy**: Subagents work independently without blocking each other
4. **Scalability**: Easy to add more theories or modify refactoring rules
5. **Comprehensive**: Each theory gets dedicated attention and analysis

## Advanced Techniques

### Custom Refactoring Rules

You can provide theory-specific refactoring rules:

```python
refactoring_rules = {
    "exclusion": {
        "focus": "witness function optimization",
        "priority": "performance"
    },
    "imposition": {
        "focus": "constraint handling",
        "priority": "type safety"
    },
    "logos": {
        "focus": "semantic clarity",
        "priority": "documentation"
    }
}
```

### Progressive Enhancement

Start with basic refactoring, then layer on more complex transformations:

1. **Phase 1**: Type hints and documentation
2. **Phase 2**: Performance optimization
3. **Phase 3**: Architectural improvements

### Monitoring and Feedback

The main agent can:
- Track progress of each subagent
- Handle failures gracefully
- Retry failed operations
- Provide real-time updates

## Common Pitfalls to Avoid

1. **Over-refactoring**: Don't change working code unnecessarily
2. **Breaking Changes**: Always maintain backward compatibility
3. **Test Coverage**: Ensure tests still pass after refactoring
4. **Documentation Sync**: Update docs to reflect changes
5. **Performance Regression**: Profile before and after changes

## Conclusion

Using subagents for parallel refactoring provides a powerful way to improve code quality across multiple modules simultaneously. This approach leverages Claude Code's ability to orchestrate multiple specialized agents, each focused on a specific task while the main agent coordinates and consolidates the results.

The key to success is:
- Clear, detailed instructions for each subagent
- Proper parallelization using the Task tool
- Comprehensive result consolidation
- Iterative refinement based on results

This pattern can be adapted for various large-scale code transformation tasks beyond refactoring, such as:
- Migration to new frameworks
- Adding comprehensive testing
- Security audits
- Performance optimization
- Documentation generation