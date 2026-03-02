# Theory Analysis Prompt for Parallel Subagents

## Objective
Launch three parallel general-purpose subagents to analyze the theory modules in `code/src/model_checker/theory_lib/` (excluding `bimodal/`) and generate comprehensive refactoring reports without making any code changes.

## Theories to Analyze
1. **Exclusion Theory** - `code/src/model_checker/theory_lib/exclusion/`
2. **Imposition Theory** - `code/src/model_checker/theory_lib/imposition/`
3. **Logos Theory** - `code/src/model_checker/theory_lib/logos/`

## Prompt for Main Agent

```
I need to analyze three theory modules for potential refactoring improvements using parallel subagents.

Launch three general-purpose subagents SIMULTANEOUSLY to analyze:
1. code/src/model_checker/theory_lib/exclusion/
2. code/src/model_checker/theory_lib/imposition/
3. code/src/model_checker/theory_lib/logos/

IMPORTANT: DO NOT MAKE ANY CODE CHANGES. Only analyze and report.

Each subagent should autonomously perform the following analysis:

## 1. CODEBASE ANALYSIS
Read and analyze ALL Python files in the assigned theory directory:
- semantic.py - Core semantic implementations
- operators.py - Theory-specific operators
- iterate.py - Model iteration utilities
- examples.py - Example implementations
- __init__.py - Module initialization
- Any additional Python files

Also review:
- code/docs/core/CODE_STANDARDS.md
- code/docs/core/ARCHITECTURE.md
- code/docs/specific/ITERATOR.md
- code/docs/templates/theory_template.py

## 2. STRUCTURAL ANALYSIS
Evaluate against ModelChecker standards:

### Module Organization
- Are concerns properly separated into distinct modules?
- Is there an appropriate balance (not too few, not too many modules)?
- Does the structure follow code/docs/core/ARCHITECTURE.md patterns?
- Are there clear boundaries between semantic logic, operators, and iteration?

### Standardization Assessment
- How well does this theory conform to the standard theory structure?
- What deviations exist from the template in code/docs/templates/theory_template.py?
- Are naming conventions consistent with other theories?
- Does it follow the iterator contracts in code/docs/contracts/ITERATOR_CONTRACTS.md?

### Code Quality Review
- Type hints coverage and quality
- Error handling patterns (per code/docs/implementation/ERROR_HANDLING.md)
- Documentation completeness (per code/docs/core/DOCUMENTATION.md)
- Testing coverage and approach (per code/docs/core/TESTING.md)
- Performance considerations (per code/docs/implementation/PERFORMANCE.md)

## 3. IMPROVEMENT OPPORTUNITIES
Identify specific refactoring opportunities:

### Separation of Concerns
- Functions/classes that should be split
- Modules that could be consolidated
- Cross-cutting concerns that need extraction
- Circular dependencies to resolve

### Standardization Needs
- Deviations from standard theory structure
- Missing standard components
- Inconsistent interfaces or patterns
- Opportunities for shared base classes/protocols

### Code Improvements
- Type safety enhancements needed
- Performance optimizations available
- Error handling gaps
- Documentation deficiencies
- Test coverage gaps

## 4. REFACTORING RECOMMENDATIONS
Provide prioritized recommendations:

### High Priority (Breaking issues or critical gaps)
- List specific issues with file:line references
- Explain why these are critical
- Suggest specific solutions

### Medium Priority (Quality improvements)
- List improvement opportunities
- Explain benefits of changes
- Provide implementation suggestions

### Low Priority (Nice-to-have enhancements)
- List minor improvements
- Note quick wins
- Suggest future considerations

## 5. COMPATIBILITY ANALYSIS
Assess inter-theory consistency:
- Common patterns that should be extracted
- Interfaces that should be standardized
- Shared utilities that could be created
- Naming conventions to align

## 6. GENERATE DETAILED REPORT
Create a comprehensive markdown report with the following structure:

# [Theory Name] Theory Analysis Report

## Executive Summary
- Overall health score (1-10)
- Key strengths
- Critical issues
- Estimated refactoring effort

## Current Structure Analysis
### Module Organization
- Current file structure
- Module responsibilities
- Dependency graph

### Standards Compliance
- Adherence to CODE_STANDARDS.md: X/10
- Adherence to ARCHITECTURE.md: X/10
- Adherence to theory template: X/10

## Detailed Findings

### Separation of Concerns
[Specific findings with code references]

### Standardization Gaps
[Deviations from standard structure]

### Code Quality Issues
[Type hints, error handling, documentation gaps]

## Refactoring Recommendations

### Priority 1: Critical Issues
[Must-fix items]

### Priority 2: Quality Improvements
[Should-fix items]

### Priority 3: Enhancements
[Nice-to-have items]

## Implementation Plan
1. Phase 1: [Foundation fixes]
2. Phase 2: [Standardization]
3. Phase 3: [Optimization]

## Risk Assessment
- Backward compatibility concerns
- Testing requirements
- Migration complexity

## Metrics
- Current lines of code: X
- Current test coverage: X%
- Type hint coverage: X%
- Cyclomatic complexity: X
- Technical debt estimate: X hours

Return this report as a complete markdown document.

## FINAL INSTRUCTIONS
1. Run all three subagents IN PARALLEL (single message, multiple Task tool calls)
2. Each subagent saves its report to:
   - Exclusion: code/src/model_checker/theory_lib/specs/reports/exclusion_analysis.md
   - Imposition: code/src/model_checker/theory_lib/specs/reports/imposition_analysis.md
   - Logos: code/src/model_checker/theory_lib/specs/reports/logos_analysis.md
3. After all complete, create a summary report at:
   code/src/model_checker/theory_lib/specs/reports/summary_analysis.md

The summary should include:
- Comparative analysis across all theories
- Common refactoring patterns identified
- Recommended standardization approach
- Priority order for refactoring
- Estimated total effort

DO NOT make any changes to the actual theory code. Only analyze and report.
```

## Expected Outcomes

After running this prompt, you will have:

1. **Three detailed analysis reports** (one per theory) in `theory_lib/specs/reports/`
2. **A summary report** comparing all theories and providing overall recommendations
3. **Clear understanding** of what needs refactoring before any changes are made
4. **Prioritized action items** for the actual refactoring phase
5. **Risk assessment** for backward compatibility and testing needs

## Review Process

After the reports are generated:

1. Review each theory-specific report for accuracy
2. Validate the recommendations against project goals
3. Adjust priorities based on business needs
4. Approve specific refactoring items
5. Create refined prompts for actual refactoring based on approved items

## Notes

- Subagents work autonomously and in parallel
- No code changes are made during analysis
- Reports follow a standardized structure for easy comparison
- All recommendations reference the documentation standards in code/docs/
- Focus is on balance: improving quality while maintaining simplicity