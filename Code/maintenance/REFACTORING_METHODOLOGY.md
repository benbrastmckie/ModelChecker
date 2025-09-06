# Refactoring Methodology

[← Code Standards](CODE_STANDARDS.md) | [Back to Maintenance](README.md) | [Method Complexity →](METHOD_COMPLEXITY.md)

## Overview

This document outlines a **systematic but flexible approach** to refactoring ModelChecker components, based on successful patterns from the builder/ package improvements. The methodology emphasizes **gradual improvement** over disruptive changes, maintaining working code while enhancing quality.

**Core Philosophy:** Refactoring should **improve code quality without breaking compatibility or introducing unnecessary complexity**. These are guidelines to aim for, not rigid rules to enforce.

## The 4-Phase Approach

Based on the successful builder/ refactor that improved compliance from 72% to 90%, this methodology provides a proven framework for systematic improvement.

### Phase 1: Foundation Cleanup
**Goal:** Establish consistent foundations without changing functionality  
**Duration:** Usually 1-2 hours  
**Impact:** Low risk, high consistency gain

#### Import Organization
Gently standardize import patterns for better maintainability:

```python
# Ideal import structure (aim for this in new/modified files)
# Standard library imports
import os
from typing import Dict, List, Optional

# Third-party imports  
import z3

# Local imports - prefer relative for portability where practical
from ..base import BaseStructure
from .utils import helper_function
```

**Guidelines:**
- **New files:** Follow the standard import organization
- **Existing files:** Standardize imports when making other changes
- **Don't refactor:** Files just for import organization unless they're already being modified

#### Code Style Consistency
Apply gentle consistency improvements:
- Remove unused imports when touching files
- Standardize variable naming in modified sections
- Ensure UTF-8 encoding for new files
- Fix obvious style inconsistencies when convenient

### Phase 2: Method Refinement  
**Goal:** Improve method organization and readability
**Duration:** 2-4 hours depending on complexity
**Impact:** Medium risk, significant readability gain

#### Method Length Guidelines
**Soft targets to aim for:**
- **Utility functions:** 20-40 lines (ideal for simple operations)
- **Business logic methods:** 40-75 lines (acceptable for domain complexity) 
- **Complex domain methods:** 75+ lines (may be appropriate for algorithms, parsing, etc.)

**When to consider extraction:**
- Method has multiple distinct responsibilities
- Repeated code patterns that could be shared
- Method is difficult to test due to complexity
- Method has deep nesting (>3-4 levels)

**Builder/ Example:**
```python
# Before: 187-line process_example method
def process_example(self, example_name, example_data, theory_name):
    # ... complex logic mixing validation, processing, output ...

# After: Extracted focused helper methods
def process_example(self, example_name, example_data, theory_name):
    """Main coordination method - focused and readable."""
    self._validate_example_inputs(example_name, example_data)
    context = self._initialize_processing_context(theory_name)
    result = self._execute_model_check(example_data, context)
    self._handle_result_output(result, example_name, theory_name)
    return result

def _validate_example_inputs(self, example_name, example_data):
    """Focused validation logic."""
    # Specific validation logic only
```

**Extraction Principles:**
- **Extract when it improves clarity**, not just to meet line counts
- **Preserve working logic** - only extract cohesive units
- **Consider testing** - extracted methods should be testable if they contain significant logic

### Phase 3: Error Handling Standardization
**Goal:** Consistent, helpful error handling across components
**Duration:** 1-3 hours
**Impact:** Low risk, improved user experience

#### Error Hierarchy Extension
Build on the proven BuilderError pattern for new packages:

```python
# Follow the successful BuilderError model
class PackageNameError(Exception):
    """Base exception for package-specific errors."""
    pass

class ValidationError(PackageNameError):
    """Raised when validation fails with helpful context."""
    
    def __init__(self, message: str, context: dict = None, suggestion: str = None):
        """Include helpful context and recovery suggestions."""
        formatted_message = message
        if context:
            formatted_message += f"\nContext: {context}"
        if suggestion:
            formatted_message += f"\nSuggestion: {suggestion}"
        super().__init__(formatted_message)
```

#### Error Message Guidelines
**Aim for helpful, actionable messages:**

```python
# Good: Specific and actionable
raise ValidationError(
    f"Formula '{formula}' uses Unicode symbols. "
    f"Use LaTeX notation instead: \\wedge for ∧, \\vee for ∨",
    context={"formula": formula, "position": position},
    suggestion="Try: '(A \\wedge B)' instead of '(A ∧ B)'"
)

# Avoid: Generic and unhelpful
raise ValueError("Invalid formula")
```

### Phase 4: Architectural Improvements
**Goal:** Enhance component interaction and maintainability  
**Duration:** 2-4 hours
**Impact:** Medium risk, long-term maintainability gain

#### Protocol-Based Interfaces
Extend the successful protocol pattern for better testability:

```python
# Build on existing protocol patterns
from typing import Protocol

class IComponentInterface(Protocol):
    """Clear interface for component functionality."""
    
    def process_data(self, data: Any) -> ProcessResult:
        """Process data with clear contract."""
        ...
    
    def validate_input(self, input_data: Any) -> bool:
        """Validate input with clear expectations."""
        ...
```

#### Dependency Injection
Improve testability without major architectural changes:

```python
# Gradual improvement - make dependencies explicit
class ComponentClass:
    def __init__(self, validator: IValidator = None, 
                 processor: IProcessor = None):
        self.validator = validator or DefaultValidator()
        self.processor = processor or DefaultProcessor()
```

## Application Guidelines

### When to Apply This Methodology

**Good candidates for refactoring:**
- Components with known quality issues
- Code that's difficult to test or extend
- Modules that frequently need changes
- Code that's causing maintenance burden

**Avoid refactoring when:**
- Code is working well and rarely changed
- Recent significant changes are still stabilizing  
- Time constraints would force rushed changes
- Risk outweighs the benefit

### Progressive Improvement Strategy

**Preferred approach:**
1. **Opportunistic improvement** - improve code when making other changes
2. **Module-by-module** - focus on one component at a time
3. **Test-driven refinement** - ensure improvements don't break functionality
4. **Incremental progress** - small, safe improvements over time

### Quality Metrics and Assessment

**Track improvement without rigid enforcement:**

```python
# Example quality indicators to monitor:
# - Average method length (aim for reasonable, not minimal)
# - Test coverage (improve when practical) 
# - Import consistency (standardize gradually)
# - Error handling clarity (enhance when touching code)
```

**Success indicators:**
- Code is easier to understand and modify
- Testing becomes more straightforward
- New contributors can orient themselves faster
- Bug fixes and enhancements require less investigation

## Integration with Existing Standards

This methodology works with existing maintenance standards:

- **[CODE_STANDARDS.md](CODE_STANDARDS.md)** - Provides the style and quality targets
- **[TESTING_STANDARDS.md](TESTING_STANDARDS.md)** - Ensures refactoring doesn't break tests
- **[ERROR_HANDLING.md](ERROR_HANDLING.md)** - Defines the error patterns to apply
- **[METHOD_COMPLEXITY.md](METHOD_COMPLEXITY.md)** - Provides complexity assessment guidelines

## Success Examples

The builder/ package refactor demonstrates this methodology's effectiveness:

**Results achieved:**
- **Compliance improvement:** 72% → 90%
- **Method organization:** 187-line methods → focused, readable functions
- **Error handling:** Consistent, helpful error messages
- **Testing:** 218/218 tests passing throughout the process
- **Architecture:** Clean protocol-based interfaces

**Key lessons:**
- **Gradual improvement** works better than wholesale rewrites
- **Preserve working functionality** while enhancing quality
- **Test-driven changes** prevent regression
- **Focus on pain points** rather than arbitrary metrics

## Conclusion

This methodology provides a **proven framework for gradual quality improvement** without the risks of major rewrites. Apply these principles **judiciously and progressively**, always prioritizing working software over perfect code.

The goal is **sustainable improvement** that makes the codebase more maintainable and enjoyable to work with, not compliance with arbitrary rules.

---

[← Code Standards](CODE_STANDARDS.md) | [Back to Maintenance](README.md) | [Method Complexity →](METHOD_COMPLEXITY.md)