# Style Guide

## Code Style

### Formatting
- **Imports**: Standard libraries first, then local imports
- **Spacing**: 4-space indentation
- **Naming**: 
  - Functions: `snake_case`
  - Classes: `PascalCase`
  - Modules: `lowercase`

### Documentation
- **Error handling**: Use descriptive exception messages
- **Documentation**: Triple-quoted docstrings for modules and functions

### Architecture
- **Maintain separation between semantic and syntactic components**
- **Each theory in `theory_lib/` follows same structure** (operators.py, semantic.py, examples.py)
- **New theories should match existing module patterns**

## Design Philosophy

### Core Principles
- **Fail Fast**: Let errors occur naturally with standard Python tracebacks rather than adding complex conditional logic to handle edge cases.
- **Deterministic Behavior**: Avoid default values, fallbacks, or implicit conversions that can mask errors or introduce non-deterministic behavior.
- **Required Parameters**: Parameters should be explicitly required with no implicit conversion between different types of values (e.g., world arrays vs. world IDs).
- **Clear Data Flow**: Keep a clear and consistent approach to passing data between components, making sure all required values are explicitly passed.
- **No Silent Failures**: Don't catch exceptions or provide defaults just to avoid errors. If a value is missing or of the wrong type, let the error happen clearly.

### Domain-Specific Guidelines
- **Explicit World References**: In bimodal logic, always use consistent world references. World IDs should be explicitly provided where needed rather than attempting conversions.
- **Direct Function Calls Over Decorators**: Favor direct function calls over decorators to maintain clear execution paths and explicit data flow. Decorators can obscure the execution flow and make debugging more complex. When functionality needs to be applied to multiple functions, prefer composition through utility functions that are explicitly called rather than decorators that wrap function behavior implicitly.

### Change Management
- **Prioritize Code Quality Over Backward Compatibility**: Backward compatibility is explicitly NOT a priority in this project. When improving the codebase, you should freely make breaking changes if they result in cleaner, more maintainable, or more flexible code. It's not just acceptable but encouraged to refactor and redesign interfaces when needed, even if this breaks existing code. Continuous improvement of the codebase takes precedence over preserving compatibility with older code patterns. However, when making breaking changes, take care to provide a unified and systematic approach that ensures consistency throughout the codebase. Design comprehensive solutions that address the entire system rather than localized fixes, and update all affected components to follow the new patterns. This creates a more coherent overall architecture even when making significant changes.

## Debugging Philosophy

### Problem-Solving Approach
- **Root Cause Analysis**: Always trace errors to their source rather than addressing symptoms. Fix the underlying issue instead of adding patches.
- **Error as Feedback**: View errors as valuable signals pointing to areas that need improvement in the codebase.
- **Structural Solutions**: When fixing bugs, consider if the issue reveals a deeper architectural problem that should be addressed.
- **Refactor Over Workaround**: Choose to refactor problematic code rather than adding conditional logic to work around issues.

### Testing and Documentation
- **Test-Driven Resolution**: Create regression tests that reproduce bugs before fixing them to ensure they don't return.
- **Documentation of Learnings**: Document significant bugs and their solutions to build institutional knowledge.
- **Error Messages as Documentation**: Write clear, specific error messages that help future developers understand requirements.

### Code Quality Standards
- **Simplification**: If a component generates frequent errors, consider simplifying its interface or responsibilities.
- **No Defensive Programming**: Avoid adding excessive validation or error handling that obscures the natural flow of the code.
- **Eliminate Error Classes**: Reduce similar errors by identifying patterns and making structural improvements.