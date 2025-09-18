# Documentation Standards

[← Code Standards](CODE_STANDARDS.md) | [Back to Maintenance](../README.md) | [Testing Standards →](TESTING.md)

## Table of Contents

1. [Overview](#overview)
2. [Documentation Philosophy](#documentation-philosophy)
3. [README Structure and Requirements](#readme-structure-and-requirements)
4. [Google-Style Docstring Standards](#google-style-docstring-standards)
5. [Comment Standards](#comment-standards)
6. [API Documentation Requirements](#api-documentation-requirements)
7. [Documentation Hierarchy](#documentation-hierarchy)
8. [Cross-Reference Management](#cross-reference-management)
9. [Mathematical Notation Standards](#mathematical-notation-standards)
10. [Templates and Examples](#templates-and-examples)
11. [Quality Metrics and Maintenance](#quality-metrics-and-maintenance)
12. [User vs Developer Documentation](#user-vs-developer-documentation)
13. [Changelog and Version Control](#changelog-and-version-control)
14. [Success Metrics](#success-metrics)

## Overview

This document establishes comprehensive documentation standards for the ModelChecker framework. These standards ensure consistency, maintainability, and usefulness across all documentation types, from code comments to user guides.

**Core Principle**: Documentation serves users first. Every piece of documentation should answer real questions that real users have when working with the code.

## Documentation Philosophy

### 1. User-Centric Design

Documentation must solve real problems for real users:

```markdown
# GOOD - Addresses user need
## Handling Z3 Timeout Errors

When model checking takes too long, you'll see:
```
TimeoutError: Z3 solver exceeded 10 seconds
```

Fix by increasing timeout in settings:
```python
settings = {'max_time': 30}  # 30 seconds
```

# BAD - Technical jargon without context
## Error Handling

The framework raises TimeoutError when Z3.check() returns 'unknown'.
```

### 2. No Backwards Compatibility

Documentation follows the same principle as code - never maintain backwards compatibility:

- **Update all references** when interfaces change
- **Remove deprecated information immediately**
- **No "legacy" or "old way" sections**
- **Keep documentation current with implementation**

### 3. Fail-Fast Documentation

Documentation should be explicit and prevent user confusion:

```python
# GOOD - Clear about required parameters
def check_validity(premises: List[str], conclusions: List[str], settings: Dict[str, Any]) -> Result:
    """
    Check logical validity of an argument.
    
    Args:
        premises: List of premise formulas in LaTeX notation
        conclusions: List of conclusion formulas in LaTeX notation  
        settings: Required settings dict with 'N' (int) and 'max_time' (int)
    """

# BAD - Hidden defaults mask requirements
def check_validity(premises, conclusions, settings=None):
    """Check validity with optional settings."""
```

## README Structure and Requirements

### Core Requirements

**Every directory MUST have a README.md** that serves as the entry point for understanding that component.

### Standard Structure

```markdown
# Component Name: Descriptive Purpose

[← Navigation](../README.md) | [Key Doc →](docs/KEY.md) | [Related →](../related/)

## Directory Structure

```
component/
├── README.md                   # This file - comprehensive overview
├── __init__.py                 # Public API exports
├── core.py                     # Main implementation
├── docs/                       # Component documentation
│   ├── README.md               # Documentation hub
│   ├── API_REFERENCE.md        # Complete API documentation
│   └── USER_GUIDE.md           # Usage guide with examples
└── tests/                      # Test suite with documentation
    ├── README.md               # Test overview and running instructions
    ├── unit/                   # Unit tests
    └── integration/            # Integration tests
```

## Overview

[2-3 paragraphs explaining:
- What this component does
- Why it's important to the framework
- How it fits with other components
- Key capabilities and limitations]

## Usage Examples

### Basic Usage

```python
from model_checker.component import Component

# Show complete, working example
component = Component(settings)
result = component.process(data)
print(result)  # Expected output format
```

### Advanced Usage

[More complex examples as needed]

## Key Features

- **Feature 1**: Detailed description with benefits
- **Feature 2**: Detailed description with use cases
- **Feature 3**: Detailed description with limitations

## Documentation

### For Users
- **[User Guide](docs/USER_GUIDE.md)** - Practical usage guide
- **[Examples](examples.py)** - Working code examples

### For Developers
- **[API Reference](docs/API_REFERENCE.md)** - Complete technical documentation
- **[Architecture](docs/ARCHITECTURE.md)** - Design decisions and patterns

## References

### Academic Sources
- Author (Year) ["Paper Title"](link), Journal

### Framework References  
- **[Related Component](../related/)** - How components interact
- **[Main Documentation](../../README.md)** - Framework overview

---

[← Navigation](../README.md) | [Key Doc →](docs/KEY.md) | [Related →](../related/)
```

### Theory-Specific README Requirements

Theory READMEs must include:

```markdown
## Theoretical Foundation

Brief explanation of the logical theory this implements, including:
- Academic background and key papers
- Core semantic concepts
- Distinguishing features from other theories

## Operator Inventory

Complete list of available operators:

| Operator | LaTeX | Unicode | Arity | Description |
|----------|-------|---------|-------|-------------|
| Negation | `\\neg` | ¬ | 1 | Logical negation |
| Conjunction | `\\wedge` | ∧ | 2 | Logical and |

## Settings and Configuration

Theory-specific settings with defaults:
```python
DEFAULT_SETTINGS = {
    'N': 3,              # Number of atomic propositions
    'max_time': 10,      # Z3 timeout in seconds
    'theory_specific': True,  # Theory-specific option
}
```

## Example Library

Overview of example categories:
- **Basic Examples**: Simple, illustrative cases
- **Advanced Examples**: Complex logical arguments
- **Edge Cases**: Boundary conditions and special cases
```

### Test Directory README Requirements

```markdown
# Component Tests: Test Suite Overview

[← Back to Component](../README.md) | [Integration Tests →](integration/) | [Unit Tests →](unit/)

## Test Organization

This test suite covers [component] with [X] total tests across [Y] categories.

## Directory Structure

```
tests/
├── README.md                   # This file - test overview
├── integration/                # Integration tests ([N] tests)
│   ├── README.md               # Integration test documentation
│   └── test_*.py               # Integration test files
└── unit/                       # Unit tests ([M] tests)
    ├── README.md               # Unit test documentation
    └── test_*.py               # Unit test files
```

## Running Tests

```bash
# All tests for this component
./run_tests.py component_name

# Unit tests only
./run_tests.py component_name --unit

# Integration tests only  
./run_tests.py component_name --integration
```

## Test Coverage

### What We Test
- ✅ Core functionality with valid inputs
- ✅ Error handling with invalid inputs
- ✅ Edge cases and boundary conditions
- ✅ Integration with other components

### Test Categories
- **Functionality Tests**: Core feature verification
- **Error Tests**: Exception handling verification
- **Performance Tests**: Timeout and efficiency verification
- **Integration Tests**: Component interaction verification

## Adding Tests

When adding new tests:
1. Follow naming convention: `test_feature_condition()`
2. Include descriptive docstrings
3. Update test counts in this README
4. Document new test categories if needed

See [Testing Standards](../../maintenance/TESTING_STANDARDS.md) for complete guidelines.
```

## Google-Style Docstring Standards

### Module Docstrings

```python
"""
Brief one-line summary of module purpose.

Detailed description of what this module implements, including:
- Core functionality and responsibilities
- Integration with other components
- Usage patterns and best practices

Example:
    Basic usage example::
    
        >>> from model_checker.module import function
        >>> result = function(arg)
        >>> print(result)
        Expected output
"""
```

### Class Docstrings

```python
class ExampleClass:
    """
    Brief one-line summary of class purpose.
    
    Detailed description of the class behavior, responsibilities,
    and design patterns used.
    
    This class implements [specific pattern/algorithm] for [purpose].
    It integrates with [other components] by [mechanism].
    
    Attributes:
        attribute1: Description of attribute1 including type and purpose
        attribute2: Description of attribute2 including constraints
        _private_attr: Description of private attributes (if essential to understanding)
    
    Example:
        Basic usage pattern::
        
            >>> obj = ExampleClass(param1, param2)
            >>> result = obj.method(data)
            >>> print(result.status)
            'success'
            
        Advanced usage::
        
            >>> obj = ExampleClass(param1, param2, advanced_option=True)
            >>> for item in obj.iterate_results():
            ...     print(item)
    """
```

### Function/Method Docstrings

```python
def complex_function(
    param1: str,
    param2: Optional[int] = None,
    settings: Dict[str, Any] = None
) -> Tuple[bool, Optional[str]]:
    """
    Brief one-line summary of function purpose.
    
    Detailed description if needed, including algorithmic notes,
    performance considerations, or usage patterns.
    
    This function implements [algorithm/pattern] to [achieve goal].
    It handles [edge cases] by [mechanism].
    
    Args:
        param1: Description of first parameter, including format requirements
            or constraints. For example: "LaTeX formula like '\\Box A'"
        param2: Description of optional parameter with default behavior.
            If None, [default behavior description].
        settings: Configuration dictionary with required keys:
            - 'N' (int): Number of atomic propositions (1-10)
            - 'max_time' (int): Timeout in seconds (default: 10)
            - 'verbose' (bool): Enable detailed output (default: False)
            
    Returns:
        Tuple containing:
        - bool: Success status of the operation
        - Optional[str]: Error message if failed, None if successful
        
    Raises:
        ValueError: When param1 is empty or contains invalid characters
        TimeoutError: When Z3 solver exceeds max_time limit
        ModelCheckerError: When theory loading fails or invalid settings
        
    Example:
        Basic usage::
        
            >>> result, error = complex_function("\\Box A", 5)
            >>> if result:
            ...     print("Success!")
            >>> else:
            ...     print(f"Error: {error}")
            
        With custom settings::
        
            >>> settings = {'N': 4, 'max_time': 20, 'verbose': True}
            >>> result, error = complex_function("\\Box A", 5, settings)
            
    Note:
        This function modifies Z3 context state. Use separate instances
        for concurrent operations.
    """
```

### Method and Special Method Docstrings

```python
class ModelStructure:
    def is_satisfiable(self) -> bool:
        """
        Check whether the current model satisfies all constraints.
        
        Computed by checking Z3 solver state. Returns False if
        solver returned 'unsat' or 'unknown'.
        
        Returns:
            bool: True if model satisfies all constraints, False otherwise
        
        Example:
            >>> model = ModelStructure(constraints)
            >>> if model.is_satisfiable():
            ...     print("Model found!")
        """
        
    def __str__(self) -> str:
        """
        Return human-readable string representation.
        
        Format: "ModelStructure(N=3, worlds=8, constraints=15)"
        
        Returns:
            Formatted string with key model statistics
        """
```

## Comment Standards

### When to Comment

Use comments sparingly - code should be self-documenting. Comment only when:

1. **Explaining WHY, not WHAT**:
```python
# GOOD - Explains reasoning
# Reset Z3 context to prevent state leakage between examples
ctx = z3.Context()

# BAD - States the obvious
# Create new context
ctx = z3.Context()
```

2. **Complex algorithms or mathematical concepts**:
```python
# Calculate bit vector size based on number of atomic propositions
# This ensures sufficient bits for all possible truth value combinations
# Formula: 2^N where N is number of atoms
bit_size = 2 ** self.N
```

3. **Non-obvious workarounds or optimizations**:
```python
# Z3 requires separate variables for each world to avoid constraint conflicts
# We can't reuse proposition variables across possible worlds
world_vars = [z3.Bool(f"{prop}_w{world}") for world in range(self.worlds)]
```

4. **Academic or theoretical context**:
```python
# Implements Kit Fine's truthmaker semantics (Fine 2017)
# where truth conditions are defined by exact verification
def verify_formula(self, formula: str, state: BitVector) -> bool:
```

### Comment Format Standards

```python
# Use complete sentences with proper capitalization and punctuation.
# Keep comments up to date with code changes.

# For multi-line explanations, use multiple single-line comments
# rather than block comments. This maintains consistency and
# makes it easier to edit individual lines.

def complex_function():
    # TODO: Optimize this algorithm for large N values
    # FIXME: Handle edge case when N=0  
    # NOTE: This implementation follows Smith et al. (2020) algorithm
    pass
```

### What NOT to Comment

```python
# DON'T comment obvious code
x = x + 1  # Increment x

# DON'T comment every line
name = get_name()      # Get the name
age = get_age()        # Get the age
email = get_email()    # Get the email

# DON'T leave commented-out code
# old_function()  # Remove this - don't commit commented code
new_function()

# DON'T use block comments for temporary notes
"""
This is a temporary note about implementation...
Remove before committing!
"""
```

## API Documentation Requirements

### Complete API Reference Structure

Every component with a public API must have `docs/API_REFERENCE.md`:

```markdown
# Component API Reference

[← Back to Documentation](README.md) | [User Guide →](USER_GUIDE.md)

## Table of Contents

1. [Overview](#overview)
2. [Core Functions](#core-functions)
3. [Classes](#classes)
4. [Constants and Types](#constants-and-types)
5. [Error Handling](#error-handling)
6. [Examples](#examples)
7. [See Also](#see-also)

## Overview

Brief description of the API's purpose and scope.

## Core Functions

### `function_name(param1, param2=None)`

Complete function documentation with parameters, returns, raises, and examples.

[Continue for all public functions]

## Classes

### `ClassName`

Complete class documentation including all public methods and properties.

#### `method_name(param)`

Complete method documentation.

## Examples

### Basic Usage Example

```python
# Complete, working example with expected output
```

### Advanced Usage Example

```python
# More complex example showing integration
```

## Error Handling

### Common Exceptions

- `ExceptionType`: When it's raised and how to handle it

### Error Examples

```python
# Example showing error condition and proper handling
```
```

### API Documentation Guidelines

1. **Complete Coverage**: Document all public interfaces
2. **Working Examples**: All examples must be tested and functional
3. **Type Information**: Include all type annotations and constraints
4. **Error Scenarios**: Document all possible exceptions
5. **Integration Context**: Show how API fits with other components

## Documentation Hierarchy

### Three-Tier Structure

The ModelChecker documentation follows a three-tier hierarchy:

```
Documentation Hierarchy:
├── README.md (Entry Point)
│   ├── Quick overview and navigation
│   └── Links to specialized docs
├── User Documentation (docs/)
│   ├── USER_GUIDE.md - Practical usage
│   ├── EXAMPLES.md - Working examples
│   └── SETTINGS.md - Configuration
└── Developer Documentation (docs/)
    ├── API_REFERENCE.md - Complete API
    ├── ARCHITECTURE.md - Design decisions
    └── CONTRIBUTING.md - Development guide
```

### Documentation Types by Audience

| Document Type | Primary Audience | Content Focus |
|---------------|------------------|---------------|
| README.md | All users | Overview, quick start, navigation |
| USER_GUIDE.md | End users | Practical usage, workflows |
| API_REFERENCE.md | Developers | Complete technical reference |
| ARCHITECTURE.md | Maintainers | Design decisions, patterns |
| EXAMPLES.md | All users | Working code examples |

### Specialization Rules

1. **README.md**: Broad overview that guides users to specialized docs
2. **USER_GUIDE.md**: Task-oriented documentation for accomplishing goals
3. **API_REFERENCE.md**: Complete technical reference for all public interfaces
4. **ARCHITECTURE.md**: Design rationale and internal structure
5. **CONTRIBUTING.md**: Development workflow and standards

## Cross-Reference Management

### Link Standards

```markdown
# Relative links to maintain portability
[Related Doc](../component/docs/GUIDE.md)
[Same Directory](GUIDE.md)
[Parent Directory](../README.md)

# Absolute links only for external resources
[Z3 Documentation](https://z3prover.github.io/api/html/namespacez3py.html)
[Academic Paper](https://doi.org/10.1000/journal.2020.123)
```

### Navigation Patterns

```markdown
# Header navigation (top of every non-README doc)
[← Back to Parent](../README.md) | [Key Resource →](KEY_DOC.md) | [Related →](related/)

# Footer navigation (bottom of every doc)
---

[← Back to Parent](../README.md) | [Next Topic →](NEXT.md)
```

### Cross-Reference Maintenance

1. **Link Validation**: Check all internal links during major refactors
2. **Consistent Naming**: Use consistent link text for the same destination
3. **Bidirectional Links**: Ensure related documents link to each other
4. **Update Dependencies**: Update all references when moving or renaming files

### Reference Management Rules

```markdown
# GOOD - Specific, descriptive link text
See [Theory Comparison Guide](../theory/COMPARISON.md) for differences between theories.

For complete API documentation, see [Logos API Reference](logos/docs/API_REFERENCE.md).

# BAD - Generic link text
See [here](../theory/COMPARISON.md) for more information.

Click [this link](logos/docs/API_REFERENCE.md) for documentation.
```

## Mathematical Notation Standards

### LaTeX in Code, Unicode in Documentation

**Core Rule**: All code must use LaTeX notation; documentation may use Unicode for clarity.

```python
# Code files - LaTeX only
MODAL_FORMULAS = [
    "\\Box (A \\rightarrow B)",  # LaTeX required
    "\\Diamond A",
    "(\\neg A \\vee B)"
]

# Error - Unicode in code breaks parser
# BAD_FORMULAS = ["□(A → B)", "◇A"]  # This will fail!
```

```markdown
<!-- Documentation files - Unicode for clarity -->
The necessity operator □ (written as `\\Box` in code) expresses that a formula is necessarily true.

Examples:
- Code: `"\\Box A"`
- Display: □A  
- Meaning: A is necessarily true
```

### Operator Documentation Standards

When documenting logical operators:

```markdown
| Operator | LaTeX Code | Unicode | Arity | Description |
|----------|------------|---------|-------|-------------|
| Negation | `\\neg` | ¬ | 1 | Logical negation |
| Conjunction | `\\wedge` | ∧ | 2 | Logical and |
| Disjunction | `\\vee` | ∨ | 2 | Logical or |
| Implication | `\\rightarrow` | → | 2 | Material conditional |
| Biconditional | `\\leftrightarrow` | ↔ | 2 | Material biconditional |
| Necessity | `\\Box` | □ | 1 | Necessary truth |
| Possibility | `\\Diamond` | ◇ | 1 | Possible truth |
```

### Formula Display Standards

```markdown
# Show both representations when introducing formulas
The conjunction formula `(A \\wedge B)` displays as (A ∧ B).

# Code examples always use LaTeX
```python
premises = ["\\Box (A \\rightarrow B)", "\\Box A"]
conclusions = ["\\Box B"]
```

# Display examples may use Unicode for readability
This represents the modal logic argument:
1. □(A → B)  [premise]
2. □A        [premise]  
3. □B        [conclusion]
```

### Mathematical Context Documentation

```markdown
# Provide mathematical context when relevant
## Truthmaker Semantics

This implementation follows Kit Fine's truthmaker semantics where:
- States are represented as bit vectors
- Verification is exact (not inexact)
- Fusion follows classical Boolean algebra

Mathematical foundation: Fine, K. (2017). Truthmaker semantics. *Journal of Philosophical Logic*, 46(2), 199-225.
```

## File Tree Formatting Standards

### Comment Alignment in File Trees

When documenting directory structures or file trees, align all comment `#` characters at the same column for professional appearance and readability:

```markdown
# CORRECT - All '#' characters aligned vertically at column 36
docs/
├── core/                          # Foundation standards
│   ├── CODE_STANDARDS.md          # Code quality and style
│   ├── ARCHITECTURE.md            # System design patterns
│   └── TESTING.md                 # Test requirements (TDD)
├── implementation/                # Development guidelines
│   ├── DEVELOPMENT_WORKFLOW.md    # Complete dev process
│   └── REFACTORING.md             # Systematic improvement
└── templates/                     # Reusable templates
    └── theory_template.py         # Theory implementation template

# INCORRECT - Misaligned '#' characters (directories have extra space)
docs/
├── core/                           # Foundation standards (# at column 37)
│   ├── CODE_STANDARDS.md          # Code quality (# at column 36)
│   └── TESTING.md                 # Test requirements (# at column 36)
└── templates/                      # Templates (# at column 37)

# INCORRECT - Comments start at wildly different positions
docs/
├── core/               # Foundation standards
│   ├── CODE_STANDARDS.md  # Code quality
│   └── TESTING.md    # Test requirements
└── templates/     # Templates
```

**Important**: Ensure the `#` character starts at exactly the same column for both directories and files. Directory names typically need fewer spaces before the `#` than file names.

### File Tree Best Practices

1. **Use consistent box-drawing characters**: `├──`, `└──`, `│`
2. **Align comments at a reasonable column**: Usually column 37-40 for typical file names
3. **Keep descriptions concise**: One-line summaries only
4. **Show relevant depth**: Usually 2-3 levels deep is sufficient
5. **Use ellipsis for truncation**: `...` to indicate more files exist

```markdown
# Example of proper file tree documentation
project/
├── src/                            # Source code
│   ├── core/                       # Core functionality
│   │   ├── __init__.py             # Package initialization
│   │   ├── models.py               # Data models
│   │   └── utils.py                # Utility functions
│   └── tests/                      # Test suite
│       ├── unit/                   # Unit tests
│       │   └── ...                 # Additional test files
│       └── integration/            # Integration tests
└── docs/                           # Documentation
    └── README.md                   # Project overview
```

### Column Calculation for Alignment

To determine the appropriate comment column:
1. Find the longest path in your tree
2. Add 2-4 spaces after it for padding
3. Align all comments at that column

```python
# Helper for calculating alignment column
longest_line = "│   └── CONTINUOUS_IMPROVEMENT.md"
padding = 2
comment_column = len(longest_line) + padding  # = 37
```

## Templates and Examples

### README Template

See [README_TEMPLATE.md](../../Docs/maintenance/templates/README_TEMPLATE.md) for the standard README structure.

### Docstring Templates

```python
# Function template
def function_name(param1: Type1, param2: Type2 = default) -> ReturnType:
    """
    Brief one-line summary.
    
    Detailed description if needed.
    
    Args:
        param1: Description with type and constraints
        param2: Description with default behavior
        
    Returns:
        Description of return value structure
        
    Raises:
        ExceptionType: When and why raised
        
    Example:
        >>> result = function_name(arg1, arg2)
        >>> print(result)
        expected output
    """

# Class template  
class ClassName:
    """
    Brief one-line summary.
    
    Detailed description of purpose and behavior.
    
    Attributes:
        attr1: Description of public attributes
        attr2: Description with constraints
    
    Example:
        >>> obj = ClassName(param)
        >>> result = obj.method()
    """
```

### API Reference Template

```markdown
# Component API Reference

[Navigation links]

## Table of Contents
[Complete TOC]

## Overview
[API scope and purpose]

## Core Functions
[All public functions with complete documentation]

## Classes  
[All public classes with methods and properties]

## Examples
[Working examples showing real usage]

## Error Handling
[Common exceptions and handling patterns]
```

## Quality Metrics and Maintenance

### Documentation Quality Metrics

1. **Completeness Metrics**:
   - Every public function has a docstring
   - Every directory has a README.md
   - All examples are tested and working
   - All internal links are valid

2. **Accuracy Metrics**:
   - Code examples match current API
   - File paths and references are current
   - Statistics match actual implementation
   - Version-specific information is updated

3. **Usefulness Metrics**:
   - Documentation answers real user questions
   - Examples solve practical problems
   - Error messages provide actionable guidance
   - Navigation helps users find information

### Maintenance Procedures

#### During Development

```bash
# Check for broken internal links
find docs/ -name "*.md" -exec grep -l "\]\(" {} \; | \
  xargs -I {} sh -c 'echo "Checking {}" && grep -o "\]\([^)]*\)" {} | cut -d"(" -f2 | cut -d")" -f1'

# Verify code examples are valid Python
grep -r "```python" docs/ | grep -v "# INCORRECT\|# BAD\|# WRONG"

# Check for outdated file counts in READMEs
grep -r "([0-9]* tests)" */README.md
```

#### During Releases

1. **Update Version References**: Check all version-specific documentation
2. **Validate Examples**: Run all code examples to ensure they work
3. **Check External Links**: Verify all external links are still valid
4. **Update Statistics**: Update file counts, test counts, etc.

#### Monthly Maintenance

1. **Link Audit**: Check all internal and external links
2. **Example Verification**: Run all documented examples
3. **Content Review**: Remove outdated information
4. **Navigation Audit**: Ensure all documents are reachable

### Quality Assurance Checklist

Before committing documentation changes:

- [ ] **Completeness**: All required sections present
- [ ] **Accuracy**: All examples tested and working
- [ ] **Navigation**: Header and footer links included and valid
- [ ] **Formatting**: Consistent markdown formatting
- [ ] **Spelling**: No spelling or grammar errors
- [ ] **Links**: All internal links point to existing files
- [ ] **Examples**: All code examples use correct syntax
- [ ] **Standards**: Follows all documentation standards
- [ ] **Audience**: Appropriate for intended users
- [ ] **Context**: Integrates well with related documentation

## User vs Developer Documentation

### User Documentation Focus

User documentation prioritizes practical accomplishment of goals:

```markdown
# GOOD - User-focused documentation
## Checking Argument Validity

To check if an argument is logically valid:

1. Create your premises and conclusions:
```python
premises = ["\\Box (A \\rightarrow B)", "\\Box A"]
conclusions = ["\\Box B"]
```

2. Choose your logical theory:
```python
from model_checker.theory_lib import logos
theory = logos.get_theory(['modal'])
```

3. Check validity:
```python
result = theory.check_validity(premises, conclusions)
if result.valid:
    print("Valid argument!")
else:
    print(f"Invalid: {result.countermodel}")
```

# BAD - Implementation-focused documentation
## Validity Checking Implementation

The validity checker uses Z3 SAT solving with bit vector representations.
The LogosSemantics class implements truthmaker semantics following Fine (2017).
```

### Developer Documentation Focus

Developer documentation explains internal structure and design decisions:

```markdown
# GOOD - Developer-focused documentation
## Architecture: Validity Checking

The validity checker follows a three-stage pipeline:

1. **Parsing** (Syntax module): Converts LaTeX strings to AST
2. **Translation** (ModelConstraints): Converts AST to Z3 constraints  
3. **Solving** (ModelStructure): Uses Z3 to find countermodels

Design decisions:
- Bit vectors represent truth states for efficiency
- Separate Z3 contexts prevent state leakage between examples
- Constraint generation is theory-agnostic for modularity

Key classes:
- `Syntax`: Handles parsing and validation
- `ModelConstraints`: Bridges syntax and semantics
- `ModelStructure`: Manages Z3 solver interaction
```

### Documentation Separation Guidelines

| Content Type | User Docs | Developer Docs |
|-------------|-----------|----------------|
| **Examples** | End-to-end workflows | Component integration |
| **Errors** | How to fix problems | Why errors occur |
| **Configuration** | What settings do | How settings work internally |
| **Theory** | What theories exist | How theories are implemented |
| **Performance** | When things are slow | Why things are slow |

## Changelog and Version Control

### Changelog Documentation

Major changes should be documented in changelogs:

```markdown
# Changelog

## [Unreleased]

### Added
- New counterfactual operators for logos theory
- Integration tests for theory loading

### Changed  
- Updated Z3 timeout handling for better error messages
- Improved performance for large N values

### Fixed
- Fixed edge case in bimodal semantics for N=1
- Corrected LaTeX parsing for nested operators

### Removed
- Deprecated old-style settings format
```

### Version Control Integration

```bash
# Document significant API changes in commit messages
git commit -m "Add counterfactual operators to logos theory

- Implements Fine's counterfactual semantics  
- Adds boxright and diamondright operators
- Updates API documentation and examples
- Breaking change: new operator precedence rules

Closes #123"
```

### Documentation Versioning

1. **Keep Current**: Update docs immediately when implementation changes
2. **No Compatibility**: Don't maintain docs for old versions
3. **Clear Deprecation**: Remove outdated information promptly  
4. **Migration Guides**: Help users adapt to changes when needed

## Success Metrics

### Documentation Effectiveness Metrics

1. **User Success Metrics**:
   - Users can complete tasks without asking questions
   - Error messages lead to successful problem resolution
   - Examples work on first try without modification
   - New users become productive quickly

2. **Maintenance Efficiency Metrics**:
   - Documentation stays current with implementation
   - Changes require minimal documentation updates
   - Information is easy to find and update
   - No duplicate or conflicting information

3. **Quality Metrics**:
   - All examples are tested and working
   - All internal links are valid
   - Documentation answers real user questions
   - Information is accurate and up-to-date

### Measuring Documentation Success

#### User Feedback Indicators

```python
# Track documentation effectiveness through:
# 1. User questions that documentation should answer
# 2. Common error patterns that need better explanation  
# 3. Examples that users need but don't exist
# 4. Parts of the API that are confusing or unused
```

#### Maintenance Health Indicators

```bash
# Check documentation health with:
find . -name "*.md" -exec grep -l "TODO\|FIXME\|XXX" {} \;  # Incomplete docs
find . -name "*.md" -exec grep -l "TBD\|Coming Soon" {} \;  # Placeholder content
grep -r "broken\|outdated\|deprecated" docs/               # Content that needs updates
```

#### Quality Assurance Indicators

1. **Example Validation**: All code examples run successfully
2. **Link Validation**: All internal links point to existing content
3. **Content Freshness**: Documentation updated within 1 week of implementation changes
4. **Completeness**: All public APIs have documentation
5. **Consistency**: Similar concepts documented in similar ways

### Continuous Improvement

1. **Regular Review**: Monthly documentation quality review
2. **User Feedback**: Collect and act on user documentation needs
3. **Metric Tracking**: Monitor documentation health metrics
4. **Standards Evolution**: Update standards based on experience
5. **Tool Integration**: Use tools to maintain documentation quality

## Conclusion

These documentation standards create a foundation for clear, maintainable, and useful documentation across the ModelChecker framework. They emphasize:

- **User-centric design** over technical completeness
- **Working examples** over abstract descriptions  
- **Current accuracy** over comprehensive coverage
- **Practical guidance** over theoretical explanation
- **Consistent patterns** over individual creativity

Apply these standards consistently to create documentation that truly serves users and maintainers effectively.

---

[← Code Standards](CODE_STANDARDS.md) | [Back to Maintenance](../README.md) | [Testing Standards →](TESTING.md)