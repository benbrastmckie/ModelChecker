# Plan 081: Syntactic Package Refactor

**Status:** Approved  
**Priority:** P1 (Critical)  
**Timeline:** 2 weeks  
**Compliance Score:** 45/100 → 90/100  

## Executive Summary

The syntactic package handles formula parsing and validation but has critical deficiencies: 0% type hint coverage (122 functions), no error handling framework, and minor technical debt. This refactor will establish it as a model implementation with full type safety and robust error handling.

## Current State Analysis

### Package Structure
```
syntactic/
├── __init__.py          # Package exports (45 lines)
├── parser.py            # Formula parsing (267 lines)
├── validator.py         # Syntax validation (189 lines)
├── transformer.py       # AST transformation (234 lines)
├── utils.py            # Parsing utilities (188 lines)
└── tests/              # Test suite (7 files, 1,018 lines)
```

### Compliance Gaps
- **Type Hints:** 0/122 functions (0%)
- **Error Handling:** No custom exceptions
- **Technical Debt:** 2 TODO comments
- **Test Coverage:** Good (1.40 ratio)
- **Documentation:** Good (README present)

## Implementation Plan

### Week 1: Foundation and Core Modules

#### Day 1-2: Error Handling Framework
```python
# syntactic/errors.py
from typing import Dict, Any, Optional, Union

class SyntacticError(Exception):
    """Base exception for syntactic operations."""
    def __init__(
        self, 
        message: str,
        formula: Optional[str] = None,
        position: Optional[int] = None,
        context: Optional[Dict[str, Any]] = None
    ):
        super().__init__(message)
        self.formula = formula
        self.position = position
        self.context = context or {}

class ParseError(SyntacticError):
    """Raised when formula parsing fails."""
    pass

class ValidationError(SyntacticError):
    """Raised when formula validation fails."""
    pass

class TransformationError(SyntacticError):
    """Raised when AST transformation fails."""
    pass

class SyntaxError(ParseError):
    """Raised for syntax errors in formulas."""
    def __init__(self, message: str, formula: str, position: int):
        super().__init__(
            message=f"Syntax error at position {position}: {message}",
            formula=formula,
            position=position
        )

class UnbalancedParenthesesError(ParseError):
    """Raised when parentheses are unbalanced."""
    pass

class UnknownOperatorError(ValidationError):
    """Raised when an unknown operator is encountered."""
    pass

class InvalidFormulaError(ValidationError):
    """Raised when formula structure is invalid."""
    pass
```

#### Day 3-4: Type Hints for parser.py (35 functions)
```python
# Before
def parse_formula(formula):
    tokens = tokenize(formula)
    ast = build_ast(tokens)
    return ast

# After
from typing import List, Union, Optional
from .types import Token, ASTNode, Formula

def parse_formula(formula: str) -> ASTNode:
    """Parse a logical formula into an AST.
    
    Args:
        formula: Logical formula string
        
    Returns:
        Root node of the AST
        
    Raises:
        ParseError: If formula cannot be parsed
    """
    tokens: List[Token] = tokenize(formula)
    ast: ASTNode = build_ast(tokens)
    return ast

def tokenize(formula: str) -> List[Token]:
    """Tokenize a formula string."""
    ...

def build_ast(tokens: List[Token]) -> ASTNode:
    """Build AST from tokens."""
    ...
```

#### Day 5: Type Hints for validator.py (28 functions)
```python
# Add types for validation functions
from typing import Set, Tuple, Protocol

class Validatable(Protocol):
    """Protocol for validatable objects."""
    def validate(self) -> bool: ...

def validate_syntax(
    ast: ASTNode,
    allowed_operators: Optional[Set[str]] = None
) -> Tuple[bool, Optional[str]]:
    """Validate AST syntax.
    
    Returns:
        Tuple of (is_valid, error_message)
    """
    ...

def check_operator(
    operator: str,
    arity: int,
    allowed: Set[str]
) -> bool:
    """Check if operator is allowed."""
    ...
```

### Week 2: Remaining Modules and Polish

#### Day 6-7: Type Hints for transformer.py (32 functions)
```python
from typing import TypeVar, Generic, Callable

T = TypeVar('T', bound=ASTNode)

class ASTTransformer(Generic[T]):
    """Transform AST nodes."""
    
    def transform(self, node: ASTNode) -> T:
        """Transform a node."""
        ...
    
    def visit(self, node: ASTNode) -> Any:
        """Visit a node."""
        method_name = f'visit_{node.type}'
        visitor: Callable = getattr(self, method_name, self.generic_visit)
        return visitor(node)
```

#### Day 8: Type Hints for utils.py (27 functions)
```python
def escape_latex(text: str) -> str:
    """Escape LaTeX special characters."""
    ...

def format_operator(
    operator: str,
    style: str = 'latex'
) -> str:
    """Format operator for display."""
    ...

def is_binary_operator(operator: str) -> bool:
    """Check if operator is binary."""
    ...
```

#### Day 9: Create types.py for Type Definitions
```python
# syntactic/types.py
from typing import Union, List, Dict, Any, Optional
from dataclasses import dataclass
from enum import Enum

class TokenType(Enum):
    """Token types for parsing."""
    ATOM = "atom"
    OPERATOR = "operator"
    LPAREN = "lparen"
    RPAREN = "rparen"
    EOF = "eof"

@dataclass
class Token:
    """Represents a token in formula."""
    type: TokenType
    value: str
    position: int

@dataclass
class ASTNode:
    """Abstract syntax tree node."""
    type: str
    value: Union[str, None]
    children: List['ASTNode']
    metadata: Dict[str, Any]

Formula = Union[str, ASTNode]
ParseResult = Tuple[bool, Optional[ASTNode], Optional[str]]
```

#### Day 10: Update Error Handling Throughout
```python
# Replace generic exceptions with specific ones
# Before
if not formula:
    raise ValueError("Empty formula")

# After
if not formula:
    raise InvalidFormulaError(
        "Formula cannot be empty",
        formula="",
        context={'suggestion': 'Provide a non-empty formula'}
    )
```

#### Day 11: Resolve TODO Items
```python
# parser.py:156
# TODO: Optimize recursive descent for deeply nested formulas
# Solution: Implement iterative parsing with explicit stack

# validator.py:234  
# TODO: Add support for custom operator validation
# Solution: Implement operator registry pattern
```

#### Day 12-13: Testing and Documentation
- Add tests for new error types
- Validate all type hints with mypy
- Update README with new error handling
- Run full test suite

#### Day 14: Final Validation
- Generate compliance report
- Ensure 90%+ type coverage
- Final code review

## Type Hint Priority

### Highest Priority (Core Functions)
1. `parse_formula()` - Entry point
2. `validate_syntax()` - Critical validation
3. `transform_ast()` - Core transformation
4. `tokenize()` - Foundation function

### File Order
1. **parser.py** (35 functions) - Core parsing
2. **validator.py** (28 functions) - Validation logic
3. **transformer.py** (32 functions) - AST operations
4. **utils.py** (27 functions) - Utilities

## Testing Strategy

### New Test Requirements
```python
# tests/test_errors.py
def test_parse_error_context():
    """Test that ParseError includes context."""
    with pytest.raises(ParseError) as exc:
        parse_formula("((A & B)")
    
    assert exc.value.formula == "((A & B)"
    assert exc.value.position is not None
    assert 'suggestion' in exc.value.context

def test_validation_error_hierarchy():
    """Test error hierarchy."""
    assert issubclass(UnknownOperatorError, ValidationError)
    assert issubclass(ValidationError, SyntacticError)
```

### Type Hint Testing
```python
# Run mypy for type checking
mypy src/model_checker/syntactic --strict

# Verify no Any types remain
grep -r "Any" src/model_checker/syntactic | grep -v "typing import"
```

## Migration Guide

### For Dependent Packages
```python
# Update imports in dependent code
# Before
from model_checker.syntactic import parse_formula

# After  
from model_checker.syntactic import parse_formula, ParseError

# Update error handling
try:
    ast = parse_formula(formula)
except ParseError as e:
    print(f"Parse failed: {e}")
    if e.position:
        print(f"Error at position {e.position}")
```

## Success Metrics

### Quantitative
- Type hint coverage: 0% → 95%+
- Functions typed: 0/122 → 116/122
- Error classes: 0 → 8+
- TODO items: 2 → 0
- Compliance score: 45/100 → 90/100

### Qualitative
- Full IDE autocomplete support
- Clear error messages with context
- Improved maintainability
- Better debugging experience

## Risk Mitigation

### Risks
1. **Breaking changes** for dependent packages
2. **Complex type definitions** for AST nodes
3. **Time estimate** may be optimistic

### Mitigations
1. Run tests for all dependent packages
2. Start with simple types, refine gradually
3. Buffer time in week 2 for overruns

## Rollback Plan

If issues arise:
1. Revert to previous commit
2. Address issues in feature branch
3. Re-apply changes incrementally
4. Validate each file independently

## Definition of Done

- [ ] All 122 functions have type hints
- [ ] Error hierarchy implemented and tested
- [ ] Both TODO items resolved
- [ ] All existing tests pass
- [ ] New error handling tests added
- [ ] mypy reports no errors with --strict
- [ ] Documentation updated
- [ ] Compliance score ≥ 90/100

---

**Related Documents:**
- [Plan 080: Framework Complete Refactor Overview](080_framework_complete_refactor_overview.md)
- [Research 041: Framework Quality and Compliance Audit](../research/041_framework_quality_compliance_audit.md)
- [Code Maintenance Standards](../../../maintenance/README.md)