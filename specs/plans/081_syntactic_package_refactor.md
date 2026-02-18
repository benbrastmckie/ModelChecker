# Plan 081: Syntactic Package Refactor

**Status:** Approved  
**Priority:** P1 (Critical)  
**Timeline:** 2 weeks  
**Compliance Score:** 45/100 → 90/100  

## Executive Summary

The syntactic package handles logical formula processing, operator management, and syntactic validation. Critical deficiencies include 0% type hint coverage (29 functions across 5 core files), minimal error handling, and 2 TODO comments. This refactor will establish comprehensive type safety, robust error handling, and improved maintainability.

## Current State Analysis

### Package Structure
```
syntactic/
├── __init__.py          # Package exports (25 lines)
├── atoms.py             # Z3 atomic propositions (33 lines, 1 function)
├── sentence.py          # Sentence class for formulas (217 lines, 8 methods)
├── operators.py         # Operator base classes (336 lines, 11 methods)
├── collection.py        # OperatorCollection registry (120 lines, 6 methods)
├── syntax.py            # Syntax processor (212 lines, 3 methods)
└── tests/              # Test suite (7 files, ~1000 lines)
    ├── unit/           # Unit tests for each module
    └── integration/    # Integration tests
```

### Compliance Gaps
- **Type Hints:** 0/29 core functions (0%)
- **Error Handling:** No custom exceptions
- **Technical Debt:** 2 TODO comments in operators.py
- **Test Coverage:** Good (comprehensive test suite)
- **Documentation:** Good (README present, well-documented)

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

#### Day 3: Type Hints for atoms.py (1 function)
```python
# Before
def AtomVal(i):
    return AtomSort.constructor(0)(i)

# After
from typing import Union
import z3
from .types import AtomType

def AtomVal(i: Union[int, str]) -> AtomType:
    """Create an atomic proposition value.
    
    Args:
        i: Index or identifier for the atom
        
    Returns:
        Z3 datatype reference for the atom
        
    Examples:
        >>> atom_p = AtomVal(0)  # Creates AtomSort!val!0
        >>> atom_q = AtomVal(1)  # Creates AtomSort!val!1
    """
    return AtomSort.constructor(0)(i)
```

#### Day 4-5: Type Hints for sentence.py (8 methods)
```python
# sentence.py type hints
from typing import List, Optional, Dict, Any
from .types import PrefixList, FormulaString
from .errors import InvalidFormulaError, ParseError

class Sentence:
    def __init__(self, infix_sentence: FormulaString) -> None:
        """Initialize sentence from infix notation."""
        if not infix_sentence:
            raise InvalidFormulaError(
                "Formula cannot be empty",
                formula="",
                context={'suggestion': 'Provide a non-empty formula'}
            )
        # ... implementation
    
    def prefix(self, infix_sentence: FormulaString) -> PrefixList:
        """Convert infix to prefix notation."""
        # ... implementation
    
    def update_types(self, operator_collection: 'OperatorCollection') -> None:
        """Update operator type references."""
        # ... implementation
```

### Week 2: Remaining Modules and Polish

#### Day 6-7: Type Hints for operators.py (11 methods)
```python
from typing import Optional, List, Dict, Any
from abc import ABC, abstractmethod
from .types import ISemantics, OperatorName
from .errors import ArityError

class Operator(ABC):
    """Abstract base class for logical operators."""
    
    name: OperatorName
    arity: int
    
    def __init__(self, semantics: ISemantics) -> None:
        """Initialize operator with semantics."""
        # ... implementation
    
    def general_print(
        self, 
        sentence_obj: 'Sentence',
        eval_point: Dict[str, Any],
        indent_num: int,
        use_colors: bool
    ) -> str:
        """Generate formatted output for operator evaluation."""
        # TODO: make this method more deterministic
        # ... implementation

class DefinedOperator(Operator):
    """Base class for user-defined operators."""
    
    primitive: bool = False
    
    @abstractmethod
    def derived_definition(self, *args: Any) -> 'Sentence':
        """Define operator in terms of primitives."""
        pass
```

#### Day 8: Type Hints for collection.py (6 methods)
```python
from typing import Dict, List, Optional, Iterator, Type
from .types import OperatorName, PrefixList
from .errors import DuplicateOperatorError, UnknownOperatorError

class OperatorCollection:
    """Registry for logical operators."""
    
    operators: Dict[OperatorName, Type['Operator']]
    
    def __init__(self, *input: Type['Operator']) -> None:
        """Initialize with operator classes."""
        # ... implementation
    
    def __iter__(self) -> Iterator[OperatorName]:
        """Iterate over operator names."""
        return iter(self.operators)
    
    def __getitem__(self, value: OperatorName) -> Type['Operator']:
        """Get operator by name."""
        if value not in self.operators:
            raise UnknownOperatorError(value, list(self.operators.keys()))
        return self.operators[value]
    
    def add_operator(self, operator: Type['Operator']) -> None:
        """Add operator to collection."""
        # ... implementation
    
    def apply_operator(self, prefix_sentence: PrefixList) -> Any:
        """Apply operator to prefix sentence."""
        # ... implementation
```

#### Day 9: Type Hints for syntax.py (3 methods) and Create types.py

**syntax.py type hints:**
```python
from typing import List, Optional, Dict, Set
from .types import FormulaString
from .errors import CircularDefinitionError

class Syntax:
    """Process and validate syntactic structures."""
    
    def __init__(
        self,
        premises: List[FormulaString],
        conclusions: List[FormulaString],
        additional_operators: Optional['OperatorCollection'] = None,
        inference: bool = False
    ) -> None:
        """Initialize syntax processor."""
        # ... implementation
    
    def initialize_sentences(
        self, 
        infix_sentences: List[FormulaString]
    ) -> List['Sentence']:
        """Convert formulas to sentence objects."""
        # ... implementation
    
    def circularity_check(
        self,
        operator_collection: 'OperatorCollection'
    ) -> None:
        """Check for circular operator definitions."""
        # ... implementation
```

**types.py creation:**
```python
# syntactic/types.py
from typing import Union, List, Dict, Any, Optional, Protocol
import z3

# Type aliases
AtomType = z3.DatatypeRef
OperatorName = str
FormulaString = str
PrefixList = List[Union[str, List]]

class ISemantics(Protocol):
    """Protocol for semantic implementations."""
    def evaluate(self, *args) -> z3.BoolRef: ...
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
# operators.py:94
# TODO: make this method more deterministic
# Solution: Use OrderedDict for consistent ordering
from collections import OrderedDict

def general_print(self, ...):
    # Use OrderedDict for world ordering
    world_results = OrderedDict()
    # ... rest of implementation

# operators.py:144
# TODO: is there an approach that is agnostic about what the eval_point includes?
# Solution: Define EvalPoint protocol
from typing import Protocol

class EvalPoint(Protocol):
    """Protocol for evaluation points."""
    world: Any
    time: Optional[Any] = None
    assignment: Optional[Dict] = None
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
- Functions typed: 0/29 → 29/29
- Error classes: 0 → 10+ (framework ready)
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

- [ ] All 29 core functions have type hints
- [ ] Error hierarchy implemented and tested (errors.py created)
- [ ] Both TODO items resolved with documented solutions
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