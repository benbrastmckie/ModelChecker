# Plan 086: Theory_lib Complete Refactor

**Status:** Approved  
**Priority:** P1 (Critical)  
**Timeline:** 5 weeks  
**Compliance Score:** 38/100 → 90/100  

## Executive Summary

The theory_lib package is the largest and most complex in the framework (17,581 lines, 27 files) with the lowest compliance score (38/100). This comprehensive refactor addresses 597 functions needing type hints, creates a complete error handling framework, fixes 43 files with import violations, and resolves 9 TODO/FIXME items. Due to its scope and complexity, this is scheduled last to apply lessons learned from other refactors.

## Current State Analysis

### Package Structure
```
theory_lib/
├── __init__.py              # Package exports
├── meta_data.py             # Theory metadata
├── bimodal/                 # Bimodal logic implementation
│   ├── __init__.py         # Theory initialization
│   ├── semantic.py         # Semantic definitions
│   ├── examples.py         # Theory examples
│   ├── operators.py        # Logical operators
│   ├── iterate.py          # Iteration logic
│   └── tests/              # Test suite
├── exclusion/              # Exclusion semantics
│   ├── __init__.py         # Theory initialization
│   ├── semantic.py         # Semantic definitions
│   ├── examples.py         # Theory examples
│   ├── operators.py        # Logical operators
│   ├── iterate.py          # Iteration logic
│   └── tests/              # Test suite
├── imposition/             # Imposition semantics
│   ├── __init__.py         # Theory initialization
│   ├── semantic.py         # Semantic definitions
│   ├── examples.py         # Theory examples
│   ├── operators.py        # Logical operators
│   ├── iterate.py          # Iteration logic
│   └── tests/              # Test suite
├── logos/                  # Hyperintensional logic
│   ├── __init__.py         # Theory initialization
│   ├── semantic.py         # Semantic definitions
│   ├── examples.py         # Theory examples
│   ├── operators.py        # Logical operators
│   ├── iterate.py          # Iteration logic
│   ├── subtheories/        # Specialized subtheories
│   └── tests/              # Test suite
└── docs/                   # Theory documentation
```

### Critical Deficiencies
- **Type Hints:** 24/621 functions (3.9%) ❌❌❌
- **Error Handling:** No framework (0 custom exceptions) ❌❌
- **Import Organization:** 43 files with violations ❌❌
- **Technical Debt:** 9 TODO/FIXME comments ❌
- **Test Coverage:** Good (1.56 ratio) ✓

## Implementation Strategy

Given the massive scope, we'll use a systematic, theory-by-theory approach with heavy automation assistance.

## Week 1: Foundation and Infrastructure

### Day 1-2: Error Handling Framework

```python
# theory_lib/errors.py
from typing import Dict, Any, Optional, List
from enum import Enum

class ErrorSeverity(Enum):
    """Error severity levels."""
    WARNING = "warning"
    ERROR = "error"
    CRITICAL = "critical"

class TheoryError(Exception):
    """Base exception for theory library.
    
    Provides rich context for debugging and recovery.
    """
    def __init__(
        self,
        message: str,
        theory: Optional[str] = None,
        severity: ErrorSeverity = ErrorSeverity.ERROR,
        context: Optional[Dict[str, Any]] = None,
        suggestion: Optional[str] = None,
        related_errors: Optional[List[Exception]] = None
    ):
        super().__init__(message)
        self.theory = theory
        self.severity = severity
        self.context = context or {}
        self.suggestion = suggestion
        self.related_errors = related_errors or []
    
    def __str__(self) -> str:
        parts = [str(self.args[0])]
        if self.theory:
            parts.append(f"Theory: {self.theory}")
        if self.severity != ErrorSeverity.ERROR:
            parts.append(f"Severity: {self.severity.value}")
        if self.suggestion:
            parts.append(f"Suggestion: {self.suggestion}")
        return " | ".join(parts)

# Theory Loading Errors
class TheoryLoadError(TheoryError):
    """Theory cannot be loaded."""
    pass

class TheoryNotFoundError(TheoryLoadError):
    """Theory module not found."""
    pass

class TheoryConfigurationError(TheoryError):
    """Theory misconfiguration."""
    pass

# Semantic Errors
class SemanticError(TheoryError):
    """Base for semantic errors."""
    pass

class SemanticValidationError(SemanticError):
    """Semantic validation failed."""
    pass

class ModelConstructionError(SemanticError):
    """Model construction failed."""
    pass

# Formula Errors
class FormulaError(TheoryError):
    """Base for formula errors."""
    pass

class FormulaParsingError(FormulaError):
    """Formula parsing failed."""
    pass

class FormulaValidationError(FormulaError):
    """Formula validation failed."""
    pass

# Operator Errors
class OperatorError(TheoryError):
    """Base for operator errors."""
    pass

class UnknownOperatorError(OperatorError):
    """Unknown operator encountered."""
    pass

class OperatorArityError(OperatorError):
    """Wrong number of arguments for operator."""
    pass

# Subtheory Errors
class SubtheoryError(TheoryError):
    """Base for subtheory errors."""
    pass

class SubtheoryLoadError(SubtheoryError):
    """Subtheory loading failed."""
    pass

class SubtheoryConflictError(SubtheoryError):
    """Subtheory conflict detected."""
    pass

# Witness Errors (Exclusion-specific)
class WitnessError(TheoryError):
    """Base for witness errors."""
    pass

class WitnessNotFoundError(WitnessError):
    """Required witness not found."""
    pass

# Constraint Errors
class ConstraintError(TheoryError):
    """Base for constraint errors."""
    pass

class UnsatisfiableError(ConstraintError):
    """Constraints are unsatisfiable."""
    pass
```

### Day 3-4: Import Cleanup Script and Execution

```python
# scripts/fix_theory_imports.py
import re
from pathlib import Path
from typing import Set, List, Tuple

def fix_star_imports(filepath: Path) -> int:
    """Fix star imports in file.
    
    Returns number of fixes made.
    """
    content = filepath.read_text()
    original = content
    
    # Pattern for star imports
    star_pattern = r'^from ([\w\.]+) import \*$'
    
    # Common imports to replace
    replacements = {
        'model_checker.syntactic': [
            'parse_formula', 'validate_syntax', 'SyntaxError'
        ],
        'model_checker.utils': [
            'create_variable', 'format_output', 'clean_formula'
        ],
        '..defaults': [
            'DEFAULT_SETTINGS', 'DEFAULT_TIMEOUT', 'MAX_STATES'
        ]
    }
    
    for match in re.finditer(star_pattern, content, re.MULTILINE):
        module = match.group(1)
        if module in replacements:
            imports = ', '.join(replacements[module])
            new_line = f'from {module} import {imports}'
            content = content.replace(match.group(0), new_line)
    
    if content != original:
        filepath.write_text(content)
        return content.count('from') - original.count('*')
    return 0

# Run on all theory_lib files
theory_path = Path('src/model_checker/theory_lib')
total_fixes = 0
for py_file in theory_path.rglob('*.py'):
    if 'test' not in str(py_file):
        fixes = fix_star_imports(py_file)
        if fixes > 0:
            print(f"Fixed {fixes} imports in {py_file}")
            total_fixes += fixes

print(f"Total: Fixed {total_fixes} star imports")
```

### Day 5: Type System Foundation

```python
# theory_lib/types.py
from typing import (
    TypeVar, Dict, List, Optional, Union, Any,
    Protocol, Callable, Tuple, Set, runtime_checkable
)
from abc import ABC, abstractmethod
import z3

# Type variables
T = TypeVar('T')
S = TypeVar('S', bound='Semantics')
P = TypeVar('P', bound='Proposition')
M = TypeVar('M', bound='ModelStructure')

# Core types
TheoryName = str
OperatorName = str
PropositionName = str
StateId = Union[int, str]
WorldId = Union[int, str]

# Z3 types
Z3Expr = Union[z3.BoolRef, z3.ArithRef]
Z3Model = z3.ModelRef
Z3Solver = z3.Solver

# Theory configuration
TheoryConfig = Dict[str, Any]
OperatorRegistry = Dict[OperatorName, 'Operator']

# Protocols
@runtime_checkable
class Semantics(Protocol):
    """Protocol for semantic implementations."""
    def evaluate(self, formula: str, model: Any) -> bool: ...
    def generate_constraints(self) -> List[Z3Expr]: ...

@runtime_checkable
class Proposition(Protocol):
    """Protocol for proposition implementations."""
    name: str
    def to_z3(self) -> Z3Expr: ...

@runtime_checkable
class ModelStructure(Protocol):
    """Protocol for model structures."""
    def get_states(self) -> List[StateId]: ...
    def get_relations(self) -> Dict[str, Any]: ...

@runtime_checkable
class Operator(Protocol):
    """Protocol for operators."""
    name: str
    arity: int
    def apply(self, *args: Any) -> Any: ...

# Callback types
FormulaValidator = Callable[[str], bool]
ModelValidator = Callable[[Any], bool]
ConstraintGenerator = Callable[[], List[Z3Expr]]
```

## Week 2: Base Modules and Bimodal Theory

### Day 6: Type hints for base modules (38 functions)

```python
# defaults.py - 12 functions
from typing import Dict, Any, Optional

DEFAULT_SETTINGS: Dict[str, Any] = {
    'timeout': 5000,
    'max_states': 10,
    'reflexive': False
}

def get_default(
    key: str,
    fallback: Optional[Any] = None
) -> Any:
    """Get default setting value."""
    return DEFAULT_SETTINGS.get(key, fallback)

def update_defaults(
    updates: Dict[str, Any]
) -> None:
    """Update default settings."""
    DEFAULT_SETTINGS.update(updates)

# base_theory.py - 26 functions
from abc import ABC, abstractmethod
from typing import Generic, TypeVar, Optional, List
from .types import TheoryConfig, Z3Expr

T_Sem = TypeVar('T_Sem', bound='BaseSemantics')
T_Prop = TypeVar('T_Prop', bound='BaseProposition')
T_Model = TypeVar('T_Model', bound='BaseModelStructure')

class BaseTheory(ABC, Generic[T_Sem, T_Prop, T_Model]):
    """Abstract base class for theories."""
    
    @abstractmethod
    def create_semantics(self) -> T_Sem:
        """Create semantics instance."""
        pass
    
    @abstractmethod
    def create_proposition(self, name: str) -> T_Prop:
        """Create proposition instance."""
        pass
    
    @abstractmethod
    def create_model_structure(self) -> T_Model:
        """Create model structure instance."""
        pass
```

### Day 7-8: Bimodal theory type hints (89 functions)

```python
# bimodal/semantics.py - 34 functions
from typing import Dict, List, Optional, Tuple, Set
import z3
from ..types import StateId, WorldId, Z3Expr, Z3Model
from ..errors import SemanticValidationError

class BimodalSemantics:
    """Semantics for bimodal logic."""
    
    def __init__(
        self,
        num_worlds: int = 3,
        num_states: int = 3
    ) -> None:
        """Initialize bimodal semantics.
        
        Args:
            num_worlds: Number of possible worlds
            num_states: Number of temporal states
        """
        self.num_worlds: int = num_worlds
        self.num_states: int = num_states
        self.solver: z3.Solver = z3.Solver()
    
    def evaluate(
        self,
        formula: str,
        world: WorldId,
        state: StateId,
        model: Optional[Z3Model] = None
    ) -> bool:
        """Evaluate formula at world-state pair.
        
        Args:
            formula: Formula to evaluate
            world: World identifier
            state: State identifier
            model: Optional Z3 model
            
        Returns:
            Truth value of formula
            
        Raises:
            SemanticValidationError: If evaluation fails
        """
        # TODO: Optimize recursive evaluation
        # (This will be resolved in Week 5)
        ...
    
    def generate_constraints(
        self,
        formula: str
    ) -> List[Z3Expr]:
        """Generate Z3 constraints for formula."""
        ...

# Continue with other bimodal files...
```

### Day 9-10: Resolve bimodal TODO/FIXME

```python
# bimodal/semantics.py:567
# FIXME: Handle edge case when temporal relations cycle
def check_temporal_consistency(
    self,
    relations: Dict[Tuple[StateId, StateId], bool]
) -> bool:
    """Check temporal consistency, handling cycles.
    
    RESOLVED: Implement cycle detection using DFS
    """
    visited: Set[StateId] = set()
    rec_stack: Set[StateId] = set()
    
    def has_cycle(state: StateId) -> bool:
        visited.add(state)
        rec_stack.add(state)
        
        for (s1, s2), exists in relations.items():
            if s1 == state and exists:
                if s2 not in visited:
                    if has_cycle(s2):
                        return True
                elif s2 in rec_stack:
                    return True
        
        rec_stack.remove(state)
        return False
    
    # Check all states for cycles
    all_states = {s for pair in relations for s in pair}
    for state in all_states:
        if state not in visited:
            if has_cycle(state):
                raise SemanticValidationError(
                    "Temporal cycle detected",
                    theory="bimodal",
                    context={'cycle_state': state}
                )
    
    return True
```

## Week 3: Exclusion and Imposition Theories

### Day 11-13: Exclusion theory (134 functions)

```python
# exclusion/semantics.py - 41 functions
from typing import Dict, List, Optional, Set
from ..types import StateId, Z3Expr, Z3Model
from ..errors import WitnessNotFoundError

class WitnessSemantics:
    """Exclusion semantics with witnesses."""
    
    def __init__(
        self,
        num_states: int = 3
    ) -> None:
        self.num_states: int = num_states
        self.witnesses: Dict[str, Set[StateId]] = {}
    
    def find_witness(
        self,
        formula: str,
        state: StateId
    ) -> Optional[StateId]:
        """Find witness for formula at state.
        
        Returns:
            Witness state if found, None otherwise
        """
        ...
    
    def validate_witnesses(
        self,
        model: Z3Model
    ) -> bool:
        """Validate all witnesses in model.
        
        Raises:
            WitnessNotFoundError: If required witness missing
        """
        ...

# exclusion/witnesses.py - 23 functions
class WitnessManager:
    """Manages witness relationships."""
    
    def __init__(self) -> None:
        self.witness_map: Dict[Tuple[StateId, str], StateId] = {}
    
    def add_witness(
        self,
        state: StateId,
        formula: str,
        witness: StateId
    ) -> None:
        """Add witness relationship."""
        self.witness_map[(state, formula)] = witness
    
    def get_witness(
        self,
        state: StateId,
        formula: str
    ) -> Optional[StateId]:
        """Get witness for formula at state."""
        return self.witness_map.get((state, formula))
```

### Day 14-15: Imposition theory (111 functions)

```python
# imposition/semantics.py - 38 functions
from typing import Dict, List, Optional, Set, Tuple
from ..types import StateId, Z3Expr
from ..errors import ModelConstructionError

class ImpositionSemantics:
    """Fine's imposition semantics."""
    
    def __init__(
        self,
        num_states: int = 3,
        allow_imposition: bool = True
    ) -> None:
        self.num_states: int = num_states
        self.allow_imposition: bool = allow_imposition
        self.impositions: Dict[StateId, Set[str]] = {}
    
    def impose(
        self,
        state: StateId,
        formula: str
    ) -> None:
        """Impose formula at state.
        
        Args:
            state: State where imposition occurs
            formula: Formula to impose
        """
        self.impositions.setdefault(state, set()).add(formula)
    
    def check_imposition(
        self,
        state: StateId,
        formula: str
    ) -> bool:
        """Check if formula is imposed at state."""
        return formula in self.impositions.get(state, set())

# imposition/operators.py - 26 functions
# TODO: Complete imposition operator
class ImpositionOperator:
    """Imposition operator implementation."""
    
    def __init__(
        self,
        name: str = 'IMP'
    ) -> None:
        self.name: str = name
        self.arity: int = 2
    
    def apply(
        self,
        state: StateId,
        formula: str
    ) -> Z3Expr:
        """Apply imposition operator.
        
        RESOLVED TODO: Implement full operator logic
        """
        # Create Z3 variable for imposition
        imp_var = z3.Bool(f'{self.name}_{state}_{formula}')
        
        # Add imposition constraints
        constraints = []
        # ... implementation
        return z3.And(constraints)
```

## Week 4: Logos Core and Subtheories

### Day 16-18: Logos core (142 functions)

```python
# logos/semantics.py - 52 functions
from typing import Dict, List, Optional, Set, Tuple, Union
from ..types import StateId, Z3Expr, OperatorRegistry
from ..errors import SubtheoryConflictError

class LogosSemantics:
    """Hyperintensional semantics with subtheories."""
    
    def __init__(
        self,
        num_states: int = 3,
        subtheories: Optional[List[str]] = None
    ) -> None:
        self.num_states: int = num_states
        self.subtheories: Set[str] = set(subtheories or [])
        self.operators: OperatorRegistry = {}
        self._load_subtheories()
    
    def _load_subtheories(self) -> None:
        """Load requested subtheories.
        
        Raises:
            SubtheoryLoadError: If subtheory cannot load
            SubtheoryConflictError: If subtheories conflict
        """
        for subtheory in self.subtheories:
            self._load_subtheory(subtheory)
    
    def _load_subtheory(
        self,
        name: str
    ) -> None:
        """Load individual subtheory."""
        # TODO: Optimize constraint generation for large models
        # (This will be resolved in Week 5)
        ...
    
    def evaluate_hyperintensional(
        self,
        formula: str,
        state: StateId,
        context: Dict[str, Any]
    ) -> bool:
        """Evaluate with hyperintensional context."""
        ...

# logos/model_structure.py - 36 functions
class LogosModelStructure:
    """Model structure for hyperintensional logic."""
    
    def __init__(
        self,
        num_states: int = 3
    ) -> None:
        self.num_states: int = num_states
        self.states: List[StateId] = list(range(num_states))
        self.relations: Dict[str, List[Tuple[StateId, StateId]]] = {}
        self.hyperintensional_content: Dict[StateId, Dict[str, Any]] = {}
    
    def add_hyperintensional_content(
        self,
        state: StateId,
        content_type: str,
        content: Any
    ) -> None:
        """Add hyperintensional content to state."""
        if state not in self.hyperintensional_content:
            self.hyperintensional_content[state] = {}
        self.hyperintensional_content[state][content_type] = content
```

### Day 19-20: Logos subtheories (145 functions)

```python
# logos/subtheories/modal/semantics.py - 28 functions
from typing import Dict, List, Optional
from ...types import StateId, Z3Expr

class ModalSubtheory:
    """Modal logic subtheory for Logos."""
    
    def __init__(
        self,
        axioms: Optional[List[str]] = None
    ) -> None:
        self.axioms: List[str] = axioms or ['T', 'K']
    
    def validate_modal_axioms(
        self,
        model: Any
    ) -> bool:
        """Validate modal axioms.
        
        TODO: Implement S5 axiom system
        RESOLVED: Add S5 support
        """
        validators = {
            'K': self._validate_k_axiom,
            'T': self._validate_t_axiom,
            'S4': self._validate_s4_axiom,
            'S5': self._validate_s5_axiom  # Added
        }
        
        for axiom in self.axioms:
            if axiom in validators:
                if not validators[axiom](model):
                    return False
        return True
    
    def _validate_s5_axiom(
        self,
        model: Any
    ) -> bool:
        """Validate S5 (euclidean) axiom."""
        # Implementation for S5
        ...

# Continue with other subtheories...
```

## Week 5: Optimization and Final Polish

### Day 21-22: Resolve remaining TODOs

```python
# logos/semantics.py:234
# TODO: Optimize constraint generation for large models
def generate_constraints(
    self,
    formula: str,
    optimize: bool = True
) -> List[Z3Expr]:
    """Generate optimized constraints.
    
    RESOLVED: Implement constraint optimization
    """
    if not optimize:
        return self._generate_basic_constraints(formula)
    
    # Optimization strategies
    constraints = []
    
    # 1. Cache repeated subformulas
    subformula_cache: Dict[str, Z3Expr] = {}
    
    # 2. Use incremental solving
    self.solver.push()
    
    # 3. Order constraints by complexity
    basic_constraints = self._extract_basic_constraints(formula)
    complex_constraints = self._extract_complex_constraints(formula)
    
    # Add basic first for early pruning
    constraints.extend(basic_constraints)
    constraints.extend(complex_constraints)
    
    return constraints

# exclusion/model_structure.py:456
# TODO: Performance improvement for witness search
def find_all_witnesses(
    self,
    formula: str
) -> Dict[StateId, Set[StateId]]:
    """Find all witnesses efficiently.
    
    RESOLVED: Use indexing for faster search
    """
    # Build index for quick lookup
    witness_index = self._build_witness_index()
    
    results = {}
    for state in self.states:
        witnesses = witness_index.get((state, formula), set())
        if witnesses:
            results[state] = witnesses
    
    return results
```

### Day 23: Automation script for remaining type hints

```python
# scripts/add_remaining_types.py
import ast
import astor
from pathlib import Path
from typing import Set

def add_any_types(filepath: Path) -> int:
    """Add Any type hints to untyped functions.
    
    Returns number of functions updated.
    """
    with open(filepath) as f:
        tree = ast.parse(f.read())
    
    updated = 0
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            # Check if has return type
            if node.returns is None:
                node.returns = ast.Name(id='Any')
                updated += 1
            
            # Check parameters
            for arg in node.args.args:
                if arg.annotation is None:
                    arg.annotation = ast.Name(id='Any')
    
    if updated > 0:
        # Add import
        import_added = False
        for n in ast.walk(tree):
            if isinstance(n, ast.ImportFrom):
                if n.module == 'typing':
                    if 'Any' not in [a.name for a in n.names]:
                        n.names.append(ast.alias(name='Any', asname=None))
                        import_added = True
                        break
        
        if not import_added:
            # Add new import
            new_import = ast.ImportFrom(
                module='typing',
                names=[ast.alias(name='Any', asname=None)],
                level=0
            )
            tree.body.insert(0, new_import)
        
        # Write back
        code = astor.to_source(tree)
        filepath.write_text(code)
    
    return updated

# Run on all theory files
total_updated = 0
for py_file in Path('src/model_checker/theory_lib').rglob('*.py'):
    if 'test' not in str(py_file):
        updated = add_any_types(py_file)
        if updated > 0:
            print(f"Added types to {updated} functions in {py_file}")
            total_updated += updated

print(f"Total: Updated {total_updated} functions")
```

### Day 24: Final type refinement

Replace generic `Any` types with specific types where possible:

```python
# Manual refinement of critical functions
# Replace Any with specific types after analysis

# Before
def evaluate(self, formula: Any, model: Any) -> Any:

# After  
def evaluate(
    self,
    formula: str,
    model: Z3Model
) -> bool:
```

### Day 25: Final testing and validation

```bash
# Run mypy on entire package
mypy src/model_checker/theory_lib --strict

# Check final type coverage
python scripts/check_type_coverage.py theory_lib
# Expected: 95%+ coverage

# Run all tests
pytest src/model_checker/theory_lib/tests/ -v

# Generate compliance report
python scripts/generate_compliance_report.py theory_lib
```

## Success Metrics

### Quantitative Goals
- Type hints: 24/621 → 590/621 functions (95%+)
- Custom exceptions: 0 → 15+ classes
- Star imports: 43 → 0
- TODO/FIXME: 9 → 0
- Compliance score: 38/100 → 90/100

### Qualitative Goals
- Full IDE support across all theories
- Clear error messages with recovery suggestions
- Clean import structure
- Optimized performance in critical paths

## Risk Management

### High Risk Areas
1. **Scale**: 597 functions to update
2. **Complexity**: Interconnected theories
3. **Time**: 5 weeks is aggressive

### Mitigation Strategies
1. **Automation**: Scripts for bulk updates
2. **Incremental**: Theory-by-theory approach
3. **Prioritization**: Core functions first
4. **Testing**: Continuous validation

## Definition of Done

- [ ] Error hierarchy implemented (15+ exception classes)
- [ ] All star imports removed (43 files cleaned)
- [ ] 95%+ functions have type hints
- [ ] All 9 TODO/FIXME items resolved
- [ ] mypy passes with reasonable strictness
- [ ] All existing tests pass (42 test files)
- [ ] Documentation updated
- [ ] Compliance score ≥ 90/100

---

**Related Documents:**
- [Plan 080: Framework Complete Refactor Overview](080_framework_complete_refactor_overview.md)
- [Research 042: Theory Library Compliance Deep Analysis](../research/042_theory_lib_compliance_deep_analysis.md)
- [Code Maintenance Standards](../../../maintenance/README.md)