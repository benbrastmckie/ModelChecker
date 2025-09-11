# Plan 083: Models Package Refactor

**Status:** Approved  
**Priority:** P2 (High)  
**Timeline:** 1 week  
**Compliance Score:** 73/100 → 90/100  

## Executive Summary

The models package defines core data structures for model checking but has low type hint coverage (24.6%) and minor technical debt. This refactor adds comprehensive type hints to 101 functions, resolves 2 TODO items, and ensures the package serves as a robust foundation for the framework's data model.

## Current State Analysis

### Package Structure
```
models/
├── __init__.py              # Package exports (34 lines)
├── model_variable.py        # Variable representations (312 lines)
├── model_builder.py         # Model construction (456 lines)
├── model_extractor.py       # Result extraction (289 lines)
├── semantic_model.py        # Semantic structures (455 lines)
├── errors.py               # Error definitions (56 lines) ✓
└── tests/                  # Test suite (10 files, 1,486 lines)
```

### Current Compliance
- **Type Hints:** 33/134 functions (24.6%) ⚠️
- **Error Handling:** 7 custom exceptions ✓
- **Technical Debt:** 2 TODO comments ⚠️
- **Test Coverage:** Excellent (2.00 ratio) ✓
- **Documentation:** Good README ✓
- **Import Organization:** Good ✓

## Implementation Strategy

Focus on adding type hints systematically while resolving technical debt. The existing error handling is good, so we'll enhance it minimally.

## Detailed Implementation Plan

### Day 1: Type System Foundation

#### Create types.py for Model-Specific Types
```python
# models/types.py
from typing import TypeVar, Union, Dict, List, Any, Protocol, Optional
from dataclasses import dataclass
import z3

# Core type definitions
T = TypeVar('T')
VariableName = str
StateId = Union[int, str]
RelationName = str
PropositionName = str

# Z3 type aliases
Z3Var = Union[z3.BoolRef, z3.IntRef, z3.RealRef]
Z3Model = z3.ModelRef
Z3Solver = z3.Solver

# Model data types
ModelData = Dict[str, Any]
StateData = Dict[StateId, Dict[PropositionName, bool]]
RelationData = Dict[RelationName, List[Tuple[StateId, StateId]]]

@dataclass
class ModelConfig:
    """Configuration for model building."""
    num_states: int
    num_relations: int
    allow_loops: bool = True
    reflexive: bool = False
    symmetric: bool = False
    transitive: bool = False

class ModelProtocol(Protocol):
    """Protocol for model implementations."""
    def get_states(self) -> List[StateId]: ...
    def get_relations(self) -> RelationData: ...
    def evaluate(self, prop: str, state: StateId) -> bool: ...
```

### Day 2: model_variable.py Type Hints (28 functions)

```python
# Before
def create_state_var(state_id, prefix='s'):
    return z3.Int(f'{prefix}_{state_id}')

def create_relation_var(rel_name, state1, state2):
    return z3.Bool(f'{rel_name}_{state1}_{state2}')

class ModelVariable:
    def __init__(self, name, var_type='bool'):
        self.name = name
        self.var_type = var_type
        self.z3_var = self._create_z3_var()

# After
from typing import Optional, Union, Literal, Dict, Any
import z3
from .types import StateId, RelationName, Z3Var

def create_state_var(
    state_id: StateId,
    prefix: str = 's'
) -> z3.IntRef:
    """Create a Z3 state variable.
    
    Args:
        state_id: State identifier
        prefix: Variable name prefix
        
    Returns:
        Z3 integer variable for state
    """
    return z3.Int(f'{prefix}_{state_id}')

def create_relation_var(
    rel_name: RelationName,
    state1: StateId,
    state2: StateId
) -> z3.BoolRef:
    """Create a Z3 relation variable.
    
    Args:
        rel_name: Relation name
        state1: Source state
        state2: Target state
        
    Returns:
        Z3 boolean variable for relation
    """
    return z3.Bool(f'{rel_name}_{state1}_{state2}')

VarType = Literal['bool', 'int', 'real']

class ModelVariable:
    """Represents a variable in the model."""
    
    def __init__(
        self,
        name: str,
        var_type: VarType = 'bool',
        context: Optional[z3.Context] = None
    ) -> None:
        """Initialize model variable.
        
        Args:
            name: Variable name
            var_type: Type of variable
            context: Optional Z3 context
        """
        self.name: str = name
        self.var_type: VarType = var_type
        self.context: Optional[z3.Context] = context
        self.z3_var: Z3Var = self._create_z3_var()
    
    def _create_z3_var(self) -> Z3Var:
        """Create appropriate Z3 variable."""
        ...
    
    def get_value(self, model: Z3Model) -> Any:
        """Get variable value from model."""
        ...
```

### Day 3: model_builder.py Type Hints (35 functions)

```python
# Before
class ModelBuilder:
    def __init__(self, config):
        self.config = config
        self.solver = z3.Solver()
        self.variables = {}
    
    def add_constraint(self, constraint):
        self.solver.add(constraint)
    
    def build(self):
        if self.solver.check() == z3.sat:
            return self.solver.model()
        return None

# After
from typing import Dict, List, Optional, Set, Tuple
import z3
from .types import ModelConfig, Z3Var, StateId, RelationName, ModelData
from .errors import ModelConstructionError

class ModelBuilder:
    """Builds semantic models from constraints."""
    
    def __init__(self, config: ModelConfig) -> None:
        """Initialize model builder.
        
        Args:
            config: Model configuration
        """
        self.config: ModelConfig = config
        self.solver: z3.Solver = z3.Solver()
        self.variables: Dict[str, Z3Var] = {}
        self._state_vars: Dict[StateId, z3.IntRef] = {}
        self._relation_vars: Dict[Tuple[RelationName, StateId, StateId], z3.BoolRef] = {}
    
    def add_constraint(self, constraint: z3.BoolRef) -> None:
        """Add constraint to solver.
        
        Args:
            constraint: Z3 boolean constraint
        """
        self.solver.add(constraint)
    
    def add_constraints(self, constraints: List[z3.BoolRef]) -> None:
        """Add multiple constraints."""
        self.solver.add(*constraints)
    
    def build(
        self,
        timeout: Optional[int] = None
    ) -> Optional[Z3Model]:
        """Build model from constraints.
        
        Args:
            timeout: Optional timeout in milliseconds
            
        Returns:
            Z3 model if satisfiable, None otherwise
            
        Raises:
            ModelConstructionError: If construction fails
        """
        if timeout:
            self.solver.set("timeout", timeout)
        
        result = self.solver.check()
        if result == z3.sat:
            return self.solver.model()
        elif result == z3.unknown:
            raise ModelConstructionError(
                "Model construction timed out",
                context={'timeout': timeout}
            )
        return None
    
    def create_states(self, num_states: int) -> List[StateId]:
        """Create state variables."""
        ...
    
    def create_relation(
        self,
        name: RelationName,
        properties: Optional[Dict[str, bool]] = None
    ) -> None:
        """Create relation with properties."""
        ...
```

### Day 4: model_extractor.py Type Hints (31 functions)

```python
# Before
def extract_model_data(z3_model, variables):
    data = {}
    for var_name, var in variables.items():
        data[var_name] = z3_model.eval(var)
    return data

class ModelExtractor:
    def __init__(self, z3_model):
        self.z3_model = z3_model
    
    def extract_states(self):
        states = []
        # Extract state information
        return states

# After
from typing import Dict, List, Set, Tuple, Optional, Any
import z3
from .types import (
    Z3Model, StateId, RelationName, PropositionName,
    StateData, RelationData, ModelData
)

def extract_model_data(
    z3_model: Z3Model,
    variables: Dict[str, Z3Var]
) -> ModelData:
    """Extract all variable values from model.
    
    Args:
        z3_model: Z3 model with assignments
        variables: Dictionary of variables
        
    Returns:
        Dictionary of variable names to values
    """
    data: ModelData = {}
    for var_name, var in variables.items():
        data[var_name] = z3_model.eval(var)
    return data

class ModelExtractor:
    """Extracts structured data from Z3 models."""
    
    def __init__(self, z3_model: Z3Model) -> None:
        """Initialize extractor with Z3 model.
        
        Args:
            z3_model: Z3 model to extract from
        """
        self.z3_model: Z3Model = z3_model
        self._cache: Dict[str, Any] = {}
    
    def extract_states(
        self,
        state_vars: Optional[List[z3.IntRef]] = None
    ) -> List[StateId]:
        """Extract state identifiers from model.
        
        Args:
            state_vars: Optional list of state variables
            
        Returns:
            List of state identifiers
        """
        if 'states' in self._cache:
            return self._cache['states']
        
        states: List[StateId] = []
        # Extract state information
        self._cache['states'] = states
        return states
    
    def extract_relations(
        self,
        relation_name: RelationName
    ) -> List[Tuple[StateId, StateId]]:
        """Extract relation pairs."""
        ...
    
    def extract_propositions(
        self,
        state: StateId
    ) -> Dict[PropositionName, bool]:
        """Extract proposition values for state."""
        ...
```

### Day 5: semantic_model.py Type Hints (40 functions) + TODO Resolution

```python
# Before
class SemanticModel:
    def __init__(self, states, relations, propositions):
        self.states = states
        self.relations = relations
        self.propositions = propositions
    
    # TODO: Add validation for model consistency
    def validate(self):
        pass
    
    # TODO: Implement model minimization
    def minimize(self):
        pass

# After
from typing import Dict, List, Set, Optional, Tuple, FrozenSet
from dataclasses import dataclass, field
from .types import StateId, RelationName, PropositionName, StateData, RelationData
from .errors import ModelValidationError

@dataclass
class SemanticModel:
    """Represents a complete semantic model."""
    
    states: List[StateId]
    relations: Dict[RelationName, List[Tuple[StateId, StateId]]]
    propositions: StateData
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def __post_init__(self) -> None:
        """Validate model after initialization."""
        self.validate()
    
    def validate(self) -> None:
        """Validate model consistency.
        
        Raises:
            ModelValidationError: If model is inconsistent
        """
        # RESOLVED TODO: Add validation for model consistency
        # Check all states in relations exist
        all_states = set(self.states)
        for rel_name, pairs in self.relations.items():
            for s1, s2 in pairs:
                if s1 not in all_states or s2 not in all_states:
                    raise ModelValidationError(
                        f"Invalid state in relation {rel_name}: ({s1}, {s2})",
                        context={'valid_states': list(all_states)}
                    )
        
        # Check proposition states are valid
        for state in self.propositions:
            if state not in all_states:
                raise ModelValidationError(
                    f"Invalid state in propositions: {state}"
                )
    
    def minimize(self) -> 'SemanticModel':
        """Minimize model by removing unreachable states.
        
        Returns:
            Minimized semantic model
        """
        # RESOLVED TODO: Implement model minimization
        reachable = self._find_reachable_states()
        
        if len(reachable) == len(self.states):
            return self  # Already minimal
        
        # Filter to reachable states
        new_states = [s for s in self.states if s in reachable]
        new_relations = {}
        for rel_name, pairs in self.relations.items():
            new_relations[rel_name] = [
                (s1, s2) for s1, s2 in pairs 
                if s1 in reachable and s2 in reachable
            ]
        new_propositions = {
            s: props for s, props in self.propositions.items()
            if s in reachable
        }
        
        return SemanticModel(
            states=new_states,
            relations=new_relations,
            propositions=new_propositions,
            metadata={**self.metadata, 'minimized': True}
        )
    
    def _find_reachable_states(
        self,
        start: Optional[StateId] = None
    ) -> Set[StateId]:
        """Find all reachable states from start."""
        if not self.states:
            return set()
        
        if start is None:
            start = self.states[0]
        
        reachable: Set[StateId] = {start}
        queue: List[StateId] = [start]
        
        while queue:
            current = queue.pop(0)
            for rel_pairs in self.relations.values():
                for s1, s2 in rel_pairs:
                    if s1 == current and s2 not in reachable:
                        reachable.add(s2)
                        queue.append(s2)
        
        return reachable
    
    def get_successors(
        self,
        state: StateId,
        relation: RelationName
    ) -> List[StateId]:
        """Get successor states via relation."""
        ...
```

### Day 6: Testing and Final Validation

#### Verify Type Coverage
```python
# scripts/check_models_types.py
import inspect
from model_checker import models

total_functions = 0
typed_functions = 0

for module_name in ['model_variable', 'model_builder', 
                    'model_extractor', 'semantic_model']:
    module = getattr(models, module_name)
    for name, func in inspect.getmembers(module, inspect.isfunction):
        if not name.startswith('_'):
            total_functions += 1
            if hasattr(func, '__annotations__'):
                typed_functions += 1

print(f"Type coverage: {typed_functions}/{total_functions} "
      f"({100*typed_functions/total_functions:.1f}%)")
```

#### Test TODO Resolutions
```python
# tests/test_semantic_model.py
def test_model_validation():
    """Test model validation catches inconsistencies."""
    with pytest.raises(ModelValidationError):
        SemanticModel(
            states=[1, 2],
            relations={'R': [(1, 3)]},  # State 3 doesn't exist
            propositions={1: {'p': True}}
        )

def test_model_minimization():
    """Test model minimization removes unreachable states."""
    model = SemanticModel(
        states=[1, 2, 3, 4],
        relations={'R': [(1, 2), (2, 3)]},  # 4 is unreachable
        propositions={i: {'p': True} for i in [1, 2, 3, 4]}
    )
    
    minimized = model.minimize()
    assert len(minimized.states) == 3
    assert 4 not in minimized.states
```

## Success Metrics

### Required Outcomes
- Type hints: 33/134 → 134/134 functions (100%)
- TODO items: 2 → 0
- Test coverage: Maintain 2.00 ratio
- Compliance score: 73/100 → 90/100

### Quality Improvements
- Full IDE autocomplete for model operations
- Validated model consistency
- Model minimization capability
- Better debugging with typed structures

## Definition of Done

- [ ] All 134 functions have type hints
- [ ] types.py created with model-specific types
- [ ] Both TODO items resolved with implementations
- [ ] Model validation implemented and tested
- [ ] Model minimization implemented and tested
- [ ] mypy passes with --strict
- [ ] All existing tests pass
- [ ] New tests for TODO resolutions
- [ ] Compliance score ≥ 90/100

---

**Related Documents:**
- [Plan 080: Framework Complete Refactor Overview](080_framework_complete_refactor_overview.md)
- [Research 041: Framework Quality and Compliance Audit](../research/041_framework_quality_compliance_audit.md)
- [Code Maintenance Standards](../../../maintenance/README.md)