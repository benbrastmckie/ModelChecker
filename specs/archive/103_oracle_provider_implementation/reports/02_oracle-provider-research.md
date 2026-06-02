# Oracle Provider Implementation Research

- **Task**: 103 - OracleProvider implementation with programmatic pipeline
- **Date**: 2026-06-01
- **Status**: Complete

## Executive Summary

All pipeline components are implemented and available. The implementation requires writing `bimodal_logic/provider.py` to wire together already-completed pieces: `json_to_prefix()` (task 102), `Sentence.from_prefix()` (task 102), `fold_formula()` (task 112), `BimodalSemantics`, `BimodalStructure`, `ModelConstraints`, `Syntax`, `isolated_z3_context()`, and `is_true()`. The entry point is already registered in `pyproject.toml`. The core challenge is the serialization layer (SimpleCountermodel + StructuredCountermodel) and the ternary task_rel extraction loop.

---

## 1. Codebase Survey: Pipeline Components

### 1.1 Translation Layer (Task 102)

**File**: `/home/benjamin/Projects/ModelChecker/code/src/bimodal_logic/translation.py`

Key functions:

```python
def json_to_prefix(formula_json: dict) -> list:
    """Convert JSON formula dict to ModelChecker prefix list.
    Supports all 17 JSON tags (6 primitive + 11 enriched).
    Raises ValueError for unknown tags."""

def temporal_depth(formula_json: dict) -> int:
    """Compute temporal nesting depth. Returns max(d+2,3) guidance for M."""

def prefix_to_infix(prefix_list: list) -> str:
    """Convert prefix list to infix string for Syntax constructor."""

def unfold_formula(formula_json: dict) -> dict:
    """Expand all enriched tags to 6 primitive tags."""

def fold_formula(formula_json: dict) -> dict:
    """Greedily fold primitive patterns into enriched tags (outside-in)."""

def normalize_formula(formula_json: dict, level: int) -> dict:
    """Fold to specified enriched level (0-3)."""
```

All 6 functions are exported from `bimodal_logic/__init__.py`.

**Operator symbol mappings** (for understanding prefix output):
- `atom` → `["p"]` (name)
- `bot` → `["\\bot"]`, `top` → `["\\top"]`
- `neg` → `["\\neg", arg]`, `box` → `["\\Box", child]`
- `imp` → `["\\rightarrow", left, right]`
- `untl` → `["\\Until", event, guard]`, `snce` → `["\\Since", event, guard]`
- `diamond` → `["\\Diamond", arg]`
- `next` → `["\\next", arg]`, `prev` → `["\\prev", arg]`
- `some_future` → `["\\future", arg]`, `some_past` → `["\\past", arg]`
- `all_future` → `["\\Future", arg]`, `all_past` → `["\\Past", arg]`
- `and` → `["\\wedge", left, right]`, `or` → `["\\vee", left, right]`

### 1.2 Sentence.from_prefix (Task 102)

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/syntactic/sentence.py`  
**Line**: 427

```python
@classmethod
def from_prefix(cls, prefix_list: 'PrefixList') -> 'Sentence':
    """Create a Sentence directly from a prefix list, bypassing the infix parser.
    
    Returns Sentence with: prefix_sentence, name, complexity, original_operator,
    original_arguments set. arguments, operator, sentence_letter, proposition = None.
    """
```

This is a clean bypass of the infix parser. The returned `Sentence` needs `update_types()` and `update_objects()` called on it (which happens via `Syntax.initialize_sentences()` if using the Syntax path, or via `ModelConstraints.instantiate()` if using programmatic path).

**Important**: The task description says `Sentence.from_prefix() → BimodalSemantics(N, M) → Syntax(operators, [sentence])`. But looking at the actual Syntax class, it only accepts infix strings, not Sentence objects. The established pattern (seen in `TestJsonToZ3Pipeline` and `test_boundary_regression.py`) is:
```python
prefix = json_to_prefix(formula_json)
infix = prefix_to_infix(prefix)   # convert prefix to infix string
syntax = Syntax([infix], [], bimodal_operators)  # Syntax takes infix strings
```

`Sentence.from_prefix` is useful for direct Sentence construction but the pipeline in practice goes through `prefix_to_infix` → `Syntax`.

### 1.3 fold_formula (Task 112)

**File**: `/home/benjamin/Projects/ModelChecker/code/src/bimodal_logic/translation.py`  
**Line**: 554

```python
def fold_formula(formula_json: dict) -> dict:
    """Greedily fold primitive patterns into enriched tags using outside-in matching.
    
    Level 3 before Level 2 before Level 1. Returns enriched representation."""
```

Used to compute `formula_folded_json` in oracle output.

### 1.4 BimodalSemantics

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/semantic.py`  
**Line**: 49

```python
class BimodalSemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 2, 'M': 2, 'contingent': False, 'disjoint': False,
        'max_time': 1, 'expectation': True, 'iterate': 1, 'solver': 'z3',
    }
    
    def __init__(self, settings):
        """Takes settings dict. Calls define_sorts(), define_primitives(), 
        build_frame_constraints(), define_invalidity()."""
```

Key attributes after init:
- `self.N` — bitvec size (number of atom bits)
- `self.M` — time bound parameter
- `self.task_rel` — Z3 Function(WorldStateSort, IntSort, WorldStateSort, BoolSort)
- `self.truth_condition` — Z3 Function(WorldStateSort, AtomSort, BoolSort)
- `self.main_world = 0`, `self.main_time = z3.IntVal(0)`
- `self.main_point = {"world": 0, "time": z3.IntVal(0)}`
- `self.frame_constraints` — list of Z3 constraints

Frame axioms are in `build_frame_constraints()` (line 488). The 9 active constraints enforce: valid_main_world, valid_main_time, enumeration, convex_world_ordering, world_interval, lawful, nullity_identity, converse, forward_comp.

### 1.5 BimodalStructure

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/semantic.py`  
**Line**: 2342

```python
class BimodalStructure(ModelDefaults):
    def __init__(self, model_constraints, max_time=1):
        """IMPORTANT: second param is named max_time but called with settings dict.
        run_test() and other callers pass the full settings dict as second arg."""
```

**Critical**: BimodalStructure calls `super().__init__(model_constraints, max_time)` which maps to `ModelDefaults.__init__(model_constraints, settings)`. So the second parameter, despite being named `max_time`, actually receives the `settings` dict. Callers pass the settings dict (not just max_time).

After `__init__` completes (if SAT):
- `structure.z3_model_status` — True if satisfiable
- `structure.z3_model` — Z3 model object
- `structure.timeout` — True if timed out
- `structure.world_histories` — `{world_id: {time: bitvec_state}}`
- `structure.world_arrays` — `{world_id: Z3 array}`
- `structure.time_shift_relations` — `{source_id: {shift: target_id}}`
- `structure.main_world = 0`
- `structure.main_time` — evaluated main time (int, usually 0)

### 1.6 ModelConstraints

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/models/constraints.py`  
**Line**: 19

```python
class ModelConstraints:
    def __init__(
        self,
        settings: 'Settings',
        syntax: 'Syntax',
        semantics: 'Semantics',
        proposition_class: Type['PropositionDefaults'],
    ) -> None:
```

Builds `all_constraints` (frame + model + premise + conclusion constraints). The oracle uses "no premises, single conclusion = negation of formula to test."

### 1.7 Syntax

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/syntactic/syntax.py`  
**Line**: 19

```python
class Syntax:
    def __init__(
        self,
        infix_premises: List[FormulaString],    # e.g., []
        infix_conclusions: List[FormulaString], # e.g., [infix_string]
        operator_collection: OperatorCollection,
    ) -> None:
```

Takes infix strings. The programmatic pipeline converts JSON → prefix → infix → Syntax.

### 1.8 BimodalProposition

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/semantic.py`  
**Line**: 2033

Used as `proposition_class` in ModelConstraints. Provides `proposition_constraints()` class method and `find_extension()` instance method.

### 1.9 bimodal_operators

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/operators.py`  
**Import**: `from model_checker.theory_lib.bimodal.operators import bimodal_operators`

`OperatorCollection` containing all bimodal operators.

### 1.10 extract_model_elements

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/semantic.py`  
**Line**: 1707

```python
def extract_model_elements(self, z3_model):
    """Returns:
        Tuple: (world_histories, main_world_history, world_arrays, time_shift_relations)
        - world_histories: {world_id (int): {time (int): bitvec_state}}
        - main_world_history: {time: bitvec_state} for world 0
        - world_arrays: {world_id (int): z3_array}
        - time_shift_relations: {source_id: {shift: target_id}}
    """
```

**Note**: Called automatically in `BimodalStructure.__init__()` — results are stored on `structure.world_histories`, etc. The oracle does NOT need to call this directly; it reads from the structure attributes.

### 1.11 Z3 Context Isolation

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/utils/context.py`  
**Line**: 20

```python
@contextmanager
def isolated_z3_context():
    """Swaps z3.z3._main_ctx to fresh Context(), clears AtomSort cache.
    
    Import: from model_checker.utils.context import isolated_z3_context
    Also available: from model_checker.utils import isolated_z3_context
    """
```

Pattern for oracle use:
```python
with isolated_z3_context():
    semantics = BimodalSemantics(settings)
    # ... full pipeline ...
    structure = BimodalStructure(model_constraints, settings)
```

### 1.12 is_true

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/solver/__init__.py`  
**Import**: `from model_checker.solver import is_true, is_false`

Used for evaluating Z3 model expressions:
```python
from model_checker.solver import is_true
is_true(z3_model.eval(semantics.task_rel(s, d, u)))
```

---

## 2. Existing Pipeline Usage Pattern

The canonical pattern (from `test_bimodal.py`, `test_boundary_regression.py`):

```python
from model_checker import ModelConstraints, Syntax, run_test
from model_checker.theory_lib.bimodal import (
    BimodalStructure, BimodalProposition, BimodalSemantics, bimodal_operators
)
from model_checker.utils.context import isolated_z3_context

with isolated_z3_context():
    settings = {'N': 2, 'M': 3, 'contingent': False, 'disjoint': False,
                'max_time': 5, 'expectation': True}  # expectation=True means SAT expected
    syntax = Syntax(premises_list, conclusions_list, bimodal_operators)
    semantics = BimodalSemantics(settings)
    model_constraints = ModelConstraints(settings, syntax, semantics, BimodalProposition)
    structure = BimodalStructure(model_constraints, settings)
    
    # After construction:
    # structure.z3_model_status == True means SAT (countermodel found)
    # structure.z3_model_status == False means UNSAT (formula is valid)
    # structure.timeout == True means timed out
```

**Oracle pipeline** (finding a countermodel for formula_json):

```python
def find_countermodel(formula_json, frame_class, timeout_ms):
    if frame_class not in self.supported_frame_classes:
        return None
    
    depth = temporal_depth(formula_json)
    M = max(depth + 2, 3)
    timeout_sec = timeout_ms / 1000.0
    
    # Compute folded representation for output
    formula_folded = fold_formula(formula_json)
    
    # Build infix string for Syntax (standard pipeline)
    prefix = json_to_prefix(formula_json)
    infix = prefix_to_infix(prefix)
    
    settings = {
        'N': 2, 'M': M,
        'contingent': False, 'disjoint': False,
        'max_time': timeout_sec,
        'expectation': True,   # We're looking for a countermodel
        'solver': 'z3',
    }
    
    self._semantics = None  # Reset between calls (ADR Decision 9)
    
    with isolated_z3_context():
        semantics = BimodalSemantics(settings)
        # Oracle pipeline: empty premises, conclusion = negation of formula
        syntax = Syntax([], [infix], bimodal_operators)
        model_constraints = ModelConstraints(settings, syntax, semantics, BimodalProposition)
        structure = BimodalStructure(model_constraints, settings)
        
        if structure.timeout or not structure.z3_model_status:
            return None
        
        # Extract and serialize countermodel
        result = _serialize_countermodel(structure, semantics, formula_json,
                                         formula_folded, depth, M)
    
    return result
```

**Semantics note**: "Countermodel for formula F" means: `F` is FALSE at the evaluation point. The oracle should check if `F` itself has a countermodel (i.e., if `¬F` is satisfiable — `F` is not a tautology). With `expectation=True` and the formula as the sole conclusion, the system finds a model where the conclusion is FALSE. This is the standard "invalidity" pipeline.

---

## 3. Ternary task_rel Extraction (ADR Decision 6)

From `specs/106_architecture_review_refactor/reports/04_architectural-decisions.md`, lines 150-162:

```python
task_triples = []
N = semantics.N
M = semantics.M
for s in range(2**N):
    for d in range(-(M-1), M):
        for u in range(2**N):
            if is_true(z3_model.eval(semantics.task_rel(s, d, u))):
                task_triples.append({"source": s, "duration": d, "target": u})
```

Complexity: O(2^(2N) * (2M-1)) — 80 evaluations for N=2, M=3.

Note: The semantics already has similar code in `inject_z3_model_values()` (line 1655-1674) for iteration — the pattern is identical. The `task_rel` function takes (BitVec or int, int, BitVec or int) arguments. With Python integers in the range `[0, 2^N)`, Z3 coerces them to the correct sort.

---

## 4. Countermodel Serialization

### 4.1 SimpleCountermodel

Requires `trueAtoms` and `falseAtoms` — lists of atoms evaluated at the main evaluation point (world=0, time=0).

**How to extract atoms**: After `BimodalStructure.__init__()`, the `structure.semantics.truth_condition` function holds the Z3 function mapping `(WorldState, AtomSort) → Bool`. To get atom truth at the main point:

```python
# Get world state at main point
main_world_id = 0
main_time = 0
world_hist = structure.world_histories.get(main_world_id, {})
main_state = world_hist.get(main_time)

# For each sentence letter (atom):
# - Evaluate truth_condition(main_state, atom_z3_const) on z3_model
# - is_true(...) gives the boolean
```

The sentence letters come from `model_constraints.sentence_letters` (list of Z3 Const objects).

### 4.2 StructuredCountermodel

Required fields per ADR Decision 6 and the pipeline diagram:

```python
{
    "trueAtoms": [{"name": "p"}, ...],
    "falseAtoms": [{"name": "q"}, ...],
    "formula": formula_json,              # original formula
    "world_histories": [...],             # {world_id, times: {t: state_label}}
    "task_relation": [                    # ternary triples
        {"source": s, "duration": d, "target": u}, ...
    ],
    "truth_valuation": {...},             # atom truth at all world/time points
    "evaluation_world": 0,
    "evaluation_time": 0,
    "world_count": int,
    "time_bound": M,
    "temporal_depth": int,
    "boundary_safe": bool,               # M > temporal_depth + 1
    "semantics_version": "...",
    "formula_folded_json": formula_folded,  # fold_formula(formula_json)
}
```

**world_histories format**: `structure.world_histories` is `{world_id (int): {time (int): bitvec_state}}`. The bitvec_state needs to be converted to a readable label (e.g., integer or bit string).

**truth_valuation**: For each atom `a`, for each world `w`, for each time `t`:
```python
state_at_t = world_histories[w][t]
truth = is_true(z3_model.eval(semantics.truth_condition(state_at_t, atom_const)))
```

---

## 5. Provider Properties

### 5.1 provider_id

`provider_id = "bmlogic_z3_base_v1"` (from task description)

### 5.2 provider_version

Semver string, e.g., `"0.1.0"` — should come from `bimodal_logic.__version__` if defined, or be hardcoded.

### 5.3 semantics_version

Pinned to BimodalLogic git tag or release. Since there's no live BimodalLogic dependency, this should be a constant string (e.g., `"bimodal-logic-v0.1.0"` or a hash).

### 5.4 supported_frame_classes

`frozenset({"Base"})` — already set in the stub at line 131.

### 5.5 capabilities

A dict describing oracle capabilities. Example:
```python
capabilities = {
    "max_N": 4,
    "max_M": 8,
    "supports_enriched_tags": True,
    "z3_timeout_configurable": True,
}
```

---

## 6. validate_self Method

```python
def validate_self(self, spot_check_formulas: list) -> bool:
    """Find countermodels for all provided known-invalid formulas.
    
    Returns True if all formulas have countermodels found, False otherwise.
    """
    for formula_json in spot_check_formulas:
        result = self.find_countermodel(formula_json, "Base", timeout_ms=5000)
        if result is None:
            return False
    return True
```

---

## 7. Entry Point

**File**: `/home/benjamin/Projects/ModelChecker/code/pyproject.toml`  
**Lines**: 36-37

```toml
[project.entry-points."bimodal_harness.oracle_providers"]
z3_base = "bimodal_logic.provider:Z3OracleProvider"
```

This is already registered. Task 103 does NOT need to modify pyproject.toml (it's done).

---

## 8. The 43-Example Test Suite

**File**: `/home/benjamin/Projects/ModelChecker/code/src/model_checker/theory_lib/bimodal/tests/unit/test_boundary_regression.py`  
**Class**: `TestExampleRegression` (line 431)

The regression suite runs 43 active examples (52 total minus 9 known-timeout exclusions). The oracle's `find_countermodel()` pipeline must produce identical SAT/UNSAT results for these 43 examples.

The test uses `run_test()` with the existing pipeline. Task 103 needs a separate `test_oracle_interface.py` that runs the same 43 formulas through the new `Z3OracleProvider.find_countermodel()` and verifies identical SAT/UNSAT.

**Key challenge**: The existing examples use infix formulas (premises + conclusions). The oracle uses JSON formula. The examples need to be converted to JSON format to test through the oracle. The oracle pipeline uses "no premises, conclusion = formula" (testing invalidity). The existing examples have premises, so conversion requires care.

---

## 9. Gaps and Critical Findings

### 9.1 Syntax Cannot Accept Sentence Objects

`Syntax.__init__` accepts only infix strings, not `Sentence` objects. The task description says "json_to_prefix() → Sentence.from_prefix() → BimodalSemantics(N, M) → Syntax(operators, [sentence])" — but this is not accurate about how Syntax works. The working pipeline is:

```python
prefix = json_to_prefix(formula_json)
infix = prefix_to_infix(prefix)
syntax = Syntax([], [infix], bimodal_operators)  # Uses infix strings
```

`Sentence.from_prefix()` is useful for direct Sentence construction if needed but is not part of the standard Syntax construction path.

### 9.2 BimodalStructure Second Parameter Naming Confusion

`BimodalStructure.__init__(model_constraints, max_time=1)` is misleading — the parameter is named `max_time` but callers pass the full `settings` dict. The parent `ModelDefaults.__init__` expects `settings` as the second parameter and calls `settings.get("max_time", 5)`. This is working correctly but must be understood.

### 9.3 AtomSort Cache Must Be Reset in isolated_z3_context

`isolated_z3_context()` already handles AtomSort cache reset (calls `reset_atom_sort()` before yielding and after restoring). No extra action needed from the oracle implementation.

### 9.4 Bitvec State Representation in world_histories

`world_histories` values are Z3 bitvec objects. They need to be converted to Python integers for serialization. Use `z3_model.eval(state).as_long()` or similar. The existing `bitvec_to_worldstate()` utility may help.

### 9.5 truth_valuation Completeness

Building a full `truth_valuation` for all atoms across all world/time points is O(|atoms| * |worlds| * |times|). For N=2, M=3, this is 2 atoms * ~3 worlds * 5 time points = ~30 evaluations. Manageable.

### 9.6 oracle_output formula_folded_json Requirement

The task requires `formula_folded_json` = `fold_formula(formula_json)`. This converts primitive formula input to enriched representation. For formulas already using enriched tags as input (e.g., `{"tag": "neg", ...}`), `fold_formula` is idempotent (returns the same enriched form). For primitive-only inputs, it computes the enriched form.

---

## 10. Package Structure

### Current bimodal_logic package
```
code/src/bimodal_logic/
├── __init__.py         # Exports Z3OracleProvider, json_to_prefix, temporal_depth, 
│                       #   prefix_to_infix, unfold_formula, fold_formula, normalize_formula
├── provider.py         # STUB — needs full implementation (task 103)
├── translation.py      # COMPLETE — json_to_prefix, temporal_depth, fold_formula etc.
└── serialization.py    # STUB — empty placeholder
```

### Files to implement in task 103
1. `bimodal_logic/provider.py` — full `Z3OracleProvider` class
2. `bimodal_logic/serialization.py` — countermodel serialization helpers

---

## 11. Recommended Implementation Approach

### Phase 1: Write failing tests
Create `code/src/model_checker/theory_lib/bimodal/tests/unit/test_oracle_provider.py`:
- Test provider properties (provider_id, supported_frame_classes, capabilities)
- Test find_countermodel returns None for unsupported frame_class
- Test find_countermodel returns None for UNSAT formula
- Test find_countermodel returns dict with required keys for SAT formula
- Test formula_folded_json is present and valid
- Test boundary_safe flag is True for simple formulas at M=max(depth+2,3)
- Test ternary task_relation triples format

### Phase 2: Implement serialization helpers in serialization.py
```python
def extract_true_false_atoms(z3_model, semantics, model_constraints, structure) -> tuple:
    """Extract trueAtoms and falseAtoms at main evaluation point."""

def extract_task_triples(z3_model, semantics) -> list:
    """Iterate all (s, d, u) triples and evaluate semantics.task_rel."""

def extract_truth_valuation(z3_model, semantics, model_constraints, structure) -> dict:
    """Build {atom_name: {world_id: {time: bool}}} mapping."""

def serialize_world_histories(structure) -> list:
    """Convert structure.world_histories to serializable list of dicts."""

def serialize_countermodel(z3_model, semantics, model_constraints, structure,
                           formula_json, formula_folded, depth, M, semantics_version) -> dict:
    """Assemble complete countermodel dict with SimpleCountermodel + StructuredCountermodel."""
```

### Phase 3: Implement Z3OracleProvider in provider.py
Full `find_countermodel()` with:
- Frame class check
- temporal_depth + M computation
- fold_formula for formula_folded_json
- isolated_z3_context wrapping
- Fresh BimodalSemantics per call
- Pipeline: prefix → infix → Syntax → ModelConstraints → BimodalStructure
- Result extraction via serialization helpers
- None on UNSAT/timeout

### Phase 4: Z3 isolation test (100 sequential calls)
Add test that runs `find_countermodel()` 100 times in sequence on a simple formula and verifies no state leakage (consistent results, no memory growth).

### Phase 5: 43-example SAT/UNSAT regression
Add `test_oracle_43_examples.py` that converts the 43 examples from `examples.py` to oracle format and verifies identical results through `find_countermodel()`.

---

## 12. Key File Paths Reference

| Component | File | Line |
|-----------|------|------|
| Provider stub | `code/src/bimodal_logic/provider.py` | 116 |
| Translation functions | `code/src/bimodal_logic/translation.py` | — |
| BimodalSemantics | `code/src/model_checker/theory_lib/bimodal/semantic.py` | 49 |
| BimodalStructure | `code/src/model_checker/theory_lib/bimodal/semantic.py` | 2342 |
| BimodalProposition | `code/src/model_checker/theory_lib/bimodal/semantic.py` | 2033 |
| extract_model_elements | `code/src/model_checker/theory_lib/bimodal/semantic.py` | 1707 |
| task_rel definition | `code/src/model_checker/theory_lib/bimodal/semantic.py` | 179 |
| ModelConstraints | `code/src/model_checker/models/constraints.py` | 19 |
| Syntax | `code/src/model_checker/syntactic/syntax.py` | 19 |
| Sentence.from_prefix | `code/src/model_checker/syntactic/sentence.py` | 427 |
| OperatorCollection | `code/src/model_checker/syntactic/collection.py` | 16 |
| isolated_z3_context | `code/src/model_checker/utils/context.py` | 20 |
| is_true | `code/src/model_checker/solver/__init__.py` | — |
| bimodal_operators | `code/src/model_checker/theory_lib/bimodal/operators.py` | — |
| 43-example set | `code/src/model_checker/theory_lib/bimodal/examples.py` | 1272 |
| Regression test | `code/src/model_checker/theory_lib/bimodal/tests/unit/test_boundary_regression.py` | 431 |
| Entry point | `code/pyproject.toml` | 36 |
| ADR Document | `specs/106_architecture_review_refactor/reports/04_architectural-decisions.md` | — |
| Prior research | `specs/103_oracle_provider_implementation/reports/01_tiered-oracle-architecture.md` | — |

---

## 13. Summary of Blockers / Risks

1. **No blockers**: All dependency tasks (101, 102, 112) are completed. All pipeline components exist.

2. **BimodalStructure signature confusion**: The second parameter is named `max_time` but receives the settings dict. Implementation must pass `settings` dict as second arg to `BimodalStructure(model_constraints, settings)`.

3. **Bitvec state serialization**: World state values in `world_histories` are Z3 bitvec objects. Need `.as_long()` or evaluation to get Python integers.

4. **Sentence.from_prefix not needed in hot path**: The task description mentions it, but the standard pipeline uses `prefix_to_infix` + `Syntax(infix)`. `Sentence.from_prefix` is available but not the primary path.

5. **truth_condition AtomSort**: The `truth_condition` Z3 function uses `AtomSort`. Sentence letters are retrieved as Z3 Const objects from `model_constraints.sentence_letters`. The formula's atoms must match what's stored in the AtomSort. Since all this happens within a single `isolated_z3_context()` block, the sort is consistent.

6. **semantics_version**: Must be a hardcoded string since there's no live BimodalLogic dependency. Suggest using the `bimodal_logic.__version__` constant as the `semantics_version` value.
