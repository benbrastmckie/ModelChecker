# Bimodal Logic Architecture

## Overview

The Bimodal theory implements temporal-modal logic through a modular architecture that extends the ModelChecker framework. This document provides a comprehensive technical overview of the theory's design, implementation patterns, and integration with the broader system for reasoning about both time and possibility.

## Table of Contents

- [Core Components](#core-components)
- [Semantic Framework](#semantic-framework)
- [Operator Implementation](#operator-implementation)
- [Model Construction](#model-construction)
- [Integration Strategy](#integration-strategy)
- [Performance Considerations](#performance-considerations)
- [Extension Points](#extension-points)
- [Witness Predicate Design History](#witness-predicate-design-history)

## Core Components

### Theory Structure

```
bimodal/
├── __init__.py          # Public API and theory configuration
├── semantic/             # Package (not a bare semantic.py module), re-export-only __init__.py
│   ├── core.py           # BimodalSemantics implementation
│   ├── model.py           # BimodalStructure
│   ├── proposition.py     # BimodalProposition
│   ├── witness_registry.py
│   └── witness_constraints.py
├── operators.py          # Operator collection with temporal-modal operators
├── examples.py           # Comprehensive example collection
├── iterate.py            # Model iteration support
├── docs/                 # Documentation (this file and others)
└── tests/                # Unit and integration tests
```

Note: bimodal does not currently ship a `notebooks/` directory (exclusion and imposition do); this
is a recorded, deliberate gap tracked in `specs/ROADMAP.md`, not an oversight in this listing.

### Class Hierarchy

```python
# Core semantic framework
BimodalSemantics(SemanticDefaults)
├── Inherits base truthmaker semantics
├── Adds temporal-modal evaluation methods
└── Configures world-history semantics

# Model and proposition structures
BimodalStructure(ModelStructure)
├── Extends base model structure
├── Adds temporal dimension (time points)
└── Manages world histories

BimodalProposition(Proposition)
├── Extends base proposition handling
└── Supports temporal-modal formulas

# Operator collection
bimodal_operators: OperatorCollection
├── Extensional operators (¬, ∧, ∨, →, ↔)
├── Modal operators (□, ◇)
├── Temporal operators (⏵, ⏴)
└── Extremal operators (⊤, ⊥)
```

## Semantic Framework

### World History Semantics

The theory implements temporal-modal logic using world histories:

#### Time Points and Worlds
```python
class BimodalSemantics(SemanticDefaults):
    """Implements world-history semantics for temporal-modal logic."""
    
    def __init__(self, settings):
        super().__init__(settings)
        self.time_points = range(settings.get('M', 1))
        self.world_histories = self._generate_world_histories()
    
    def evaluate_at_point(self, world, time, formula):
        """Evaluate formula at specific (world, time) point."""
        return self._evaluate_temporal_modal(world, time, formula)
```

#### Key Semantic Operations

1. **Temporal Evaluation**: `evaluate_temporal(world, time, formula)`
   - Evaluates formulas relative to specific time points
   - Handles temporal operator progression

2. **Modal Evaluation**: `evaluate_modal(world, time, formula)`
   - Evaluates modal formulas at specific (world, time) points
   - Uses accessibility relations between worlds

3. **World History Management**: `get_world_histories()`
   - Manages sequences of worlds across time
   - Ensures temporal continuity

4. **Accessibility Relations**: `accessible_worlds(world, time)`
   - Defines modal accessibility at each time point
   - Supports temporal evolution of modal structure

### Truth Conditions

#### Extensional Operators
Standard truth-functional evaluation at each (world, time) point:

```python
# Conjunction: A ∧ B
def conjunction_semantic_clause(self, sentence):
    """A ∧ B is true when both A and B are true at the evaluation point."""
    world, time, args = sentence['world'], sentence['time'], sentence['args']
    A, B = args[0], args[1]
    
    return z3.And(
        self.evaluate_at_point(world, time, A),
        self.evaluate_at_point(world, time, B)
    )
```

#### Modal Operators
Modal evaluation considers accessible worlds at current time:

```python
def necessity_semantic_clause(self, sentence):
    """□A: A is necessary (true at all accessible worlds)."""
    world, time, args = sentence['world'], sentence['time'], sentence['args']
    A = args[0]
    
    # A is necessary if true at all accessible worlds at current time
    accessible = self.accessible_worlds(world, time)
    return z3.And([
        self.evaluate_at_point(w, time, A)
        for w in accessible
    ])

def possibility_semantic_clause(self, sentence):
    """◇A: A is possible (true at some accessible world)."""
    world, time, args = sentence['world'], sentence['time'], sentence['args']
    A = args[0]
    
    # A is possible if true at some accessible world at current time
    accessible = self.accessible_worlds(world, time)
    return z3.Or([
        self.evaluate_at_point(w, time, A)
        for w in accessible
    ])
```

#### Temporal Operators
Temporal evaluation moves along time dimension within world histories:

```python
def future_semantic_clause(self, sentence):
    """⏵A: A will be true (true at next time point)."""
    world, time, args = sentence['world'], sentence['time'], sentence['args']
    A = args[0]
    
    # Check bounds
    if time + 1 >= len(self.time_points):
        return z3.BoolVal(False)
    
    # A is true at next time point in same world
    return self.evaluate_at_point(world, time + 1, A)

def past_semantic_clause(self, sentence):
    """⏴A: A was true (true at previous time point)."""
    world, time, args = sentence['world'], sentence['time'], sentence['args']
    A = args[0]
    
    # Check bounds
    if time - 1 < 0:
        return z3.BoolVal(False)
    
    # A was true at previous time point in same world
    return self.evaluate_at_point(world, time - 1, A)
```

## Operator Implementation

### Operator Collection Structure

```python
# In operators.py
from model_checker.syntactic import OperatorCollection, Operator

# Extensional operators (standard logical operators)
class Negation(Operator):
    def __init__(self):
        super().__init__("\\neg", 1)
    
    def semantic_clause(self, sentence):
        # Classical negation at evaluation point
        pass

# Modal operators
class Necessity(Operator):
    def __init__(self):
        super().__init__("\\Box", 1)
    
    def semantic_clause(self, sentence):
        # Modal necessity across accessible worlds
        pass

class Possibility(Operator):
    def __init__(self):
        super().__init__("\\Diamond", 1)
    
    def semantic_clause(self, sentence):
        # Modal possibility across accessible worlds
        pass

# Temporal operators
class Future(Operator):
    def __init__(self):
        super().__init__("\\future", 1)
    
    def semantic_clause(self, sentence):
        # Temporal progression to next time point
        pass

class Past(Operator):
    def __init__(self):
        super().__init__("\\past", 1)
    
    def semantic_clause(self, sentence):
        # Temporal regression to previous time point
        pass

# Create operator collection
bimodal_operators = OperatorCollection({
    # Extensional
    "\\neg": Negation(),
    "\\wedge": Conjunction(),
    "\\vee": Disjunction(),
    "\\to": Conditional(),
    "\\leftrightarrow": Biconditional(),
    "\\top": Top(),
    "\\bot": Bottom(),
    
    # Modal
    "\\Box": Necessity(),
    "\\Diamond": Possibility(),
    
    # Temporal
    "\\future": Future(),
    "\\past": Past(),
})
```

### Operator Design Patterns

#### Temporal-Modal Interaction Pattern
Operators that combine temporal and modal reasoning:

```python
def temporal_modal_operator(self, sentence):
    """Pattern for operators combining temporal and modal evaluation."""
    world, time, args = sentence['world'], sentence['time'], sentence['args']
    
    # First apply temporal operation
    temporal_result = self.apply_temporal_operation(world, time, args)
    
    # Then apply modal operation to result
    modal_result = self.apply_modal_operation(temporal_result)
    
    return modal_result
```

#### World History Pattern
Many operators must consider world histories:

```python
def evaluate_across_history(self, world_history, formula):
    """Common pattern for evaluating across time points."""
    return z3.And([
        self.evaluate_at_point(world_history[t], t, formula)
        for t in self.time_points
    ])
```

## Model Construction

### Integration with BuildExample

The bimodal theory integrates seamlessly with ModelChecker's BuildExample:

```python
from model_checker import BuildExample
from model_checker.theory_lib.bimodal import get_theory

# Standard usage pattern
theory = get_theory()
example_case = [premises, conclusions, settings]
example = BuildExample("temporal_modal_test", theory, example_case)
result = example.check_result()
```

### Model Structure Implementation

The theory uses specialized model structures for temporal-modal reasoning:

```python
# In __init__.py
def get_theory(config=None):
    return {
        "semantics": BimodalSemantics,
        "proposition": BimodalProposition,
        "model": BimodalStructure,
        "operators": bimodal_operators
    }
```

### Constraint Generation

The theory generates Z3 constraints that capture temporal-modal semantics:

```python
class BimodalSemantics(SemanticDefaults):
    def generate_frame_constraints(self):
        """Generate constraints specific to temporal-modal semantics."""
        constraints = super().generate_frame_constraints()
        
        # Add temporal constraints
        constraints.extend(self._temporal_constraints())
        
        # Add modal constraints
        constraints.extend(self._modal_constraints())
        
        # Add temporal-modal interaction constraints
        constraints.extend(self._temporal_modal_constraints())
        
        return constraints
    
    def _temporal_constraints(self):
        """Constraints governing temporal structure."""
        return [
            # Time points are linearly ordered
            # Temporal operators respect boundaries
            # World histories are consistent
        ]
    
    def _modal_constraints(self):
        """Constraints governing modal structure."""
        return [
            # Accessibility relations at each time
            # Modal operator behavior
            # World branching structure
        ]
```

### Frame-Class Axioms

Unlike the illustrative pseudocode above (`generate_frame_constraints`, `_temporal_constraints`,
`_modal_constraints` do not exist in `core.py`), this subsection is a factual reference to
`build_frame_constraints` in
`code/src/model_checker/theory_lib/bimodal/semantic/core.py`, naming its real method names and
line anchors.

The table below records every Z3 constraint that corresponds to a `TaskFrame` axiom in
BimodalLogic's `Frame.lean`/`TaskFrame.lean`, whether it is asserted or free (discharged without a
Z3 constraint), and its citation:

| Constraint | Status | Paper `def:frame` axiom? | Z3 encoding site | Citation |
|---|---|---|---|---|
| `nullity_identity` | **Asserted** | No — the paper's own `lem:nullity` is *derived* (reflexivity only); ModelChecker's iff-form is strictly stronger, an intentional over-strong design choice | `build_nullity_identity_constraint`, `core.py:280` | `TaskFrame.lean:74-75, 108-109` (design-question note); over-sufficient for `cor:occurrence`'s `TaskRel w 0 w` discharge, `Extension.lean:97-99` |
| `converse` | **Asserted** | No — definitional convention on the group structure, not an independent axiom | `build_converse_constraint`, `core.py:305` | `TaskFrame.lean` (`converse` as `AddCommGroup` inverse, not a `def:frame` field) |
| `forward_comp` (Compositionality, `<-` half) | **Asserted** | Yes — half of *Compositionality* | `build_forward_comp_constraint`, `core.py:344` | `Frame.lean:112-114` (`Compositional.compose`) |
| `interpolation` (Compositionality, `->` half) | **Asserted** | Yes — the other half of *Compositionality* | `build_interpolation_constraint`, `core.py` (immediately after `build_forward_comp_constraint`) | `TaskFrame.lean` `Interpolates` predicate; consumed at `Extension/Constraint.lean:43-55, 217-244` |
| `seriality` | **Asserted** | Yes | `build_seriality_constraint`, `core.py` (immediately before `build_interpolation_constraint`) | `TaskFrame.lean` `Serial` predicate; consumed at `Extension/Constraint.lean:43-55` |
| `Limit` | **Free** | Yes | discharged at the sort level, no Z3 assertion needed | `TaskFrame.limit_of_succOrder`, `TaskFrame.lean:730`; hypotheses `[SuccOrder D][NoMaxOrder D]` (Z3 `Int`) and `hnull` (`nullity_identity`, unguarded) |
| `Spherical` | **Free** | Yes | discharged at the sort level, no Z3 assertion needed | `TaskFrame.spherical_of_finite`, `TaskFrame.lean:985`; hypothesis `[Finite W]` (Z3 `WorldStateSort = BitVecSort(N)`) |

**On "asserted" counts**: this is a 7-row, per-constraint table (5 asserted, 2 free). Read against
the paper's own four-axiom family (`{Compositionality, Seriality, Limit, Spherical}`), only **two**
end up asserted, with both new rows added below (Compositionality — complete now that `forward_comp` and
`interpolation` together cover both directions — and Seriality) and two remain free
(Limit, Spherical): a **2 asserted / 2 free** count at the paper-axiom level. The two counts
(5/2 at the Z3-constraint-row level, 2/2 at the paper-axiom level) differ because `nullity_identity`
and `converse` are not independent `def:frame` axioms in their own right, and because
`forward_comp`/`interpolation` are two Z3 rows implementing one paper axiom (Compositionality).
Both counts are recorded here rather than forcing a single number that would misdescribe the table.

**Duration-domain guard (open gap, recorded not resolved)**: every asserted row above is guarded by
`is_valid_duration`, which restricts it to the bounded window `(-M, M)` — `is_valid_duration` is a
*guard*, not a sort restriction (`task_rel`'s duration argument remains Z3 `Int`, i.e. `\Z`,
throughout), so *Limit*/*Spherical* freeness is unaffected by any of the asserted rows' guards. But
the resulting structure a countermodel run actually searches over is a `TaskFrame` restricted to
`(-M, M)`, not literally `thm:extension`'s unbounded `TaskFrame \Z`. This embedding question is an
open gap inherited from the predecessor audit
(`specs/152_audit_bimodal_frame_class_and_verdict_dependence/`) and is load-bearing for future
certification work; it is not resolved by this table or by adding Seriality/Interpolation.

## Integration Strategy

### Theory Comparison Support

The theory supports comparison with other theories through standardized interfaces:

```python
# In examples.py
semantic_theories = {
    "Primary": bimodal_theory,      # Temporal-modal logic
    "Alternative": logos_theory,    # For comparison with hyperintensional logic
}
```

### Component Design Philosophy

The architecture follows a specialized design pattern:

1. **Semantic Core**: Custom BimodalSemantics for temporal-modal behavior
2. **Proposition/Model**: Specialized components for temporal-modal structures  
3. **Operators**: Comprehensive collection covering temporal, modal, and extensional operators
4. **Examples/Tests**: Theory-specific collections demonstrating temporal-modal reasoning

### API Consistency

The theory implements the standard theory interface:

```python
# Required functions for uniform API
def get_theory(config=None):
    """Standard theory configuration interface."""
    
def get_examples():
    """Standard example access interface."""
    
def get_test_examples():
    """Standard test example access interface."""
```

## Performance Considerations

### Computational Complexity

Bimodal semantics introduces significant performance challenges:

1. **State Space Growth**: O(2^(M×N)) for M time points and N propositions
2. **Modal Branching**: Multiple worlds at each time point
3. **Temporal Depth**: Linear growth with number of time points
4. **Constraint Density**: Complex interactions between temporal and modal constraints

### Optimization Strategies

#### Time Point Management
```python
class BimodalSemantics(SemanticDefaults):
    def __init__(self, settings):
        super().__init__(settings)
        # Optimize time point representation
        self.max_time = settings.get('M', 1)
        self._time_cache = {}
        self._world_cache = {}
    
    def get_time_points(self):
        """Cached time point enumeration."""
        if 'times' not in self._time_cache:
            self._time_cache['times'] = list(range(self.max_time))
        return self._time_cache['times']
```

#### World History Optimization
```python
def optimize_world_histories(self):
    """Optimize world history representation."""
    # Use efficient data structures for world sequences
    # Cache temporal transitions
    # Minimize modal branching where possible
    pass
```

### Memory Management

```python
# Efficient constraint generation for temporal-modal logic
def semantic_clause(self, sentence):
    """Generate constraints efficiently for bimodal operators."""
    # Use generators for large time/world spaces
    # Cache expensive modal computations
    # Release intermediate temporal results
    pass
```

## Extension Points

### Adding New Operators

To add a new operator to the bimodal theory:

1. **Create Operator Class**:
```python
class NewTemporalModalOperator(Operator):
    def __init__(self):
        super().__init__("\\newop", arity)
    
    def semantic_clause(self, sentence):
        # Implement semantics using temporal-modal framework
        world, time = sentence['world'], sentence['time']
        # Handle both temporal and modal aspects
        pass
```

2. **Register in Collection**:
```python
bimodal_operators["\\newop"] = NewTemporalModalOperator()
```

3. **Add Tests and Documentation**:
   - Unit tests in `tests/`
   - Examples in `examples.py`
   - Documentation updates

### Extending Semantics

To modify the semantic framework:

```python
class ExtendedBimodalSemantics(BimodalSemantics):
    """Extended version with additional temporal-modal features."""
    
    def __init__(self, settings):
        super().__init__(settings)
        # Add extensions
    
    def custom_temporal_operation(self, world, time, args):
        """New temporal operation."""
        pass
    
    def custom_modal_operation(self, world, time, args):
        """New modal operation."""
        pass
```

### Alternative Temporal-Modal Theories

The architecture supports alternative temporal-modal approaches:

```python
class AlternativeBimodalSemantics(SemanticDefaults):
    """Different approach to temporal-modal semantics."""
    
    def temporal_accessibility(self, world, time):
        """Alternative temporal accessibility relation."""
        # Different temporal structure (branching, circular, etc.)
        pass
    
    def modal_accessibility(self, world, time):
        """Alternative modal accessibility relation."""
        # Different modal structure at each time
        pass
```

## Witness Predicate Design History

This section records how Box's truth and falsity conditions came to be encoded the way they are
today, why an alternative encoding built to solve the same problem is not in the tree, and what
is now known about the non-determinism that alternative was designed to fix.

### Falsity Constraints for Modal Operators

`\Box`'s truth and falsity conditions are implemented directly in `NecessityOperator.true_at()`
and `NecessityOperator.false_at()` (`operators.py`): `true_at()` uses `z3.ForAll` to require the
argument true at every valid world at the evaluation time; `false_at()` is its Z3 dual, using
`z3.Exists` to assert some valid world where the argument is false. Both quantify directly over
`is_world(...)`, with no domain guard on the evaluation time (paper/Lean-aligned semantics).

A separate, older mechanism also exists in the tree: `semantic/witness_constraints.py` defines a
`WitnessConstraintGenerator` class with a `generate_witness_constraints()` method and a
`_witness_constraint_for_falsity()` method, and `semantic/witness_registry.py` defines a
`WitnessRegistry` for tracking per-formula `accessible_world` predicates. `BimodalSemantics`
(`semantic/core.py`) still constructs one of each at initialization. Neither class's
constraint-generating methods are called anywhere in the current truth-evaluation pipeline,
however — `_witness_constraint_for_falsity()` remains the placeholder it has always been (it
docstrings itself as pending "Phase 4 integration" and its body is a bare `pass`). The witness
registry and constraint generator are therefore live but unused scaffolding: instantiated on
every `BimodalSemantics`, referenced by no caller outside their own unit tests. Anyone extending
Box/Diamond's semantics should treat `operators.py`'s direct `ForAll`/`Exists` encoding as the
actual mechanism, not the witness-predicate classes.

### The Quantifier-Free Encoding, and Why It Is Not Used

An alternative encoding was designed, implemented, and validated: instead of `z3.ForAll` over an
uninterpreted `accessible_world` predicate, it enumerated concrete `(world, time)` pairs directly
and asserted the falsity condition against each one via a `generate_witness_constraints_quantifier_free()`
method, gated by a `quantifier_free_witnesses` settings flag (defaulting to enabled). It was
carried through a "make quantifier-free witnesses the default" change and a final validation pass
before development on that line stopped.

This encoding is not present in the current tree, and `bimodal` exposes no `quantifier_free_witnesses`
setting today. It was built specifically to work around observed non-deterministic countermodel
results for `\Box`-containing examples; the diagnosis motivating it attributed that
non-determinism to Z3's `ForAll` quantifier-instantiation heuristics (see next subsection for why
that diagnosis has since been superseded). Once the underlying symptom had a different, much
smaller fix, the quantifier-free encoding's original justification no longer applied, and it was
not carried forward into the `semantic/` subpackage layout the rest of the witness-predicate work
was consolidated into. Reintroducing a quantifier-free encoding should be justified by a fresh,
measured problem — e.g. a specific case where `ForAll`/`Exists` quantification demonstrably
underperforms — not by resurrecting this design on the assumption that its original motivation
still holds.

### Non-Determinism: Diagnosed Causes

Two different root-cause attributions exist in this project's history for the same observed
symptom (`\Box`-countermodel results flipping between success and failure depending on run
order):

1. **Earlier attribution**: non-deterministic behavior in a falsity-constraint implementation was
   attributed to "Z3's ForAll quantifier instantiation heuristics" being inherently
   non-deterministic. This diagnosis motivated designing the quantifier-free encoding described
   above as a way to avoid `ForAll` entirely.
2. **Confirmed root cause**: a process-global bound-variable counter (`_bound_var_counter` in
   `operators.py`) generated the numeric suffix appended to every quantified operator's bound
   variable name (via `_fresh_bound_int()`). Left unreset, that counter's value — and therefore
   the exact bound-variable names baked into a given example's Z3 constraints — depended on how
   many prior examples had already run in the same process. That run-order-dependent naming was
   enough to perturb Z3's MBQI-driven quantifier instantiation and flip individual examples (for
   example `BM_CM_4`) between success and failure depending on test order. The fix is
   `reset_bound_var_counter()`, called once per fresh `BimodalSemantics` instance from
   `BimodalSemantics._reset_global_state()`, so bound-variable names are reproducible and
   independent of prior process history. `test_bound_var_counter_isolation.py` is the empirical
   regression guard for this fix.

`ForAll` itself was never the problem: it is deterministic given deterministic input terms. The
non-determinism came from bound-variable *names* silently varying across runs of the same
process, not from anything unstable about universal quantification. When bimodal countermodel
results become order-dependent again, check counter/naming isolation (is
`reset_bound_var_counter()` still being called on every fresh `BimodalSemantics`? does
`test_bound_var_counter_isolation.py` still pass?) before concluding that `ForAll` instantiation
is inherently non-deterministic and reaching for a quantifier-free rewrite.

## Rendering and Output-Encoding Policy

Bimodal owns the theory's most affected renderer: `print_world_histories` (columnar, horizontal)
and `print_world_histories_vertical` are the only aligned, column-budgeted print paths in the
codebase, so this theory's `docs/` is the natural home for the rendering-policy record the
project's non-ASCII output convention requires. See `code/docs/core/TESTING_GUIDE.md`'s
output-encoding testing section for the full cross-theory policy and its testing recipes; this
subsection records the bimodal-specific consequence: what changes when a glyph is substituted
inside an aligned column layout.

### The Adopted Option

**Stream-encoding-aware ASCII fallback** (`model_checker.utils.glyphs`), not a blanket
ASCII-only mode and not a global interpreter reconfiguration. `BimodalStructure`'s print methods
resolve each glyph via `glyph(name, output)`/`to_subscript(n, output)`, keyed off
`getattr(output, "encoding", None)`: a stream that can encode the preferred Unicode glyph (a real
terminal, a UTF-8 file, `io.StringIO`) gets it; a stream that cannot (a `cp1252`-constrained
Windows pipe) gets a readable ASCII substitute instead of raising `UnicodeEncodeError`.

### The Substitution Table

| Semantic name | Unicode | ASCII fallback | Used by |
|---|---|---|---|
| `DOUBLE_ARROW` | `⟹` | `=>` | `print_evaluation`, `_create_world_line` (columnar world-history arrow) |
| `DOWN_ARROW` | `↓` | `v` | `print_world_histories_vertical` (inter-row arrow) |
| duration subscripts | `₀`-`₉`, `₋` | plain digits, `-` | `_to_subscript` (both arrow call sites above) |

### The Column-Budget Rule: Derive From the Rendered Arrow, Never Hard-Code a Width

`_create_time_positions` computes each time column's starting position by reserving
`column_widths[time] + <arrow width>` per column. **The arrow width is derived from the actual
rendered arrow string** (`_max_arrow_width_for_time`, mirroring `_create_world_line`'s own
per-world duration computation) — never a hard-coded constant. This is a hard rule for this
renderer, not a stylistic preference: a naive `⟹` → `=>` substitution *widens* the arrow slot
(`" ⟹₁ "` is 4 characters, `" =>1 "` is 5), and a fixed-width budget sized for one rendering
silently overflows under the other. Deriving the budget from the actually-rendered string keeps
both the Unicode and the ASCII rendering correctly reserved for, automatically, with no per
-encoding special case.

**Any future change to this renderer's arrow slot must preserve this derivation.** Reverting to a
hard-coded width constant (as the pre-fix code had: `+ 4  # Width + space for " ==> "`, a comment
that already described a 5-character ASCII arrow the code never actually rendered) reintroduces
the alignment defect this policy exists to prevent — including a latent two-digit-duration
overflow (`⟹₁₂` is 5 characters) that predates and is independent of the encoding-safety work,
fixed as a consequence of this same derivation.

### The Alignment Invariant

Within a single rendering, every world-history row's state token for a given time column starts
at the same character column — checked directly, not by inspection, in
`theory_lib/bimodal/tests/unit/test_world_history_alignment.py`. This invariant is asserted
**separately** for the UTF-8 rendering and the `cp1252` rendering; the two renderings are **not**
expected to share identical absolute columns (their arrow widths legitimately differ), only to
each be internally self-consistent. Any future renderer change — a new glyph, a new column type,
a different arrow shape — must preserve this invariant under both encodings, and should extend
this test file rather than introduce a parallel alignment check elsewhere.

The down-arrow (`↓`/`v`) and duration-subscript substitutions are exactly 1-for-1 width-neutral
(one character either way), so — unlike the double-arrow column budget — they need no width
recalculation anywhere they are used. Do not "fix" this by adding width arithmetic for them; the
in-line comment at each call site marks this explicitly so a future editor does not add
unnecessary complexity here.

### Deliberately Out of Scope

Re-enabling `output/progress/display.py`'s commented-out `stream.isatty()` gate on
`TerminalDisplay.enabled` is unrelated to this policy and intentionally untouched — it is a
progress-display *behavior* change (would stop showing progress in any non-terminal context),
not an encoding-safety concern. See `code/docs/core/TESTING_GUIDE.md`'s output-encoding section
for the full record of this and one other recorded scope boundary.

## Testing Architecture

### Test Organization

```
tests/
├── test_bimodal.py         # Basic functionality tests
├── test_iterate.py         # Model iteration tests
├── test_temporal.py        # Temporal operator tests
├── test_modal.py          # Modal operator tests
└── test_interactions.py   # Temporal-modal interaction tests
```

### Test Patterns

```python
# Standard test pattern for bimodal logic
def test_temporal_modal_interaction():
    """Test interaction between temporal and modal operators."""
    theory = get_theory()
    
    # Test □⏵p vs ⏵□p distinction
    example_case = [
        ["□⏵p"],           # Premises: necessarily, p will be true
        ["⏵□p"],           # Conclusions: in the future, p will be necessary
        {"M": 3, "N": 1, "expectation": False}  # These should be different
    ]
    
    example = BuildExample("temporal_modal_test", theory, example_case)
    result = example.check_result()
    
    # Should find countermodel showing the distinction
    assert result['model_found'] == True
```

## Future Development

### Potential Extensions

1. **Temporal Logic Variants**: Branching time, circular time, dense time
2. **Modal Logic Variants**: Different accessibility relations, multi-modal systems
3. **Temporal-Modal Operators**: Until, since, always eventually, etc.
4. **Probabilistic Extensions**: Probabilistic temporal-modal logic

### Integration Opportunities

1. **Cross-Theory Translation**: Automatic translation between bimodal and other theories
2. **Temporal Hyperintensional Logic**: Combining with Logos theory
3. **Dynamic Logic Integration**: Action and temporal-modal reasoning
4. **Performance Optimization**: Specialized solvers for temporal-modal constraints

## Theoretical Background

The bimodal theory combines several logical traditions:

### Temporal Logic Foundation
- **Linear Time**: Discrete time points forming sequences
- **Temporal Operators**: Future and past operators for temporal reasoning
- **Time-Relative Evaluation**: Formulas evaluated at specific time points

### Modal Logic Foundation  
- **Possible Worlds**: Alternative possibilities at each time point
- **Accessibility Relations**: Connections between possible worlds
- **Modal Operators**: Necessity and possibility for modal reasoning

### Combined Framework
- **World Histories**: Sequences of worlds across time
- **Dual Accessibility**: Both temporal and modal accessibility relations
- **Point Evaluation**: Formulas evaluated at (world, time) pairs

## Conclusion

The Bimodal theory architecture provides a sophisticated implementation of temporal-modal logic within the ModelChecker framework. The design emphasizes:

- **Dual Reasoning**: Seamless integration of temporal and modal operators
- **Scalability**: Efficient handling of complex temporal-modal structures
- **Extensibility**: Clear extension points for new temporal-modal operators
- **Performance**: Optimization strategies for computationally intensive reasoning
- **Integration**: Full compatibility with ModelChecker ecosystem

This architecture enables researchers to explore sophisticated temporal-modal reasoning patterns while maintaining the performance and usability standards expected from the ModelChecker platform.

---

**Navigation**: [README](../README.md) | [User Guide](USER_GUIDE.md) | [Operators](OPERATORS.md) | [Settings](SETTINGS.md)