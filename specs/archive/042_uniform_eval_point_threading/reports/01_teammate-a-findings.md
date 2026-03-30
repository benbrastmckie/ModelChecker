# Teammate A Findings: eval_point Threading Patterns in Logos Subtheories

**Task**: 42 - Uniform eval_point threading across all logos subtheory operators
**Artifact**: 01
**Teammate**: A
**Focus**: Implementation approaches and current patterns in the logos/ subtheories

---

## Key Findings

### 1. The eval_point Structure and the Core Problem

The `eval_point` dictionary is the primary carrier of evaluation context throughout the semantic
machinery. Currently in `LogosSemantics.__init__`, the `main_point` is initialized with only
one key:

```python
self.main_point = {
    "world": self.main_world
}
```

The `with_assignment` and `get_assignment` helpers (added for first-order support) allow the
`eval_point` to carry an optional second key:

```python
# get_assignment (with safe fallback to empty assignment):
return eval_point.get("assignment", VariableAssignment.empty())

# with_assignment (spreads existing keys, adds/replaces assignment):
return {**eval_point, "assignment": assignment}
```

This design is correct for propagating the variable assignment from the `main_point` into
recursive calls - but only if every operator that creates a new `eval_point` for a shifted world
carries forward the full existing `eval_point` rather than constructing a bare `{"world": u}` dict.

### 2. Which Operators Create Shifted eval_points (Intensional Operators)

These operators shift the evaluation world, and all of them are currently creating bare
`{"world": u}` dicts that drop the `assignment` key:

#### modal/operators.py - NecessityOperator

```python
# true_at (lines 43-48):
sem.true_at(argument, {"world": u})     # DROPS assignment

# false_at (lines 54-59):
sem.false_at(argument, {"world": u})    # DROPS assignment
```

The `NecessityOperator.true_at` and `false_at` both construct fresh dicts with only `"world"`.
If a formula like `\\Box (\\forall v. P[v])` is evaluated, the universal quantifier sees an
`eval_point` without `"assignment"` - which is acceptable (it uses `get_assignment` with fallback)
- but breaks the transparency principle because any pre-existing assignment context is silently
discarded at the world-shift boundary.

#### modal/operators.py - PossibilityOperator (partially written, appears unused)

```python
# true_at (line 118):
sem.true_at(argument, {"world": u, "time": eval_point["time"]})

# false_at (line 131):
sem.false_at(argument, {"world": u, "time": eval_point["time"]})
```

This version attempts to carry a `"time"` key but also introduces `eval_point["time"]` which
would cause a `KeyError` because the standard logos `main_point` has no `"time"` key. This code
appears to be a bimodal leftover that was not cleaned up. It also drops `"assignment"`.

#### counterfactual/operators.py - CounterfactualOperator

```python
# true_at (line 50):
semantics.true_at(rightarg, {"world": u})     # DROPS assignment

# false_at (line 65):
semantics.false_at(rightarg, {"world": u})    # DROPS assignment
```

Both the true and false cases shift to alternative world `u` using a bare dict. The antecedent
evaluation uses `extended_verify(x, leftarg, eval_point)` (passing the full `eval_point` through
correctly), but the consequent evaluation at the alternative world drops the assignment.

### 3. Which Operators Are Extensional (Correctly Pass eval_point Through)

These operators pass `eval_point` unchanged to their recursive calls - the correct pattern for
extensional operators that do not shift the world:

**extensional/operators.py**: All operators (`NegationOperator`, `AndOperator`, `OrOperator`,
`TopOperator`, `BotOperator`, `ConditionalOperator`, `BiconditionalOperator`) uniformly pass
`eval_point` through unchanged:

```python
# Example from NegationOperator:
def true_at(self, argument, eval_point):
    return self.semantics.false_at(argument, eval_point)   # passes through correctly
```

**constitutive/operators.py**: All operators (`IdentityOperator`, `GroundOperator`,
`EssenceOperator`, `RelevanceOperator`, `ReductionOperator`) pass `eval_point` through unchanged.
These are hyperintensional operators but do not shift worlds - they quantify over verifiers and
falsifiers at the current eval_point:

```python
# Example from IdentityOperator.true_at:
semantics.extended_verify(x, leftarg, eval_point)    # passes through correctly
semantics.extended_falsify(x, leftarg, eval_point)   # passes through correctly
```

### 4. First-Order Operators: Correctly Shift Assignment in eval_point

The first-order operators (`LambdaOperator`, `ForAllOperator`, `ExistsOperator`) all follow the
correct pattern: they extract the existing assignment from `eval_point`, extend it with new
bindings, and create the new `eval_point` using `with_assignment` (which uses `{**eval_point, ...}`
to preserve the existing world key and any other keys):

```python
# Example from ForAllOperator.true_at:
assignment = sem.get_assignment(eval_point)
new_assignment = assignment.variant(variable, domain_elem)
new_eval_point = sem.with_assignment(eval_point, new_assignment)
constraints.append(sem.true_at(formula, new_eval_point))
```

This is the correct pattern. The world is preserved (via `{**eval_point, "assignment": ...}`),
and only the `"assignment"` key is updated. However, if a quantifier is nested inside a modal
or counterfactual operator, the formula is evaluated at an `eval_point` that was created by
the outer operator without an `"assignment"` key - so the inner quantifier's `get_assignment`
correctly falls back to an empty assignment. The problem manifests only when first-order
quantification is combined with world-shifting operators.

### 5. The find_proposition Method in LogosProposition

The `find_proposition` method in `LogosProposition` also constructs a bare `{"world": eval_world}`
dict:

```python
# Lines 1207-1209:
eval_point = {"world": eval_world}
if assignment is not None:
    eval_point = semantics.with_assignment(eval_point, assignment)
return operator.find_verifiers_and_falsifiers(*arguments, eval_point)
```

This is acceptable for the model-enumeration phase (where `eval_world` is a concrete Z3 value
and there is no outer assignment context), but it follows the same pattern of building
`eval_point` from scratch rather than extending a pre-existing one.

---

## Recommended Approach

### Standard Pattern for World-Shifting Operators

Every intensional operator that quantifies over worlds (modal, counterfactual) should use
`with_world` - a helper analogous to `with_assignment` - to create the shifted eval_point:

```python
# Proposed helper to add to LogosSemantics:
def with_world(self, eval_point, world):
    """Create a new evaluation point with a different world, preserving all other keys."""
    return {**eval_point, "world": world}
```

This helper should be added to `LogosSemantics` alongside the existing `with_assignment`.

Using `with_world`, the broken patterns become:

```python
# NecessityOperator.true_at - BEFORE:
sem.true_at(argument, {"world": u})

# AFTER:
sem.true_at(argument, sem.with_world(eval_point, u))
```

```python
# CounterfactualOperator.true_at - BEFORE:
semantics.true_at(rightarg, {"world": u})

# AFTER:
semantics.true_at(rightarg, semantics.with_world(eval_point, u))
```

### Semantic Principle to Enforce

The distinction between extensional and intensional operators should be formalized:

- **Extensional operators** (negation, conjunction, disjunction, material conditional,
  biconditional, constitutive operators): pass `eval_point` unchanged to subformulas.
  These operators do not shift the world or the variable assignment.

- **Intensional world-shifting operators** (necessity, counterfactual): use `with_world` to
  create a new `eval_point` that preserves the assignment but shifts the world.

- **Variable-binding operators** (forall, exists, lambda): use `with_assignment` to create a
  new `eval_point` that preserves the world but extends the assignment.

- **Operators that shift both world and assignment** (a modal operator applied to a
  first-order formula): the composition works automatically when both helpers are used
  correctly, because `{**eval_point, "world": u}` preserves "assignment", and
  `{**eval_point, "assignment": sigma}` preserves "world".

### What Needs Changing

1. **Add `with_world` helper** to `LogosSemantics` (semantic.py, alongside `with_assignment`).

2. **Fix `NecessityOperator`** (modal/operators.py, lines 46 and 58):
   - Replace `{"world": u}` with `sem.with_world(eval_point, u)` in both `true_at` and `false_at`.

3. **Fix `CounterfactualOperator`** (counterfactual/operators.py, lines 50 and 65):
   - Replace `{"world": u}` with `semantics.with_world(eval_point, u)` in both `true_at` and
     `false_at`.

4. **Fix `PossibilityOperator`** (modal/operators.py, lines 118 and 131):
   - This code appears to be a vestigial bimodal operator and references `eval_point["time"]`
     which does not exist in the standard logos framework. It should either be removed or
     rewritten to use `sem.with_world(eval_point, u)`.

5. **Update `find_proposition` in `LogosProposition`** (semantic.py, line 1207):
   - The current construction `{"world": eval_world}` is fine for the concrete model-evaluation
     phase (where no assignment context exists), but should be documented as intentional.

---

## Evidence/Examples

### Location of all bare dict constructions that drop assignment:

| File | Line(s) | Pattern | Impact |
|------|---------|---------|--------|
| `subtheories/modal/operators.py` | 46, 58 | `{"world": u}` | Drops assignment in necessity evaluation |
| `subtheories/modal/operators.py` | 118, 131 | `{"world": u, "time": eval_point["time"]}` | Drops assignment AND raises KeyError for "time" |
| `subtheories/counterfactual/operators.py` | 50, 65 | `{"world": u}` | Drops assignment in counterfactual consequent |

### Location of correct pattern using `with_assignment`:

| File | Lines | Pattern |
|------|-------|---------|
| `subtheories/first-order/operators.py` | 88-91, 102-105, 117-120, etc. | `sem.with_assignment(eval_point, new_assignment)` |

### Location of the helper methods:

| File | Lines | Method |
|------|-------|--------|
| `theory_lib/logos/semantic.py` | 640-653 | `get_assignment` |
| `theory_lib/logos/semantic.py` | 655-673 | `with_assignment` |

---

## Confidence Level: High

The evidence is unambiguous: bare `{"world": u}` dict constructions exist in the modal and
counterfactual operators. The fix is straightforward - add a `with_world` helper and replace
the bare constructions. The correctness of this approach is confirmed by the existing
`with_assignment` pattern used in the first-order operators.

The `with_world` pattern also provides semantic transparency: a reader can see at a glance
that the modal operator "shifts the world while preserving everything else", just as
`with_assignment` signals "binds a variable while preserving the world". Without this pattern,
the semantics is opaque about what is preserved across world shifts.
