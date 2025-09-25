# Testing Semantic Constraints: Proving Properties Through Countermodel Search

[← Back to Usage](README.md) | [Workflow →](WORKFLOW.md) | [Tools →](TOOLS.md)

## Table of Contents

1. [Introduction](#introduction)
2. [Core Architecture](#core-architecture)
   - [The Constraint Testing Pattern](#the-constraint-testing-pattern)
   - [Proof by Absence](#proof-by-absence)
3. [Implementation Techniques](#implementation-techniques)
   - [Theory-Specific Settings](#theory-specific-settings)
   - [Constraint Negation](#constraint-negation)
   - [Result Interpretation](#result-interpretation)
4. [Practical Examples](#practical-examples)
   - [Frame Constraints in Imposition Theory](#frame-constraints-in-imposition-theory)
   - [Testing Your Own Constraints](#testing-your-own-constraints)
5. [Advanced Applications](#advanced-applications)
   - [Discovering Minimal Axioms](#discovering-minimal-axioms)
   - [Comparing Constraint Systems](#comparing-constraint-systems)
6. [Troubleshooting](#troubleshooting)
7. [References](#references)

## Introduction

ModelChecker provides a methods for easily deriving semantic constraints, or establishing implications between constraints. Instead of manually proving theorems, you can use the framework to search for countermodels - if none exist, the constraint is proven to hold for at least those models that it has surveyed.

This guide explains how to use ModelChecker's constraint testing features to verify semantic properties, discover minimal axiom sets, and understand the relationships between different constraint systems. The techniques shown here are particularly valuable for researchers developing new semantic theories or investigating the foundations of existing ones.

**Architecture Context**: For the theoretical foundations of how ModelChecker transforms logical constraints into semantic models, see the [Semantics Architecture](../architecture/SEMANTICS.md). For understanding the complete pipeline from formulas to models, see the [Pipeline Overview](../architecture/PIPELINE.md).

## Core Architecture

### The Constraint Testing Pattern

The fundamental insight is to **search for violations rather than prove validity**. Given a semantic definition and a proposed constraint:

1. **Negate the constraint** - Add its negation to the model
2. **Search for models** - Use Z3 to find satisfying assignments
3. **Interpret absence** - No model means the constraint always holds

```python
# Traditional approach: Add constraint and hope it's satisfied
constraints.append(ForAll([x, y], property(x, y)))

# Constraint testing: Search for violations
test_constraints = [Exists([x, y], Not(property(x, y)))]
# If no model found => property always holds
```

This approach transforms theorem proving into model finding, leveraging Z3's efficient search capabilities.

### Proof by Absence

When ModelChecker reports "there is no countermodel" for a negated constraint, this constitutes a proof that the original constraint is entailed by the base semantics modulo the size of the models checked. The proof is constructive in the sense that Z3 has exhaustively searched the finite model space without finding violations.

Key insights:
- **Finite models suffice** - For most logical properties, small models (N=3-5) provide adequate test cases
- **Systematic search** - Z3 explores all possible assignments efficiently
- **Unsat cores** - When no model exists, Z3 can identify which constraints conflict

### Complementing Traditional Proofs

ModelChecker is not intended to replace pen-and-paper semantic proofs. Rather, it serves as a powerful companion tool that streamlines the research process:

**Rapid Exploration**: Quickly test conjectures and explore logical implications before investing time in formal proofs. What might take hours to work through by hand can be checked in seconds.

**Error Prevention**: Catch small mistakes early - a missing case, an incorrect assumption about parthood relations, or an overlooked interaction between constraints. These errors are easy to make in complex proofs but immediately revealed by countermodels.

**Hypothesis Generation**: Use countermodels to understand why certain properties fail, guiding the development of stronger or more refined principles. The concrete examples help build intuition about abstract relationships.

**Proof Validation**: After completing a pen-and-paper proof, use ModelChecker to verify the result holds in finite models. While not a complete verification, this provides valuable confidence in the proof's correctness.

The tool excels at the exploratory phase of research, where you're developing theories and testing relationships. Once you've used ModelChecker to map the logical terrain and avoid pitfalls, traditional proof methods remain essential for establishing results with full mathematical rigor.

## Implementation Techniques

### Recursive Semantic Dispatch Architecture

The ModelChecker implements a sophisticated recursive dispatch system that seamlessly integrates semantic frameworks with modular operator implementations. This architecture enables both compositional semantics and operator modularity through carefully coordinated method calls.

**Architecture Reference**: For the complete architectural design of the syntactic-semantic bridge, see [Syntactic Architecture](../architecture/SYNTACTIC.md) and [Builder Architecture](../architecture/BUILDER.md) which orchestrates the entire pipeline.

#### The Dispatch Pattern

When evaluating a complex formula, the semantic class delegates to operator methods, which recursively call back to the semantics for their arguments:

```python
# In semantic.py: Initial dispatch to operator
def true_at(self, sentence, eval_point):
    if sentence.is_atomic():
        # Base case: atomic propositions handled directly
        return self._evaluate_atomic(sentence, eval_point)
    else:
        # Recursive case: delegate to operator implementation
        operator = self.get_operator(sentence.main_operator)
        return operator.true_at(*sentence.arguments, eval_point)

# In operators.py: Operator calls back to semantics for arguments
class AndOperator(syntactic.Operator):
    def true_at(self, leftarg, rightarg, eval_point):
        # Recursive dispatch back to semantics for subformulas
        return z3.And(
            self.semantics.true_at(leftarg, eval_point),    # Recurse on left
            self.semantics.true_at(rightarg, eval_point)    # Recurse on right
        )
```

#### Extended Semantics Dispatch

The same recursive pattern applies to hyperintensional evaluation methods:

```python
# In semantic.py: Dispatch to operator for extended verification
def extended_verify(self, state, sentence, eval_point):
    if sentence.is_atomic():
        return self.verify(state, sentence.letter)
    else:
        operator = self.get_operator(sentence.main_operator)
        return operator.extended_verify(state, *sentence.arguments, eval_point)

# In operators.py: Operator recursively calls semantics for arguments
class NecessityOperator(syntactic.Operator):
    def extended_verify(self, state, argument, eval_point):
        # Only the null state can verify necessity statements
        return z3.And(
            state == self.semantics.null_state,
            # Recursive call: argument must be true at evaluation point
            self.semantics.true_at(argument, eval_point)
        )
```

#### Modularity Benefits

1. **Separation of Concerns**: Semantic framework handles infrastructure (states, worlds, basic relations) while operators implement logical behavior
2. **Operator Independence**: Each operator class is self-contained and can be developed/tested separately
3. **Dynamic Loading**: Theories can selectively include operator sets through the registry system
4. **Recursive Composition**: Complex formulas automatically decompose through the dispatch pattern

### Theory-Specific Settings

ModelChecker supports theory-specific settings that modify constraint generation. The pattern for implementing constraint testing:

```python
class YourSemantics(SemanticDefaults):
    DEFAULT_GENERAL_SETTINGS = {
        "test_constraint": False,  # Theory-specific setting
    }
    
    def __init__(self, combined_settings):
        self.test_constraint = combined_settings.get('test_constraint', False)
        
        if self.test_constraint:
            # Replace normal constraints with test constraints
            self.constraints = self._generate_test_constraints()
        else:
            # Normal semantic constraints
            self.constraints = self._generate_normal_constraints()
```

### Constraint Negation

The key technique is replacing normal constraints with their negations:

```python
def _generate_test_constraints(self):
    """Generate constraints that test whether properties hold."""
    
    # Define the properties you want to test
    property1 = ForAll([x, y], 
        Implies(self.relation(x, y), self.desired_property(x, y))
    )
    
    property2 = ForAll([x],
        Implies(self.condition(x), self.expected_result(x))
    )
    
    # Return disjunction of negations
    # This searches for ANY violation
    return [Or(
        Not(property1),
        Not(property2)
    )]
```

The disjunction means we're looking for a model that violates *at least one* property, making the search more efficient than testing properties individually.

### Result Interpretation

Results from constraint testing:

- **"No countermodel"** - All tested properties are satisfied by the base semantics
- **"Countermodel found"** - At least one property can be violated
- **Specific violations** - The countermodel shows exactly which property fails and how

## Practical Examples

### Frame Constraints in Imposition Theory

The imposition theory provides an excellent example of constraint testing in action. Fine's imposition semantics requires four frame constraints on the primitive relation, but the logos semantics defines alternatives constructively. To test whether the constructive definition automatically satisfies these constraints:

```python
# In imposition/semantic.py
if self.derive_imposition:
    # Test whether is_alternative satisfies frame constraints
    constraints = self._derive_imposition()
    
def _derive_imposition(self):
    # Define frame constraint analogs
    inclusion = ForAll([x, y, z],
        Implies(alt_imposition(x, y, z), part(x, z))
    )
    
    actuality = ForAll([x, y],
        Implies(And(part(x, y), world(y)),
            Exists([z], And(part(z, y), alt_imposition(x, y, z)))
        )
    )
    
    # Return negation to search for violations
    return [Or(Not(inclusion), Not(actuality), ...)]
```

Running with `derive_imposition=True`:
```python
# In imposition theory example file - set derive_imposition in settings
IM_TR_0_settings = {
    'N': 3,
    'derive_imposition': True  # Test whether derived constraints hold
}

# Result: "there is no countermodel"
# Proves: is_alternative automatically satisfies all frame constraints
```

This proves that the constructive definition inherently has the right structural properties without needing explicit constraints.

### Testing Your Own Constraints

To test constraints in your own semantic theory:

1. **Add a theory setting**:
```python
DEFAULT_GENERAL_SETTINGS = {
    "test_fusion_closure": False,
}
```

2. **Implement constraint generation**:
```python
def _test_fusion_closure(self):
    # Property: if s1 and s2 verify A, their fusion must too
    x, y = BitVecs('x y', self.N)
    
    fusion_closure = ForAll([x, y],
        Implies(
            And(self.verify(x, self.A), self.verify(y, self.A)),
            self.verify(self.fusion(x, y), self.A)
        )
    )
    
    # Search for violations
    return [Not(fusion_closure)]
```

3. **Run the test**:
```python
# In your test.py file:
TEST_settings = {
    'N': 3,
    'test_fusion_closure': True  # Enable the constraint test
}
```

```bash
# Run the test
model-checker your_theory/test.py
```

## Advanced Applications

### Discovering Minimal Axioms

Use constraint testing to find minimal axiom sets:

1. **Start with all constraints active**
2. **Systematically remove constraints**
3. **Test if remaining constraints entail the removed one**
4. **Identify dependencies and redundancies**

```python
# Test if constraint C is entailed by constraints A and B
constraints = [A, B, Not(C)]
# If no model exists, then A ∧ B ⊢ C
```

This technique helps identify the logical core of a semantic theory.

### Comparing Constraint Systems

Compare how different constraint systems relate:

```python
# Do Fine's constraints entail logos properties?
def test_constraint_entailment():
    # Add Fine's constraints
    fine_constraints = [inclusion, actuality, incorporation, completeness]

    # Test if they entail a logos property
    logos_property = ForAll([u, y, w],
        Implies(
            is_alternative(u, y, w),
            Exists([z], And(
                part(z, u),
                max_compatible_part(z, w, y)
            ))
        )
    )

    return fine_constraints + [Not(logos_property)]
```

This reveals logical relationships between different semantic frameworks.

### Z3 Integration and Model Evaluation

ModelChecker's semantic testing relies on sophisticated integration with the Z3 theorem prover, converting semantic constraints into Z3 formulas and extracting meaningful results from Z3 models.

**Architecture Deep Dive**: For comprehensive details on how semantic constraints are generated and processed, see [Semantics Architecture](../architecture/SEMANTICS.md). For the model structure and constraint system, see [Models Architecture](../architecture/MODELS.md).

#### Constraint Generation Pipeline

```python
# Semantic constraints become Z3 first-order formulas
class LogosSemantics(SemanticDefaults):

    def __init__(self):
        # ... initialization code ...

        # Define the frame constraints
        x, y = z3.BitVecs("frame_x frame_y", self.N)

        # Possibility downward closure: parts of possible states are possible
        possibility_downward_closure = ForAll(
            [x, y],
            z3.Implies(
                z3.And(
                    self.possible(y),
                    self.is_part_of(x, y)
                ),
                self.possible(x)
            ),
        )

        # Set frame constraints
        self.frame_constraints = [
            possibility_downward_closure,
            self.is_world(self.main_world),  # Main evaluation world exists
        ]
```

#### Z3 Model Extraction

When Z3 finds a satisfying model, ModelChecker extracts structured semantic information:

```python
class LogosModelStructure:
    def extract_from_z3_model(self, z3_model, semantics):
        """Extract semantic structure from Z3 model."""

        # Extract possible states
        self.possible_states = {
            state for state in self.all_states
            if self._evaluate_z3_boolean(z3_model, semantics.possible(state))
        }

        # Extract worlds (maximal possible states)
        self.worlds = {
            state for state in self.possible_states
            if self._evaluate_z3_boolean(z3_model, semantics.is_world(state))
        }

        # Extract main evaluation world
        self.main_world = next(
            state for state in self.worlds
            if self._evaluate_z3_boolean(z3_model, semantics.main_world == state)
        )

    def _evaluate_z3_boolean(self, model, z3_expr):
        """Safely evaluate Z3 expression to Python boolean."""
        try:
            result = model.evaluate(z3_expr)
            return z3.is_true(result)
        except:
            return False  # Handle symbolic expressions gracefully
```

### Verifier and Falsifier Computation

The heart of hyperintensional semantics lies in computing which states verify or falsify each proposition. This process combines Z3 model evaluation with set-theoretic operations.

#### Proposition Analysis

```python
class LogosProposition:
    def find_proposition(self):
        """Extract verifier and falsifier sets from Z3 model."""
        model = self.model_structure.model
        semantics = self.model_structure.semantics

        # Extract verifiers: states where verify(state, letter) is true
        verifiers = {
            state for state in self.model_structure.possible_states
            if self._evaluate_z3_boolean(
                model, semantics.verify(state, self.sentence_letter)
            )
        }

        # Extract falsifiers: states where falsify(state, letter) is true
        falsifiers = {
            state for state in self.model_structure.possible_states
            if self._evaluate_z3_boolean(
                model, semantics.falsify(state, self.sentence_letter)
            )
        }

        return verifiers, falsifiers

    def _evaluate_z3_boolean(self, model, z3_expr):
        """Robust Z3 expression evaluation."""
        try:
            evaluated = model.evaluate(z3_expr, model_completion=True)
            return z3.is_true(evaluated)
        except Exception:
            # Handle cases where Z3 returns symbolic expressions
            return False
```

#### Complex Formula Computation

For complex formulas, verifier/falsifier sets are computed compositionally using operator-specific rules:

```python
# In operators.py: AndOperator verifier/falsifier computation
def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
    """Conjunction verifiers are products of argument verifiers."""
    left_V, left_F = left_sent_obj.proposition.find_proposition()
    right_V, right_F = right_sent_obj.proposition.find_proposition()

    # Verifiers: states that verify both conjuncts
    verifiers = product(left_V, right_V)  # Fusion of verifier pairs

    # Falsifiers: states that falsify at least one conjunct
    falsifiers = coproduct(left_F, right_F)  # Union with overlap handling

    return verifiers, falsifiers

def product(set1, set2):
    """Fusion product of two state sets."""
    return {state1 | state2 for state1 in set1 for state2 in set2}

def coproduct(set1, set2):
    """Disjoint union handling overlaps appropriately."""
    return set1.union(set2)
```

## Troubleshooting

### Common Issues

**Timeouts with large N**:
- Start with N=3 or N=4 for initial tests
- Increase gradually only if no countermodel found
- Remember: small countermodels often suffice

**Unclear which constraint fails**:
- Test constraints individually first
- Use `--print-constraints` to see generated formulas
- Check `--print-z3` for raw solver output

**Settings not recognized**:
- Ensure setting is in `DEFAULT_GENERAL_SETTINGS`
- Check setting name matches exactly
- Verify theory initialization handles the setting

### Debugging Techniques

```python
# In your test.py file, set test_constraint in settings:
TEST_settings = {
    'N': 3,                    # Start with small state space
    'test_constraint': True,   # Enable constraint testing
    'max_time': 20
}
```

```bash
# See what constraints are generated
model-checker test.py --print-constraints

# Get detailed Z3 output
model-checker test.py --print-z3

# Both debug flags together
model-checker test.py --print-constraints --print-z3
```

## References

### Implementation Examples
- **[Imposition Semantics](../../Code/src/model_checker/theory_lib/imposition/semantic.py)** - Complete `derive_imposition` implementation
- **[Imposition Comparison Reports](../../Code/src/model_checker/theory_lib/imposition/reports/imposition_comparison/README.md)** - Comprehensive analysis of constraint testing methodology and theory comparison

### Related Documentation
- **[Theory Development](WORKFLOW.md#theory-development-workflow)** - Creating new theories
- **[Examples Guide](EXAMPLES.md)** - Writing constraint test examples
- **[Output Guide](OUTPUT.md)** - Saving constraint test results
- **[Operators Guide](OPERATORS.md)** - Implementing modular operator systems
- **[Settings Guide](SETTINGS.md)** - Configuring semantic parameters

### Theoretical Background
- **[Architecture](../architecture/README.md)** - ModelChecker's approach
- **[Semantic Properties](../architecture/SEMANTICS.md)** - Constraint types
- **[Model Theory](../architecture/MODELS.md)** - Finite model construction

---

[← Back to Usage](README.md) | [Workflow →](WORKFLOW.md) | [Theory Library →](../../Code/src/model_checker/theory_lib/README.md)
