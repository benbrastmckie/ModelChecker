# Semantics: From Strings to Z3 Constraints

[← Syntax Pipeline](SYNTAX.md) | [Back to Methodology](README.md) | [Model Finding →](MODELS.md)

## Table of Contents

1. [Introduction](#introduction)
2. [Base Classes Overview](#base-classes-overview)
   - [SemanticDefaults](#semanticdefaults)
   - [PropositionDefaults](#propositiondefaults)
   - [ModelDefaults](#modeldefaults)
   - [ModelConstraints](#modelconstraints)
3. [Logos Semantic Pipeline](#logos-semantic-pipeline)
   - [LogosSemantics Structure](#logossemantics-structure)
   - [Z3 Primitive Declaration](#z3-primitive-declaration)
   - [Frame Constraints](#frame-constraints)
   - [Truth/Falsity Evaluation](#truthfalsity-evaluation)
   - [Main Evaluation Point](#main-evaluation-point)
4. [LogosProposition Class](#logosproposition-class)
   - [Role in Constraining](#role-in-constraining)
   - [Verifier/Falsifier Computation](#verifierfalsifier-computation)
   - [Proposition Constraints Hierarchy](#proposition-constraints-hierarchy)
   - [Settings Interaction](#settings-interaction)
5. [Operator Implementation Pattern](#operator-implementation-pattern)
   - [Operator Base Class](#operator-base-class)
   - [Required Methods](#required-methods)
   - [Finding Verifiers/Falsifiers](#finding-verifiersfalsifiers)
   - [Print Methods](#print-methods)
6. [Subtheory Architecture](#subtheory-architecture)
   - [Operator Registry System](#operator-registry-system)
   - [Dynamic Loading](#dynamic-loading)
   - [Dependency Management](#dependency-management)
   - [Conflict Resolution](#conflict-resolution)
7. [Z3 Constraint Collection](#z3-constraint-collection)
   - [Frame Constraints](#frame-constraints-1)
   - [Model Constraints](#model-constraints-1)
   - [Premise Constraints](#premise-constraints)
   - [Conclusion Constraints](#conclusion-constraints)
   - [Settings-Based Generation](#settings-based-generation)
   - [Complete Aggregation](#complete-aggregation)
   - [Debugging Techniques](#debugging-techniques)
8. [Example Constraint Pipeline](#example-constraint-pipeline)
9. [Code Examples](#code-examples)
10. [References](#references)

## Introduction

The semantics module bridges the gap between parsed logical formulas and SMT solver constraints. It provides a flexible framework for implementing various semantic theories, from classical possible worlds semantics to more complex approaches like truthmaker semantics. Each theory defines its own interpretation rules while sharing the common constraint generation pipeline.

The pipeline transforms syntactic structures into Z3 constraints through a series of semantic interpretation layers, each adding specific constraints based on the logical theory and configured settings. The result is a complete set of constraints that, when solved, yields models demonstrating validity or invalidity of logical arguments.

Key architectural insights:

- **Theory Independence**: Semantic theories plug into the framework without modifying core infrastructure
- **Constraint Layering**: Different constraint types (frame, model, evaluation) compose cleanly
- **Settings-Driven Behavior**: Runtime configuration controls semantic properties without code changes
- **Modular Operators**: New logical connectives integrate through a consistent interface

For the parsing stage that precedes semantic interpretation, see [Syntax Pipeline](SYNTAX.md). For how generated constraints are solved, see [Model Finding](MODELS.md).

## Semantic Pipeline Overview

The complete semantic pipeline transforms parsed syntax into Z3 constraints through multiple stages:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         SEMANTIC PIPELINE FLOW                          │
└─────────────────────────────────────────────────────────────────────────┘

1. INITIALIZATION
┌────────────────────┐    ┌────────────────────┐    ┌────────────────────┐
│ Theory Classes     │    │ Settings           │    │ Parsed Syntax      │
│ • SemanticClass    │    │ • N (state bits)   │    │ • Sentence objects │
│ • PropositionClass │───▶│ • contingent       │───▶│ • Operator refs    │
│ • ModelClass       │    │ • non_empty, etc   │    │ • Atomic letters   │
└────────────────────┘    └────────────────────┘    └────────────────────┘
         │                           │                          │
         └───────────────────────────┼──────────────────────────┘
                                     │
                                     ▼
2. SEMANTIC INSTANTIATION   ┌─────────────────────────────┐
                            │   ModelConstraints          │
                            │ • Instantiate semantics     │
                            │ • Link operators to theory  │
                            │ • Update sentence objects   │
                            └────────┬────────────────────┘
                                     │
3. Z3 PRIMITIVE SETUP                ▼
┌─────────────────────────────────────────────────────────────────────────┐
│ SemanticDefaults.__init__                                               │
│ • verify: BitVec × Atom → Bool     (state verifies proposition)         │
│ • falsify: BitVec × Atom → Bool    (state falsifies proposition)        │
│ • possible: BitVec → Bool          (state is possible in model)         │
│ • Additional theory-specific functions (accessibility, etc.)            │
└────────────────────────────────────┬────────────────────────────────────┘
                                     │
4. CONSTRAINT GENERATION             ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                         Four Types of Constraints                       │
├─────────────────────────────────────────────────────────────────────────┤
│ FRAME          │ ATOMIC PROPS      │ PREMISES        │ CONCLUSIONS      │
│ • Possibility  │ • Classical logic │ • All true at w │ • ≥1 false at w  │
│   closure      │ • Settings-based  │ • Use true_at() │ • Use false_at() │
│ • Main world   │   (contingent,    │ • Recursive     │ • Creates        │
│ • Theory rules │   non_empty...)   │   evaluation    │   countermodel   │
└────────────────┴───────────────────┼─────────────────┴──────────────────┘
                                     │
                                     │
                                     │
5. OPERATOR EVALUATION               ▼
┌─────────────────────────────────────────────────────────────────────────┐
│ Operators Generate Constraints via Semantic Methods                     │
│                                                                         │
│ ┌─────────────┐  extended_verify()   ┌─────────────────────────────┐    │
│ │ Atomic: A   │─────────────────────▶│ verify(state, A)            │    │
│ └─────────────┘                      └─────────────────────────────┘    │
│                                                                         │
│ ┌─────────────┐  Recursive calls     ┌─────────────────────────────┐    │
│ │ Complex:    │─────────────────────▶│ ∃x,y: state = x|y ∧         │    │
│ │ A ∧ B       │  to subformulas      │       verify(x,A) ∧         │    │
│ └─────────────┘                      │       verify(y,B)           │    │
│                                      └─────────────────────────────┘    │
└─────────────────────────────────────┬───────────────────────────────────┘
                                      │
6. CONSTRAINT AGGREGATION             ▼
                        ┌─────────────────────────────┐
                        │   All Constraints to Z3     │
                        │ • solver.add(frame_constr)  │
                        │ • solver.add(model_constr)  │
                        │ • solver.add(premise_constr)│
                        │ • solver.add(conclusion)    │
                        └─────────────┬───────────────┘
                                      │
                                      ▼
                            ┌──────────────────┐
                            │   Z3 SOLVER      │
                            │ • SAT → Model    │
                            │ • UNSAT → Valid  │
                            └──────────────────┘
```

This pipeline demonstrates how semantic theories plug into the framework: they define Z3 primitives and evaluation rules, the framework generates appropriate constraints, and the solver finds models satisfying all constraints. Each stage maintains clean separation of concerns while passing necessary information forward.

## Base Classes Overview

### SemanticDefaults

The foundation for all semantic implementations, providing core operations:

```python
class SemanticDefaults:
    """Base semantic operations for modal logics."""

    def __init__(self, combined_settings):
        self.N = combined_settings['N']  # Number of atomic states (bit positions)
        self.name = self.__class__.__name__

        # Core state operations
        self.full_state = BitVecVal((1 << N) - 1, N)  # All bits set (e.g., 111 for N=3)
        self.null_state = BitVecVal(0, N)             # No bits set (e.g., 000)
        self.all_states = [BitVecVal(i, N) for i in range(1 << N)]  # All 2^N states

    def fusion(self, bit_s, bit_t):
        """State combination via bitwise OR."""
        return bit_s | bit_t  # Fusion creates smallest state containing both

    def is_part_of(self, bit_s, bit_t):
        """Mereological part-of relation."""
        return self.fusion(bit_s, bit_t) == bit_t  # s ≤ t iff s|t = t
```

*Full implementation: [`model_checker/model.py`](../../Code/src/model_checker/model.py)*

The bit vector representation enables efficient state operations: fusion combines states (union of properties), parthood checks containment (subset of properties), and the fixed size N limits the state space for tractable solving. This mereological approach treats states as parts that can be combined, enabling fine-grained semantic distinctions.

### PropositionDefaults

Base class for proposition representation and constraint generation:

```python
class PropositionDefaults:
    """Links sentences to semantic interpretation."""

    def __init__(self, sentence, model_structure):
        self.sentence = sentence
        self.model_structure = model_structure
        self.semantics = model_structure.semantics
        self.N = self.semantics.N

    def find_proposition(self):
        """Find verifier and falsifier sets."""
        # Implemented by subclasses - returns (verifiers, falsifiers)

    def proposition_constraints(self, sentence_letter):
        """Generate constraints for atomic propositions."""
        # Implemented by subclasses - returns list of Z3 constraints
```

*Full implementation: [`model_checker/model.py`](../../Code/src/model_checker/model.py)*

PropositionDefaults acts as the bridge between syntactic sentence objects and their semantic interpretation. Each proposition tracks which states make it true (verifiers) and false (falsifiers), enabling hyperintensional distinctions where logically equivalent sentences can have different truthmakers.

### ModelDefaults

Core model structure and solving capabilities:

```python
class ModelDefaults:
    """Handles Z3 solving and model interpretation."""

    def __init__(self, model_constraints, settings):
        self.model_constraints = model_constraints
        self.semantics = model_constraints.semantics
        self.settings = settings

        # Constraint collection by type
        self.frame_constraints = []      # Structural properties of the semantics
        self.model_constraints_list = [] # Atomic proposition behavior
        self.premise_constraints = []    # Premises must be true
        self.conclusion_constraints = [] # At least one conclusion false

        # Z3 solving
        self.z3_model = self.evaluate_constraints()  # None if unsat
```

*Full implementation: [`model_checker/model.py`](../../Code/src/model_checker/model.py)*

ModelDefaults manages the complete constraint solving process. It categorizes constraints by type (frame, model, premise, conclusion) for debugging and tracking purposes, then passes them to Z3's SMT solver. The `evaluate_constraints()` method aggregates all constraints and either returns a satisfying model (proving the argument invalid) or None (suggesting validity). This separation of concerns allows theories to focus on constraint generation while the base class handles the solving mechanics.

### ModelConstraints

Bridges syntax to semantics by generating constraints:

```python
class ModelConstraints:
    """Links parsed syntax to semantic constraints."""

    def __init__(self, settings, syntax, semantics, proposition_class):
        self.settings = settings
        self.syntax = syntax
        self.semantics = semantics        # Instantiated semantic theory
        self.proposition_class = proposition_class  # Class for propositions

        # Instantiate operators with semantics
        self.operators = self.instantiate_operators()  # Operator instances

        # Update sentences with semantic operators
        for sentence in self.syntax.all_sentences.values():
            sentence.update_objects(self)  # Link operators to semantics
```

*Full implementation: [`model_checker/model.py`](../../Code/src/model_checker/model.py)*

ModelConstraints orchestrates the semantic interpretation process. It instantiates operator classes with the chosen semantic theory, then updates all parsed sentences to use these semantic-aware operators. This separation allows the same syntactic structure to be interpreted by different semantic theories.

## Example: Logos Semantic Pipeline

### Theory Implementation Example: LogosSemantics

As an example, LogosSemantics implements hyperintensional truthmaker semantics:

```python
class LogosSemantics(SemanticDefaults):
    """Hyperintensional truthmaker semantics for Logos theory."""

    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 16,                  # Default state space size (2^16 possible states)
        'contingent': True,       # Require contingent propositions (not tautologies/contradictions)
        'non_empty': True,        # No empty verifier/falsifier sets (every prop has truthmakers)
        'non_null': True,         # No null state verifiers/falsifiers (null state is inert)
        'disjoint': True,         # Disjoint verifier/falsifier sets (no truth-value gluts)
        'max_time': 10,           # Solver timeout in seconds
    }
```

*Full implementation: [`model_checker/theory_lib/logos/semantic.py`](../../Code/src/model_checker/theory_lib/logos/semantic.py)*

These default settings embody key semantic commitments: contingency prevents trivial models, non-emptiness ensures every proposition has genuine truthmakers/falsemakers, non-null excludes the null state from verification (making it semantically inert), and disjointness enforces classical two-valued logic at the propositional level.

### Z3 Primitive Declaration

Core semantic primitives as Z3 functions:

```python
# Verification relation: state × proposition → bool
self.verify = z3.Function(
    "verify",
    z3.BitVecSort(self.N),    # State (bitvector of size N)
    syntactic.AtomSort,        # Atomic proposition (custom Z3 sort)
    z3.BoolSort()              # Returns True/False
)

# Falsification relation: state × proposition → bool
self.falsify = z3.Function(
    "falsify",
    z3.BitVecSort(self.N),    # Same signature as verify
    syntactic.AtomSort,        # But opposite semantic role
    z3.BoolSort()
)

# Possibility predicate: state → bool
self.possible = z3.Function(
    "possible",
    z3.BitVecSort(self.N),    # Which states exist in the model?
    z3.BoolSort()              # Defines the "actual" state space
)
```

These Z3 functions are uninterpreted - the solver will find specific interpretations that satisfy all constraints. The separation of `verify` and `falsify` enables hyperintensional distinctions: two formulas can be true in the same worlds but have different verifiers, capturing different "reasons" for their truth.

### Frame Constraints

Structural constraints defining the semantic framework:

```python
# Possibility is downward-closed under parthood
x, y = z3.BitVecs("frame_x frame_y", self.N)
possibility_downward_closure = ForAll(
    [x, y],
    z3.Implies(
        z3.And(
            self.possible(y),           # If y is possible
            self.is_part_of(x, y)       # and x is part of y
        ),
        self.possible(x)                # then x is possible
    )
)

# Main world must be possible
self.main_world = z3.BitVec("w", self.N)
main_world_constraint = self.is_world(self.main_world)  # Ensures w is maximal

self.frame_constraints = [
    possibility_downward_closure,
    main_world_constraint
]
```

The downward closure constraint embodies a key principle: if a complex state is possible, all its parts must be possible too. This prevents "impossible parts of possible wholes" and ensures the possibility relation respects mereological structure. The main world constraint guarantees we evaluate formulas at a genuine (maximal) world, not an arbitrary state.

### Truth/Falsity Evaluation

Extended verification and falsification for complex formulas:

```python
def true_at(self, world, sentence, eval_point):
    """Sentence is true at world if some part verifies it."""
    x = z3.BitVec("true_at_x", self.N)
    return Exists(
        x,
        z3.And(
            self.is_part_of(x, world),              # x is part of the world
            self.extended_verify(x, sentence, eval_point)  # x verifies the sentence
        )
    )

def false_at(self, world, sentence, eval_point):
    """Sentence is false at world if some part falsifies it."""
    x = z3.BitVec("false_at_x", self.N)
    return Exists(
        x,
        z3.And(
            self.is_part_of(x, world),               # x is part of the world
            self.extended_falsify(x, sentence, eval_point)  # x falsifies the sentence
        )
    )
```

These methods implement the bridge between state-level verification (what states verify/falsify) and world-level truth (what's true/false at worlds). A sentence is true at a world when the world contains a verifying state - it has the "truthmaking part" within it. This allows different worlds to make the same sentence true in different ways.

### Main Evaluation Point

The evaluation context for premises and conclusions:

```python
# Define main evaluation point
self.main_point = {
    "world": self.main_world    # The world where we evaluate premises/conclusions
}

# Used in constraint generation
premise_true = self.true_at(
    self.main_point["world"],   # Evaluate at main world
    premise_sentence,            # The premise to check
    self.main_point             # Pass evaluation context
)
```

The evaluation point dictionary enables theories with multiple parameters (world, time, context) to pass evaluation contexts through the semantic machinery. For basic modal logic only "world" is needed, but temporal logics might add "time", epistemic logics might add "agent", etc.

## LogosProposition Class

### Role in Constraining

LogosProposition constrains how atomic sentence letters are interpreted:

```python
class LogosProposition(PropositionDefaults):
    """Constrains atomic proposition interpretation."""

    def __init__(self, sentence, model_structure, eval_world='main'):
        super().__init__(sentence, model_structure)
        self.eval_world = (
            model_structure.main_point["world"]  # Default: evaluate at main world
            if eval_world == 'main'
            else eval_world                      # Or at specified world
        )
        self.verifiers, self.falsifiers = self.find_proposition()  # Compute truth-makers
```

*Full implementation: [`model_checker/theory_lib/logos/proposition.py`](../../Code/src/model_checker/theory_lib/logos/proposition.py)*

LogosProposition initialization demonstrates the evaluation context mechanism. The `eval_world` parameter allows propositions to be evaluated at different worlds - defaulting to the main world for premises/conclusions, but supporting evaluation at alternative worlds for modal operators. The immediate computation of verifier/falsifier sets during initialization enables efficient caching - each proposition's truthmakers are calculated once and reused throughout the semantic evaluation.

### Verifier/Falsifier Computation

Finding exact verifier and falsifier sets:

```python
def find_proposition(self):
    """Compute verifier and falsifier sets for the sentence."""
    if self.sentence.sentence_letter:  # Is this an atomic sentence?
        # Atomic sentence - extract from Z3 model
        return self.find_exact_proposition()  # Query Z3 for verify/falsify values
    else:
        # Complex sentence - use operator method
        operator = self.sentence.operator      # The logical connective
        arguments = self.sentence.arguments    # Sub-sentences
        return operator.find_verifiers_and_falsifiers(
            self.model_structure,
            *arguments,                        # Pass all arguments
            self.eval_world                    # At this evaluation world
        )
```

This method embodies the compositional principle: atomic sentences get their verifiers/falsifiers directly from the model (via Z3), while complex sentences compute them from their parts according to the operator's semantic rules. This separation allows new operators to be added without modifying the core proposition logic.

### Proposition Constraints Hierarchy

Constraints are applied in layers based on settings:

```python
def proposition_constraints(self, sentence_letter):
    """Generate constraints based on semantic settings."""

    # Always applied - enforce classical logic
    classical = get_classical_constraints()  # No gaps, no gluts, fusion closure

    # Setting-dependent constraints
    constraints = classical.copy()

    if self.settings.get('contingent', False):
        constraints.extend(get_contingent_constraints())  # Not tautology/contradiction

    if self.settings.get('non_empty', False):
        constraints.extend(get_non_empty_constraints())   # Has verifiers & falsifiers

    if self.settings.get('disjoint', False):
        constraints.extend(get_disjoint_constraints())    # No state both verifies & falsifies

    if self.settings.get('non_null', False):
        constraints.extend(get_non_null_constraints())    # Null state doesn't verify/falsify

    return constraints
```

This layered approach lets users control the semantic properties of their models. Classical constraints ensure basic logical coherence, while optional constraints add increasingly restrictive conditions. The modular design means new constraint types can be added without modifying existing code.

### Settings Interaction

Each constraint type serves a specific purpose:

```
┌───────────────────────────────────────────────────────────────────────────────┐
│                     Constraint Types and Their Effects                        │
├──────────────────┬──────────────────────────────────┬─────────────────────────┤
│ Constraint Type  │ Formal Statement                 │ Semantic Effect         │
├──────────────────┼──────────────────────────────────┼─────────────────────────┤
│ **Classical**    │                                  │                         │
│ Verifier fusion  │ x⊩⁺A ∧ y⊩⁺A → (x|y)⊩⁺A           │ Verifiers upward closed │
│ Falsifier fusion │ x⊩⁻A ∧ y⊩⁺A → (x|y)⊩⁺A           │ Falsifiers upward closed│
│ No gluts         │ x⊩⁺A ∧ y⊩⁻A → ¬(x∘y)             │ Truth is consistent     │
│ No gaps          │ poss(x) → ∃y(x∘y ∧ (x⊩⁺A ∨ y⊩⁻A))│ Truth is complete       │
├──────────────────┼──────────────────────────────────┼─────────────────────────┤
│ **Contingent**   │                                  │                         │
│ Has poss verifier│ ∃x(poss(x) ∧ x⊩⁺A)               │ Not always false        │
│ Has poss falsifie│ ∃x(poss(x) ∧ x⊩⁻A)               │ Not always true         │
├──────────────────┼──────────────────────────────────┼─────────────────────────┤
│ **Non-empty**    │                                  │                         │
│ Some verifier    │ ∃x(x⊩⁺A)                         │ Has truthmakers         │
│ Some falsifier   │ ∃x(x⊩⁻A)                         │ Has falsemakers         │
├──────────────────┼──────────────────────────────────┼─────────────────────────┤
│ **Disjoint**     │                                  │                         │
│ No overlap       │ ∀x,y,z: ((x⊩⁺A ∨ x⊩⁻A) ∧         │ No common parts between │
│ for distinct     │          (y⊩⁺B ∨ y⊩⁻B) ∧         │ verifier and falsifiers │
│ sentence letters │          (z⊑x ∧ z⊑y) → z=□)      │                         │
├──────────────────┼──────────────────────────────────┼─────────────────────────┤
│ **Non-null**     │                                  │                         │
│ No null verifier │ ¬(□⊩A)                           │ Null state is inert     │
│ No null falsifier│ ¬(□⊩A)                           │ for all propositions    │
└──────────────────┴──────────────────────────────────┴─────────────────────────┘
```

*Implementation of constraint generators: [`model_checker/theory_lib/logos/proposition.py#proposition_constraints`](../../Code/src/model_checker/theory_lib/logos/proposition.py)*

## Operator Implementation Pattern

The number and type of semantic methods an operator implements depends on the semantic framework:

- **Extensional theories**: Truth evaluated directly (no evaluation point) - may use just `evaluate()`
- **Unimodal theories**: Truth evaluated at worlds - use `true_at()`
- **Bimodal theories**: Truth evaluated at world time pairs - use `true_at()`
- **Unilateral hyperintensional**: Truth plus verification - use `true_at()` and `extended_verify()`
- **Bilateral hyperintensional**: Truth plus verification/falsification - use all four methods:
  - `true_at()` - determines truth at worlds
  - `false_at()` - determines falsity at worlds
  - `extended_verify()` - identifies verifying states
  - `extended_falsify()` - identifies falsifying states

### Operator Base Class

The full operator interface supports bilateral hyperintensional semantics (like Logos), but theories can use subsets:

```python
class Operator:
    """Base class for logical operators."""

    name = None        # LaTeX name like "\\wedge"
    arity = None       # Number of arguments (0, 1, or 2)
    primitive = True   # False for defined operators

    def __init__(self, semantics):
        self.semantics = semantics  # Link to semantic theory

    # Methods used depend on semantic framework:

    # Intensional methods (truth at worlds)
    def true_at(self, world, sentence, eval_point):
        """When is the sentence true at a world?"""
        # For modal, temporal, or world-based semantics
        # eval_point contains evaluation parameters (world, time, etc.)

    def false_at(self, world, sentence, eval_point):
        """When is the sentence false at a world?"""
        # Can default to: not true_at()
        # eval_point passed through for consistency

    # Hyperintensional methods (verification by states)
    def extended_verify(self, state, *args, eval_point):
        """When does a state verify the sentence?"""
        # For truthmaker semantics (unilateral or bilateral)

    def extended_falsify(self, state, *args, eval_point):
        """When does a state falsify the sentence?"""
        # Only for bilateral truthmaker semantics
```

#### Required Methods by Theory Type

- **Extensional theories**: May define custom `evaluate()` method
- **Classical/Modal logic**: Requires `true_at()` (and optionally `false_at()`)
- **Temporal/Bimodal logic**: Requires `true_at()` with multi-parameter eval_point
- **Unilateral truthmaker**: Requires `true_at()` and `extended_verify()`
- **Bilateral truthmaker**: Requires all four methods

### Framework Examples

Different semantic frameworks use different method subsets:

```python
# Classical/Modal logic - intensional only
class ClassicalAndOperator(Operator):
    def true_at(self, world, sentence, eval_point):
        # A∧B true at w iff both true at w
        return z3.And(
            self.semantics.true_at(world, sentence.arguments[0], eval_point),
            self.semantics.true_at(world, sentence.arguments[1], eval_point)
        )
    # false_at defaults to negation of true_at

# Bimodal logic - world and time
class BimodalUntilOperator(Operator):
    def true_at(self, world, sentence, eval_point):
        # A U B true at (w,t) iff B becomes true with A holding until then
        current_time = eval_point["time"]
        t = z3.Int("until_t")
        
        # ∃t' ≥ t: B true at (w,t') ∧ ∀t'' ∈ [t,t'): A true at (w,t'')
        return z3.Exists(t, z3.And(
            t >= current_time,
            self.semantics.true_at(world, sentence.arguments[1], 
                                 {"world": world, "time": t}),
            z3.ForAll(z3.Int("t_prime"), 
                z3.Implies(
                    z3.And(current_time <= t_prime, t_prime < t),
                    self.semantics.true_at(world, sentence.arguments[0],
                                         {"world": world, "time": t_prime})
                ))
        ))
        # Other bimodal operators omitted for brevity

# Unilateral truthmaker semantics (e.g., some versions of relevance logic)
class UnilateralAndOperator(Operator):
    def true_at(self, world, sentence, eval_point):
        # Truth at worlds follows classical pattern
        return z3.And(
            self.semantics.true_at(world, sentence.arguments[0], eval_point),
            self.semantics.true_at(world, sentence.arguments[1], eval_point)
        )

    def extended_verify(self, state, arg1, arg2, eval_point):
        # State verifies A∧B iff it contains both an A-verifier and B-verifier
        x = z3.BitVec("uni_and_x", self.semantics.N)
        y = z3.BitVec("uni_and_y", self.semantics.N)
        return z3.Exists([x, y], z3.And(
            self.semantics.is_part_of(x, state),
            self.semantics.is_part_of(y, state),
            self.semantics.extended_verify(x, arg1, eval_point),
            self.semantics.extended_verify(y, arg2, eval_point)
        ))
```

The `eval_point` parameter is a dictionary that can contain different evaluation parameters depending on the semantic theory:
- **Modal logic**: `{"world": w}` - just the current world
- **Temporal logic**: `{"world": w, "time": t}` - world and time point
- **Epistemic logic**: `{"world": w, "agent": a}` - world and agent perspective
- **Context-dependent**: `{"world": w, "context": c}` - world and context parameter

*For complete operator implementations, see:*
- *Modal operators: [`model_checker/theory_lib/logos/modal/operators.py`](../../Code/src/model_checker/theory_lib/logos/modal/operators.py)*
- *Temporal operators: [`model_checker/theory_lib/bimodal/operators.py`](../../Code/src/model_checker/theory_lib/bimodal/operators.py)*
- *Extensional operators: [`model_checker/theory_lib/logos/extensional/operators.py`](../../Code/src/model_checker/theory_lib/logos/extensional/operators.py)*

### Bilateral Hyperintensional Pattern (Logos)

The Logos theory uses all four methods to implement bilateral truthmaker semantics. Here are three representative operators showing different patterns:

```python
class NegationOperator(Operator):
    name = "\\neg"
    arity = 1
    
    def extended_verify(self, state, arg, eval_point):
        """State verifies ¬A iff it falsifies A."""
        return self.semantics.extended_falsify(state, arg, eval_point)
        
    def extended_falsify(self, state, arg, eval_point):
        """State falsifies ¬A iff it verifies A."""
        return self.semantics.extended_verify(state, arg, eval_point)

class AndOperator(Operator):
    name = "\\wedge"
    arity = 2

    def extended_verify(self, state, arg1, arg2, eval_point):
        """State verifies A∧B iff it's the fusion of an A-verifier
        and a B-verifier."""
        x = z3.BitVec("and_x", self.semantics.N)
        y = z3.BitVec("and_y", self.semantics.N)
        return Exists(
            [x, y],
            z3.And(
                state == self.semantics.fusion(x, y),        # state = x|y
                self.semantics.extended_verify(x, arg1, eval_point),  # x verifies A
                self.semantics.extended_verify(y, arg2, eval_point)   # y verifies B
            )
        )
    
    def extended_falsify(self, state, arg1, arg2, eval_point):
        """State falsifies A∧B iff it falsifies A, falsifies B, or is the 
        fusion of an A-falsifier and a B-falsifier."""
        sem = self.semantics
        x = z3.BitVec("and_falsify_x", sem.N)
        y = z3.BitVec("and_falsify_y", sem.N)
        return z3.Or(
            sem.extended_falsify(state, arg1, eval_point),  # state falsifies A
            sem.extended_falsify(state, arg2, eval_point),  # state falsifies B
            Exists(
                [x, y],
                z3.And(
                    state == sem.fusion(x, y),          # state = x|y
                    sem.extended_falsify(x, arg1, eval_point),  # x falsifies A
                    sem.extended_falsify(y, arg2, eval_point)   # y falsifies B
                )
            )
        )

class CounterfactualOperator(Operator):
    name = "\\boxright"
    arity = 2
    
    def extended_verify(self, state, arg1, arg2, eval_point):
        """A state verifies A □→ B at a world iff the state is that world
        and A □→ B is true at that world."""
        world = eval_point["world"]
        return z3.And(
            state == world,
            self.true_at(arg1, arg2, eval_point)
        )
    
    def true_at(self, arg1, arg2, eval_point):
        """A □→ B is true at world w iff for all verifiers x of A and 
        all worlds u such that u is an x-alternative to w, B is true at u."""
        semantics = self.semantics
        N = semantics.N
        x = z3.BitVec("t_cf_x", N)
        u = z3.BitVec("t_cf_u", N)
        return ForAll(
            [x, u],
            z3.Implies(
                z3.And(
                    semantics.extended_verify(x, arg1, eval_point),  # x verifies A
                    semantics.is_alternative(u, x, eval_point["world"])  # u is x-alternative to w
                ),
                semantics.true_at(arg2, {"world": u})      # B true at u
            )
        )
```

These three operators illustrate key patterns in bilateral truthmaker semantics:
- **Negation** shows the simplest case: verification and falsification swap roles
- **Conjunction** demonstrates asymmetric fusion: verifiers require fusion (both parts needed), falsifiers distribute (either part suffices)
- **Counterfactual** combines hyperintensional state-level verification with intensional world-level evaluation, showing how the framework supports hybrid operators

### Finding Verifiers/Falsifiers

Operators compute exact verifier/falsifier sets:

```python
def find_verifiers_and_falsifiers(self, model_structure, *args):
    """Find all verifiers and falsifiers for the operator."""
    semantics = model_structure.semantics
    z3_model = model_structure.z3_model

    # Collect possible verifiers
    verifiers = {
        state for state in model_structure.possible_states
        if z3_model.evaluate(  # Check if constraint is satisfied
            self.extended_verify(state, *args, eval_point)
        )
    }

    # Collect possible falsifiers
    falsifiers = {
        state for state in model_structure.possible_states
        if z3_model.evaluate(  # Check if constraint is satisfied
            self.extended_falsify(state, *args, eval_point)
        )
    }

    return verifiers, falsifiers  # Sets of bit vectors
```

Note that `z3_model.evaluate()` may not work correctly when the constraint involves existential quantification over functions, as Z3 doesn't always store witnesses for such quantifiers in the model. In these cases, the framework uses alternative methods for extracting verifier/falsifier information, typically by iterating through possible states and checking constraints directly.

### Print Methods

Operators define visualization for results:

```python
def print_method(self, sentence, eval_point, indent, colors):
    """Display evaluation details for the operator."""
    # Default: show general evaluation
    self.general_print(sentence, eval_point, indent, colors)

    # Modal operators might show alternative worlds
    self.print_over_worlds(sentence, eval_point, alt_worlds, indent, colors)

    # Temporal operators might show time sequences
    self.print_over_times(sentence, eval_point, times, indent, colors)
```

Print methods enable rich visualization of semantic evaluation. Different operator types can provide specialized views: modal operators show truth across possible worlds, temporal operators display evolution over time, and hyperintensional operators reveal verifier/falsifier structure.

## Subtheory Architecture

### Operator Registry System

LogosOperatorRegistry manages modular operator loading:

```python
class LogosOperatorRegistry:
    """Central registry for all Logos operators."""

    def __init__(self):
        self.operators = OperatorCollection()
        self.loaded_subtheories = set()

    def load_subtheories(self, subtheory_names):
        """Dynamically load requested subtheories."""
        for name in subtheory_names:
            if name not in self.loaded_subtheories:
                self._load_subtheory(name)
                self.loaded_subtheories.add(name)
```

*Full implementation: [`model_checker/theory_lib/logos/registry.py`](../../Code/src/model_checker/theory_lib/logos/registry.py)*

The operator registry provides centralized management of logical operators across subtheories. It maintains a single `OperatorCollection` that maps operator names to their implementations, tracks which subtheories have been loaded to prevent duplication, and handles the dynamic import of operator modules. This design allows theories to be composed from modular pieces - you can load just the operators you need (e.g., only modal operators for a modal logic example) rather than loading the entire theory library.

### Dynamic Loading

Subtheories are loaded on demand:

```python
def _load_subtheory(self, name):
    """Load operators from a subtheory module."""
    # Import subtheory module
    module = importlib.import_module(
        f'model_checker.theory_lib.logos.{name}.operators'
    )

    # Get operator list
    if hasattr(module, 'OPERATORS'):
        operators = module.OPERATORS
    elif hasattr(module, '__all__'):
        operators = [
            getattr(module, op_name)
            for op_name in module.__all__
        ]

    # Add to collection
    self.operators.add_operator(operators)
```

The dynamic loading system enables modular theory construction. Rather than loading all operators upfront, theories can be assembled from reusable components. This improves performance (fewer constraints to generate) and enables experimentation with operator combinations.

### Dependency Management

Subtheories can declare dependencies:

```python
# In modal/operators.py
DEPENDENCIES = []  # No dependencies

# In counterfactual/operators.py
DEPENDENCIES = ['modal']  # Requires modal operators (Box, Diamond)

# Registry loads dependencies automatically
def _load_subtheory(self, name):
    # Load dependencies first
    for dep in module.DEPENDENCIES:
        if dep not in self.loaded_subtheories:
            self._load_subtheory(dep)  # Recursive loading
```

This ensures operators are always available when needed. If you load 'counterfactual', it automatically loads 'modal' first, preventing missing operator errors. The dependency graph must be acyclic to avoid infinite recursion.

### Conflict Resolution

Operator name conflicts are resolved by precedence:

```python
def add_operator(self, operator):
    """Add operator, skipping if name exists."""
    if operator.name in self.operator_dictionary:
        # First loaded wins - dependencies load first
        return  # Skip duplicate registration
    self.operator_dictionary[operator.name] = operator
```

The "first wins" policy means dependencies take precedence. If both 'modal' and 'epistemic' define `\\Box`, whichever loads first provides the implementation. This allows theories to override operators by controlling load order.

## Z3 Constraint Collection

The framework collects constraints in four categories that together define valid models:

```
┌──────────────────────────────────────────────────────────┐
│                       Constraint Flow                    │
└──────────────────────────────┬───────────────────────────┘
                               │
┌──────────────────────────────┴───────────────────────────┐
│              Frame Constraints (Semantic Structure)      │
│ • Possibility downward closure                           │
│ • Main world exists and is maximal                       │
│ • Compatibility relations between states                 │
└──────────────────────────────┬───────────────────────────┘
                               │
┌──────────────────────────────┴───────────────────────────┐
│            Model Constraints (Atomic Propositions)       │
│ • Classical constraints (no gaps/gluts, fusion closure)  │
│ • Optional: contingent, non-empty, disjoint, non-null    │
│ • Applied to each atomic sentence letter                 │
└──────────────────────────────┬───────────────────────────┘
                               │
┌──────────────────────────────┴───────────────────────────┐
│              Evaluation Constraints (Truth Values)       │
│ • All premises true at main world                        │
│ • At least one conclusion false at main world            │
│ • Generates countermodel to the inference                │
└──────────────────────────────┬───────────────────────────┘
                               │
                               ▼
                        ┌─────────────┐
                        │  Z3 Solver  │
                        └─────────────┘
```

### Frame Constraints

Structural constraints from the semantic theory:

```python
# From LogosSemantics
frame_constraints = [
    possibility_downward_closure,    # Possible states closed under parts
    main_world_is_possible,          # Evaluation world exists
    compatibility_relations,         # State compatibility rules
]
```

These frame constraints are stored in the semantics object and later collected by ModelDefaults during the constraint aggregation phase. They form the foundational layer of the constraint hierarchy - all models must satisfy these structural requirements before considering proposition-specific or evaluation constraints. The frame constraints essentially define the "rules of the game" for the semantic theory, establishing how states relate to each other and which states count as legitimate evaluation points.

### Model Constraints

Constraints from atomic propositions:

```python
# For each atomic sentence letter
for letter in syntax.sentence_letters:
    constraints = proposition_class.proposition_constraints(letter)
    model_constraints.extend(constraints)

# Results in constraints like:
# - Classical logic constraints (no gaps/gluts)
# - Contingency constraints (if enabled)
# - Non-emptiness constraints (if enabled)
# - Disjointness constraints (if enabled)
```

Each atomic proposition gets its own set of constraints, scaled by the number of atomic letters. With 3 atoms and all settings enabled, this generates ~15-20 constraints per atom, totaling 45-60 model constraints. This multiplicative effect makes the `N` setting crucial for performance.

### Premise Constraints

Premises must be true at the main world:

```python
for premise in syntax.premises:
    constraint = semantics.true_at(
        semantics.main_point["world"],  # Evaluate at main world
        premise,                        # This premise sentence
        semantics.main_point           # Pass evaluation context
    )
    premise_constraints.append(constraint)
```

The requirement that all premises be true at the main world is determined by the theory's `premise_behavior` setting, which defines what counts as a countermodel. The standard behavior seeks countermodels where premises are true but conclusions false, but alternative settings could look for models where premises are false (testing consistency) or where premises have different truth values (exploring logical space).

### Conclusion Constraints

At least one conclusion must be false:

```python
# Invalidity requires some conclusion false
false_conclusions = []
for conclusion in syntax.conclusions:
    false_constraint = semantics.false_at(
        semantics.main_point["world"],  # At main world
        conclusion,                      # This conclusion
        semantics.main_point            # Evaluation context
    )
    false_conclusions.append(false_constraint)

conclusion_constraint = z3.Or(false_conclusions)  # At least one must be false
```

The requirement that at least one conclusion be false is determined by the theory's `conclusion_behavior` setting. The standard behavior (`at_least_one_false`) captures classical validity: an argument is invalid when there's a model making all premises true but at least one conclusion false. Alternative behaviors include `all_false` (all conclusions must be false) or `some_true_some_false` (mixed truth values), enabling different notions of logical consequence. The `Or` constraint here implements the default behavior of finding countermodels to classical validity.

### Settings-Based Generation

Settings control which constraints are active:

```python
def generate_constraints(settings):
    constraints = []

    # Always include frame constraints
    constraints.extend(frame_constraints)

    # Atomic proposition constraints based on settings
    for letter in sentence_letters:
        prop_constraints = generate_prop_constraints(letter, settings)
        constraints.extend(prop_constraints)

    # Evaluation constraints
    constraints.extend(premise_constraints)
    constraints.append(conclusion_constraint)

    return constraints
```

This function demonstrates the layered constraint generation approach. Frame constraints are always included as they define the semantic structure. Model constraints are generated per atomic proposition, with the specific constraints determined by settings (contingent, non_empty, etc.). Finally, evaluation constraints encode the validity checking logic. The function returns a flat list of all constraints, ready for Z3 to solve. This modular design allows easy extension - new constraint types can be added without modifying the core generation logic.

### Complete Aggregation

ModelConstraints collects all constraint types:

```python
class ModelDefaults:
    def evaluate_constraints(self):
        """Aggregate and solve all constraints."""
        solver = z3.Solver()

        # Add all constraint types with tracking
        solver.assert_and_track(frame_constraints, "frame")
        solver.assert_and_track(model_constraints, "model")
        solver.assert_and_track(premise_constraints, "premises")
        solver.assert_and_track(conclusion_constraint, "conclusions")

        # Solve with timeout
        solver.set("timeout", settings['max_time'] * 1000)
        result = solver.check()

        return solver.model() if result == z3.sat else None
```

*Full implementation: [`model_checker/model.py#ModelDefaults.solve`](../../Code/src/model_checker/model.py)*

The `solve` method is the culmination of the semantic pipeline. It creates a fresh Z3 solver, adds all constraint types with tracking labels (useful for debugging unsat cores), sets the timeout based on user settings, and attempts to find a satisfying model. The use of `assert_and_track` allows identification of which constraint types cause unsatisfiability. If Z3 finds a model (returns `sat`), it represents a countermodel to the logical argument; if no model exists (`unsat`), the argument is valid. The timeout prevents infinite searching on complex problems.

### Debugging Techniques

Practical debugging strategies for constraint generation and solving:

```python
# 1. Constraint counting and categorization
if settings.get('verbose'):
    print(f"Frame constraints: {len(frame_constraints)}")
    print(f"Model constraints: {len(model_constraints)}")
    print(f"  - Per atom: {len(model_constraints) // len(syntax.sentence_letters)}")
    print(f"Premise constraints: {len(premise_constraints)}")
    print(f"Total: {len(all_constraints)}")

# 2. Incremental constraint checking
def debug_constraints_incrementally():
    solver = z3.Solver()

    # Add constraints in stages
    solver.push()  # Create checkpoint
    solver.add(frame_constraints)
    if solver.check() == z3.unsat:
        print("Frame constraints are unsatisfiable!")
        return

    solver.add(model_constraints)
    if solver.check() == z3.unsat:
        print("Model constraints conflict with frame!")
        solver.pop()  # Restore to checkpoint
        # Try with different settings

# 3. Unsat core analysis
if solver.check() == z3.unsat:
    solver.set(unsat_core=True)
    # Track constraints with labels
    solver.assert_and_track(frame_constraints, "frame")
    solver.assert_and_track(model_constraints, "model")

    core = solver.unsat_core()
    print(f"Conflict involves: {[str(c) for c in core]}")

# 4. Save constraints for external analysis
if settings.get('debug_constraints'):
    # Human-readable format
    with open('constraints_readable.txt', 'w') as f:
        for i, c in enumerate(frame_constraints):
            f.write(f"Frame {i}: {c}\n")

    # SMT-LIB format for other solvers
    with open('constraints.smt2', 'w') as f:
        f.write(solver.to_smt2())

# 5. Constraint simplification
def simplify_and_check(constraint):
    simplified = z3.simplify(constraint)
    print(f"Original: {constraint}")
    print(f"Simplified: {simplified}")
    if simplified == False:
        print("Constraint is unsatisfiable!")
```

**Common debugging scenarios:**

1. **"No model found" with simple formulas**: Usually means conflicting settings. Try minimal settings first (`contingent=False, non_empty=False`).
2. **Timeout on complex formulas**: Reduce `N` (fewer states = smaller search space) or increase `max_time`. Complexity > 5 often needs N ≤ 3.
3. **Unexpected model behavior**: Use `print_z3=True` to see raw Z3 model, check if `verify`/`falsify` functions match your intuition.
4. **Theory comparison differences**: Enable `debug_constraints` to compare constraint counts between theories - structural differences reveal semantic variations.

**Performance profiling:**

```python
import time

# Time each constraint type
start = time.time()
frame = semantics.frame_constraints
print(f"Frame generation: {time.time() - start:.3f}s")

start = time.time()
model = generate_model_constraints()
print(f"Model generation: {time.time() - start:.3f}s")

# Monitor solver phases
solver.set("verbose", 10)  # Z3 internal verbosity
```

Performance profiling helps identify bottlenecks in the semantic pipeline. Timing constraint generation phases reveals whether frame, model, or evaluation constraints dominate generation time. The Z3 verbose setting provides internal solver statistics showing time spent in different solving phases (preprocessing, search, conflict analysis). This information guides optimization: if model constraint generation is slow, consider reducing the number of atoms or simplifying proposition constraints; if solving is slow, try different Z3 tactics or reduce the state space size (N).

## Example Constraint Pipeline

Complete example showing all constraint types for `A ∧ B → C`:

```python
# 1. Input
premises = ["(A \\wedge B)"]  # Parentheses required for binary operators
conclusions = ["C"]
settings = {
    'N': 3,
    'contingent': True,
    'non_empty': True
}

# 2. Frame constraints (always present)
frame = [
    # Possibility downward closure
    ForAll([x,y], Implies(
        And(possible(y), is_part_of(x,y)), 
        possible(x)
    )),
    # Main world exists
    is_world(w)
]

# 3. Model constraints for A, B, C
model = [
    # Classical constraints for each letter
    ForAll([x,y], Implies(
        And(verify(x,A), verify(y,A)), 
        verify(fusion(x,y),A)
    )),
    ForAll([x,y], Implies(
        And(verify(x,A), falsify(y,A)), 
        Not(compatible(x,y))
    )),

    # Contingent constraints
    Exists([x], And(possible(x), verify(x,A))),
    Exists([x], And(possible(x), falsify(x,A))),

    # Non-empty constraints
    Exists([x], verify(x,A)),
    Exists([x], falsify(x,A)),

    # Same pattern for B and C...
]

# 4. Premise constraint
premise = [
    # (A ∧ B) is true at main world
    Exists([x], And(
        is_part_of(x,w), 
        extended_verify(x, "(A \\wedge B)", {"world": w})
    ))

    # Which expands to:
    Exists([x], And(
        is_part_of(x,w),
        Exists([y,z], And(
            x == fusion(y,z),
            verify(y,A),
            verify(z,B)
        ))
    ))
]

# 5. Conclusion constraint
conclusion = [
    # C is false at main world
    Exists([x], And(is_part_of(x,w), falsify(x,C)))
]

# Total constraints passed to Z3
all_constraints = frame + model + premise + conclusion
```

This example shows the complete constraint generation for a simple argument. The constraints use a mix of mathematical notation and Z3 syntax to illustrate the semantic conditions. Frame constraints (2) establish basic structure, model constraints (~18 with 3 atoms) define proposition behavior, premise constraints (1) require the conjunction true at the main world, and conclusion constraints (1) require C false. The expansion of the premise constraint shows how complex formulas reduce to constraints on atomic verifiers - the conjunction requires a state that fuses an A-verifier with a B-verifier. Z3 searches for variable assignments satisfying all ~22 constraints simultaneously.

## Code Examples

### Complete Semantic Setup

```python
from model_checker.theory_lib.logos import (
    LogosSemantics, LogosProposition, LogosOperatorRegistry
)

# Configure settings
settings = {
    'N': 4,                  # 2^4 = 16 possible states
    'contingent': True,      # Propositions must be genuinely contingent
    'non_empty': True,       # Every proposition needs truthmakers
    'disjoint': True         # No state both verifies and falsifies
}

# Initialize semantics
semantics = LogosSemantics(settings)

# Load operators
registry = LogosOperatorRegistry()
registry.load_subtheories(['modal', 'constitutive'])  # Load only needed subtheories
operators = registry.operators
```

This setup demonstrates the complete initialization sequence for a semantic theory. The settings configure fundamental semantic properties: `N=4` creates a state space with 16 possible combinations, while the boolean flags enforce classical behavior (no truth-value gaps or gluts). The registry pattern enables selective operator loading - here we get modal operators (□, ◇) and constitutive operators (≤_C), avoiding unnecessary constraint generation from unused subtheories.

### Z3 Primitive Usage

```python
# Direct Z3 function usage
from z3 import BitVec, Bool, Const, Implies, And, Not

# Create state and atom
state = BitVec('s', 4)               # State as 4-bit vector
atom_A = Const('A', AtomSort)        # Atomic proposition A

# Use semantic primitives
verifies_A = semantics.verify(state, atom_A)      # Does state verify A?
falsifies_A = semantics.falsify(state, atom_A)    # Does state falsify A?
is_possible = semantics.possible(state)           # Is state possible?

# Create constraint
constraint = Implies(
    And(is_possible, verifies_A),    # If state is possible and verifies A
    Not(falsifies_A)                 # Then it doesn't falsify A (no gluts)
)
```

This example shows direct manipulation of Z3 primitives, useful when implementing custom operators or debugging constraint generation. The semantic primitives (`verify`, `falsify`, `possible`) are uninterpreted Z3 functions - the solver finds specific interpretations satisfying all constraints. The constraint shown enforces the "no gluts" principle: no possible state can both verify and falsify the same proposition, ensuring classical two-valued logic at the propositional level.

### Operator Implementation Example

```python
class NegationOperator(Operator):
    name = "\\neg"
    arity = 1

    def extended_verify(self, state, arg, eval_point):
        """State verifies ¬A iff it falsifies A."""
        return self.semantics.extended_falsify(state, arg, eval_point)

    def extended_falsify(self, state, arg, eval_point):
        """State falsifies ¬A iff it verifies A."""
        return self.semantics.extended_verify(state, arg, eval_point)

    def find_verifiers_and_falsifiers(self, model_structure, arg):
        """Swap verifiers and falsifiers of argument."""
        arg_verifiers, arg_falsifiers = arg.proposition.find_proposition()
        return arg_falsifiers, arg_verifiers  # Swapped
```

*See also: [`model_checker/theory_lib/logos/subtheories/extensional/operators.py`](../../Code/src/model_checker/theory_lib/logos/subtheories/extensional/operators.py) for complete operator implementations*

Negation demonstrates the elegance of the operator pattern: it simply swaps verification and falsification. This captures the intuition that evidence against A is evidence for ¬A, and vice versa. The `find_verifiers_and_falsifiers` method efficiently computes exact verifier sets by reusing the argument's computation and swapping - no need to query Z3 again. This pattern extends to other operators: conjunction fuses verifiers, disjunction fuses falsifiers, and modal operators check across possible worlds.

### Settings Impact Example

```python
# Minimal settings - few constraints
settings_minimal = {
    'N': 3,              # Small state space (8 states)
    'contingent': False, # Allow tautologies/contradictions
    'non_empty': False   # Allow empty verifier sets
}
# Results in: Only classical constraints (fusion closure, no gaps)

# Maximal settings - many constraints
settings_maximal = {
    'N': 3,              # Same state space
    'contingent': True,  # Force genuine contingency
    'non_empty': True,   # Require truthmakers
    'disjoint': True,    # No truth-value gluts
    'non_null': True     # Null state is inert
}
# Results in: Classical + all optional constraints

# Impact on solving
# Minimal: Faster solving, more models, allows edge cases
# Maximal: Slower solving, fewer models, philosophically robust
```

Settings dramatically affect both solver performance and semantic properties. Minimal settings find models quickly but may include degenerate cases (propositions with no truthmakers, necessary truths). Maximal settings enforce philosophical desiderata but generate many more constraints - with 3 atomic propositions and all settings enabled, you get ~60 constraints versus ~15 with minimal settings. Choose settings based on your theoretical commitments and performance requirements.

### Complete Constraint Generation

```python
from model_checker.model import ModelConstraints
from model_checker.syntactic import Syntax

# Parse formulas
syntax = Syntax(premises, conclusions, operators)

# Generate constraints
model_constraints = ModelConstraints(
    settings,
    syntax,
    semantics,         # Class, not instance
    LogosProposition   # Class for atomic propositions
)

# Access different constraint types
frame = semantics.frame_constraints                    # Structural constraints
model = model_constraints.model_constraints            # Atomic prop behavior
premises = model_constraints.premise_constraints       # Premises must be true
conclusions = model_constraints.conclusion_constraints # At least one false

print(f"Total constraints: {len(frame + model + premises + [conclusions])}")
```

This example shows the complete constraint generation pipeline. ModelConstraints orchestrates the process: it instantiates the semantics with settings, updates sentences to link operators with their semantic implementations, and collects constraints from all sources. The final constraint count helps estimate solver difficulty - typical examples generate 50-200 constraints depending on formula complexity and settings. All constraints are passed to Z3 as a single satisfiability problem.

## References

### Implementation Files

**Core Framework:**
- [`model_checker/model.py`](../../Code/src/model_checker/model.py) - Base semantic classes (SemanticDefaults, PropositionDefaults, ModelDefaults) and ModelConstraints orchestration
- [`model_checker/syntactic.py`](../../Code/src/model_checker/syntactic.py) - Operator base class and interfaces

**Logos Theory Implementation:**
- [`model_checker/theory_lib/logos/semantic.py`](../../Code/src/model_checker/theory_lib/logos/semantic.py) - LogosSemantics class
- [`model_checker/theory_lib/logos/proposition.py`](../../Code/src/model_checker/theory_lib/logos/proposition.py) - LogosProposition class
- [`model_checker/theory_lib/logos/registry.py`](../../Code/src/model_checker/theory_lib/logos/registry.py) - Operator registry system

**Operator Implementations:**
- [`logos/subtheories/extensional/operators.py`](../../Code/src/model_checker/theory_lib/logos/subtheories/extensional/operators.py) - Basic logical operators (∧, ∨, ¬, →)
- [`logos/subtheories/modal/operators.py`](../../Code/src/model_checker/theory_lib/logos/subtheories/modal/operators.py) - Modal operators (□, ◇)
- [`logos/subtheories/counterfactual/operators.py`](../../Code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py) - Counterfactual operators (□→)
- [`logos/subtheories/constitutive/operators.py`](../../Code/src/model_checker/theory_lib/logos/subtheories/constitutive/operators.py) - Constitutive operators (≤_C)

### Related Documentation

- [Syntax Pipeline](SYNTAX.md) - How formulas become sentences
- [Model Finding](MODELS.md) - How constraints are solved
- [Theory Development](../../Code/docs/DEVELOPMENT.md) - Creating new theories

---

[← Syntax Pipeline](SYNTAX.md) | [Back to Methodology](README.md) | [Model Finding →](MODELS.md)
