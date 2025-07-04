# From Syntax to Semantics: The Complete Model Checking Process

## Executive Summary

This document traces the complete journey through the ModelChecker's **three-fold programmatic semantic methodology**: **Syntax → Truth-Conditions → Extensions**. We examine how sentence objects become Z3 constraints and then concrete models, comparing how two-phase and single-phase architectures handle the transitions between these three fundamental levels.

## Table of Contents

1. [Overview: The Model Checking Pipeline](#overview-the-model-checking-pipeline)
2. [Stage 1: Syntactic Input and Parsing](#stage-1-syntactic-input-and-parsing)
3. [Stage 2: Recursive Formula Decomposition](#stage-2-recursive-formula-decomposition)
4. [Stage 3: Constraint Generation](#stage-3-constraint-generation)
5. [Stage 4: Semantic Primitive Grounding](#stage-4-semantic-primitive-grounding)
6. [Stage 5: Z3 Constraint Construction](#stage-5-z3-constraint-construction)
7. [Stage 6: Model Finding and Extension Assignment](#stage-6-model-finding-and-extension-assignment)
8. [Stage 7: Model Extraction and Interpretation](#stage-7-model-extraction-and-interpretation)
9. [Stage 8: Semantic Structure Construction](#stage-8-semantic-structure-construction)
10. [The Syntax-Semantics Boundary](#the-syntax-semantics-boundary)
11. [Single-Phase vs Two-Phase: Where They Diverge](#single-phase-vs-two-phase-where-they-diverge)

## Overview: The Model Checking Pipeline

The complete process transforms through the **three-fold methodology**:

```
Syntax Level                    Truth-Conditions Level           Extensions Level
------------                    ----------------------           ----------------
"¬¬A ⊢ A"         →         Z3 Constraints        →         Z3 Model         →    State Space
(sentences)      (AST)          (logical requirements)        (concrete values)    (interpretation)
```

**Key Insight**: Both architectures use the **same three-level structure** - they differ in **how information flows** between levels.

### Three-Level Transitions

1. **Syntax → Truth-Conditions**: Sentence objects → Z3 constraint formulas
2. **Truth-Conditions → Extensions**: Z3 constraints → Concrete model interpretations  
3. **Extensions → Syntax**: Model values → Syntax-level truth evaluation

**Critical Insight**: Both architectures use the same three levels. The difference is whether **circular information flow** is maintained (single-phase) or **lost** (two-phase).

## Stage 1: Syntactic Input and Parsing

### Input Format

The process begins with purely syntactic strings:

```python
premises = ['\\exclude \\exclude A', '(A \\uniwedge B)']
conclusions = ['A', '(B \\univee C)']
settings = {'N': 3, 'max_time': 5}
```

### Parsing Process

The `Syntax` class transforms strings into Abstract Syntax Trees (ASTs):

```python
class Syntax:
    def parse(self, formula_string):
        # Tokenization
        tokens = self.tokenize(formula_string)
        # "\\exclude \\exclude A" -> ['\\exclude', '\\exclude', 'A']
        
        # Recursive parsing
        ast = self.parse_tokens(tokens)
        # Returns: Sentence object with nested structure
```

### AST Structure

```python
# "¬¬A" becomes:
Sentence(
    operator=ExclusionOperator(),
    arguments=[
        Sentence(
            operator=ExclusionOperator(),
            arguments=[
                Sentence(
                    sentence_letter='A',
                    operator=None,
                    arguments=[]
                )
            ]
        )
    ]
)
```

**Key Point**: This is the **Syntax Level** of the three-fold methodology - structured representations with no truth-conditions or extensions yet. **This level is identical in both approaches.**

## Stage 2: Recursive Formula Decomposition

### The Operator Framework

Each operator defines how to decompose complex formulas:

```python
class Operator:
    def true_at(self, *arguments, eval_point):
        """Define truth conditions recursively"""
        pass
    
    def extended_verify(self, state, *arguments, eval_point):
        """Define verification conditions recursively"""
        pass
```

### Recursion Example: Exclusion

For `¬¬A`, the decomposition proceeds:

```python
# Level 1: Outer exclusion
exclude_operator.true_at(inner_formula, eval_point)
# Returns: EXISTS v. extended_verify(v, inner_formula, eval_point) AND v ⊑ world

# Level 2: Inner exclusion  
exclude_operator.extended_verify(state, atom_A, eval_point)
# Returns: Three-condition formula with Skolem functions

# Level 3: Atomic base case
atom_A.extended_verify(state, eval_point)
# Returns: verify(state, 'A')
```

**Level Transition**: The recursion begins the **Syntax → Truth-Conditions** transition, introducing logical requirements while maintaining syntactic structure. **This transition occurs identically in both approaches.**

## Stage 3: Syntax → Truth-Conditions Transition

### The First Level Transition

This is the crucial transition where **Syntax Level** sentence objects become **Truth-Conditions Level** Z3 constraints. **This transition occurs identically in both architectures:**

```python
def generate_formula_constraints(sentence, eval_point, semantics):
    if sentence.is_atomic():
        # SYNTAX -> SEMANTICS: Atomic sentences get semantic interpretation
        return generate_atomic_constraints(sentence, eval_point, semantics)
    else:
        # Recursive case: Delegate to operator
        return sentence.operator.generate_constraints(
            sentence.arguments, eval_point, semantics
        )
```

### Atomic Formula Foundation

For atomic sentence `A`:

```python
def generate_atomic_constraints(atom, eval_point, semantics):
    # Create existential quantifier over verifiers
    v = z3.BitVec(f"v_atom_{atom.id}", semantics.N)
    
    # CRITICAL MOMENT: Connect syntax to semantic primitive
    return z3.Exists([v], z3.And(
        semantics.verify(v, atom.sentence_letter),  # Semantic primitive!
        semantics.is_part_of(v, eval_point['world'])
    ))
```

**This completes the Syntax → Truth-Conditions transition**: The atomic sentence letter `'A'` becomes a Z3 constraint using the `verify` primitive. **This transition is identical in both approaches.**

## Stage 4: Truth-Conditions Level Foundations

### The Truth-Conditions Primitives

The exclusion theory defines these fundamental logical requirements as Z3 functions:

```python
# 1. Verification relation: Which states verify which atoms
self.verify = z3.Function(
    "verify",
    z3.BitVecSort(self.N),  # State
    syntactic.AtomSort,      # Atom
    z3.BoolSort()           # Truth value
)

# 2. Exclusion relation: Which states exclude which states  
self.excludes = z3.Function(
    "excludes",
    z3.BitVecSort(self.N),  # State 1
    z3.BitVecSort(self.N),  # State 2
    z3.BoolSort()           # Truth value
)

# 3. Mereological relations (defined via bitvector operations)
def is_part_of(x, y):
    return (x & y) == y

def fusion(x, y):
    return x | y
```

### Complex Operator Grounding

For exclusion operator on `¬A`:

```python
def exclusion_constraints(state, argument, eval_point):
    # Create Skolem witnesses
    h_sk = z3.Function(f"h_{id}", z3.BitVecSort(N), z3.BitVecSort(N))
    y_sk = z3.Function(f"y_{id}", z3.BitVecSort(N), z3.BitVecSort(N))
    
    # Three conditions in terms of semantic primitives
    
    # Condition 1: ∀x ∈ Ver(φ): y(x) ⊑ x ∧ h(x) excludes y(x)
    condition_1 = z3.ForAll([x], z3.Implies(
        is_verifier(x, argument),  # Recursive call for argument
        z3.And(
            is_part_of(y_sk(x), x),
            excludes(h_sk(x), y_sk(x))  # Semantic primitive!
        )
    ))
    
    # Condition 2: ∀x ∈ Ver(φ): h(x) ⊑ state
    condition_2 = z3.ForAll([x], z3.Implies(
        is_verifier(x, argument),
        is_part_of(h_sk(x), state)  # Mereological primitive!
    ))
    
    # Condition 3: state = ⋃{h(x) : x ∈ Ver(φ)}
    condition_3 = (state == fusion_of_h_values(h_sk, argument))
    
    return z3.And(condition_1, condition_2, condition_3)
```

## Stage 5: Truth-Conditions → Extensions Transition

### Constraint Assembly

All generated constraints are collected and combined:

```python
def build_z3_constraints(premises, conclusions, semantics):
    constraints = []
    
    # Frame constraints (background theory)
    constraints.extend(semantics.frame_constraints)
    
    # Premise constraints (must be true)
    for premise in premises:
        constraint = semantics.true_at(premise, semantics.main_point)
        constraints.append(constraint)
    
    # Conclusion constraints (must be false for countermodel)
    for conclusion in conclusions:
        constraint = z3.Not(semantics.true_at(conclusion, semantics.main_point))
        constraints.append(constraint)
    
    # Atom constraints (non-empty, contingent, etc.)
    for atom in get_atoms(premises + conclusions):
        constraints.extend(semantics.atom_constraints(atom))
    
    return z3.And(constraints)
```

### Frame Constraints

These define the background semantic theory:

```python
# Exclusion is symmetric
z3.ForAll([x, y], z3.Implies(
    excludes(x, y),
    excludes(y, x)
))

# Null state excludes nothing
z3.ForAll([x], z3.Not(excludes(null_state, x)))

# Mereological principles
z3.ForAll([x, y, z], z3.Implies(
    z3.And(is_part_of(x, y), is_part_of(y, z)),
    is_part_of(x, z)  # Transitivity
))
```

## Stage 6: Extensions Level Creation

### Z3 Solving Process

[See [Z3 Background: Constraint Solving](Z3_background.md#constraint-generation-and-solving)]

```python
solver = z3.Solver()
solver.add(all_constraints)  # Truth-Conditions Level input

if solver.check() == z3.sat:
    model = solver.model()   # Extensions Level output
    # Model contains concrete assignments
else:
    # No model exists (valid entailment)
```

### Extensions Level Assignment

**This is the Truth-Conditions → Extensions transition** - Z3 produces concrete values from logical requirements:

```python
# Z3 assigns extensions to all variables and functions:

# 1. Main world gets concrete value
main_world = BitVecVal(5, 3)  # Binary: 101 = {0, 2}

# 2. Verify relation gets extension
verify('A') = {BitVecVal(1, 3), BitVecVal(5, 3)}  # States {0} and {0,2} verify A
verify('B') = {BitVecVal(2, 3), BitVecVal(3, 3)}  # States {1} and {0,1} verify B

# 3. Exclusion relation gets extension  
excludes = {(1,2), (2,1), (1,4), (4,1), ...}

# 4. Skolem functions get interpretation (in two-phase)
h_sk(1) = 2
h_sk(5) = 4
# etc.
```

**Critical Point**: This transition creates the **Extensions Level** - abstract truth-conditions become concrete interpretations.

## Stage 7: Extensions Level Processing

### Extracting the Z3 Model

[See [Z3 Background: Model Extraction](Z3_background.md#model-extraction-and-interpretation)]

```python
def extract_model_data(z3_model, semantics):
    extracted = {}
    
    # Extract main world
    extracted['main_world'] = z3_model.evaluate(semantics.main_world)
    
    # Extract verify extension
    extracted['verify'] = {}
    for atom in all_atoms:
        verifiers = set()
        for state in all_states:
            if z3.is_true(z3_model.evaluate(semantics.verify(state, atom))):
                verifiers.add(state)
        extracted['verify'][atom] = verifiers
    
    # Extract exclusion pairs
    extracted['excludes'] = []
    for s1 in all_states:
        for s2 in all_states:
            if z3.is_true(z3_model.evaluate(semantics.excludes(s1, s2))):
                extracted['excludes'].append((s1, s2))
    
    return extracted
```

### Computing Derived Relations

```python
# Possible states (can be part of a world)
possible_states = []
for state in all_states:
    if z3.is_true(z3_model.evaluate(semantics.possible(state))):
        possible_states.append(state)

# Worlds (maximal possible states)
worlds = []
for state in possible_states:
    if z3.is_true(z3_model.evaluate(semantics.is_world(state))):
        worlds.append(state)
```

## Stage 8: Extensions → Syntax Transition (Attempted)

### Building the Model Structure

The final semantic structure assembles all components:

```python
class ExclusionStructure:
    def __init__(self, model_constraints, settings):
        # Get Z3 model
        self.z3_model = solve_constraints(model_constraints)
        
        # Extract semantic data
        self.main_world = extract_main_world(self.z3_model)
        self.verify_relation = extract_verify_relation(self.z3_model)
        self.exclusion_relation = extract_exclusion_relation(self.z3_model)
        
        # Compute propositions
        self.propositions = {}
        for sentence in all_sentences:
            self.propositions[sentence] = self.compute_proposition(sentence)
    
    def compute_proposition(self, sentence):
        """Find verifying states for a sentence"""
        verifiers = set()
        for state in self.all_states:
            if self.verifies(state, sentence):
                verifiers.add(state)
        return Proposition(sentence, verifiers)
```

### Truth Evaluation in the Model

```python
def evaluate_truth(sentence, world, model_structure):
    """Check if sentence is true at world in the model"""
    proposition = model_structure.propositions[sentence]
    
    # True iff some verifier is part of the world
    for verifier in proposition.verifiers:
        if is_part_of(verifier, world):
            return True
    return False
```

## The Three-Level Methodology

### Level Transitions

The three-level methodology involves specific transitions. **These transitions occur at the same points in both architectures:**

```python
# SYNTAX LEVEL: 
sentence_letter = 'A'  # Sentence object

# SYNTAX → TRUTH-CONDITIONS (same in both approaches):
constraint = semantics.verify(state, sentence_letter)  # Z3 constraint

# TRUTH-CONDITIONS LEVEL:
# 'A' now expressed as logical requirement
```

### Why These Are The Transitions

1. **Syntax Level**: Objects are sentence structures with no logical requirements
2. **Truth-Conditions Level**: Structures become logical requirements (Z3 constraints)
3. **Extensions Level**: Requirements receive concrete interpretations (Z3 models)

**Important**: These level definitions apply equally to both architectures.

### Multi-Level Transitions

For complex formulas, level transitions happen recursively in both architectures:

1. **Operators**: Syntax Level operators → Truth-Conditions Level requirements
2. **Atoms**: Syntax Level letters → Truth-Conditions Level primitives
3. **Formulas**: Syntax Level trees → Truth-Conditions Level constraint systems

**The three-level structure is preserved in both approaches.**

## Incremental vs Static: Three-Level Information Flow

### Static: Linear Three-Level Flow

[See [FINDINGS.md](../../FINDINGS.md#understanding-static-vs-incremental-model-checking)]

```python
# STATIC: Complete Constraint Generation
constraints = generate_all_constraints(premises, conclusions)
model = z3_solve(constraints)
# Solver state discarded here

# === SOLVER STATE RESET ===

# STATIC: Truth Evaluation with fresh context
propositions = compute_propositions(sentences, model)
truth_values = evaluate_truth(propositions)
```

**Problem**: Skolem function interpretations from static constraint generation are inaccessible during static evaluation.

### Incremental: Circular Three-Level Flow

[See [Incremental Modeling](../incremental_modeling.md#implementation-strategy-unified-verification-architecture)]

```python
class IncrementalProcessor:
    def process_incrementally(self, sentence, eval_point):
        # Same solver instance maintained throughout
        while not self.is_complete(sentence):
            # Generate next constraint component
            constraint = self.next_constraint_component(sentence)
            
            # Add to persistent solver
            self.solver.add(constraint)
            
            # Check satisfiability with same solver
            if self.solver.check() == unsat:
                return None  # No model exists
            
            # Extract partial model from same solver
            partial_model = self.solver.model()
            
            # Skolem interpretations remain accessible
            self.witness_store.update(partial_model)
            
            # Compute propositions using accessible witnesses
            self.update_propositions(sentence, self.witness_store)
        
        return self.final_model()
```

### Key Differences

| Aspect | Static | Incremental |
|--------|--------|--------------|
| **Three-Level Structure** | Same structure | Same structure |
| **Constraint Generation** | Batch processing | Incremental processing |
| **Solver State** | Reset between phases | Persistent throughout |
| **Witness Access** | Lost after constraint generation | Maintained throughout |
| **Processing Pattern** | Linear pipeline | Interactive feedback |
| **Skolem Functions** | Inaccessible after constraint generation | Continuously accessible |

### Where They Diverge

The architectures diverge **not in the three-level structure** but in **information flow between levels**:

```python
# Static Exclusion Operator
def extended_verify_static(self, state, argument, eval_point):
    # Create Skolem functions (will be lost)
    h_sk = z3.Function(...)
    constraints = three_conditions(h_sk, ...)
    return constraints  # No witness preservation

# Incremental Exclusion Operator  
def extended_verify_incremental(self, state, argument, eval_point):
    # Create and register witnesses
    h_witness = self.witness_store.create_witness(...)
    
    # Generate constraints
    constraints = three_conditions(h_witness, ...)
    
    # Store witness mapping for later access
    self.witness_store.register(argument, h_witness)
    
    return constraints  # Witness preserved
```

## Summary: The Three-Level Journey

### Syntax Level (Steps 1-3)
1. **Input**: Syntactic strings `"¬¬A ⊢ A"`
2. **Parsing**: Strings → AST structures 
3. **Decomposition**: AST → Recursive sentence objects

### Truth-Conditions Level (Steps 4-6)
4. **Constraint Generation**: **[SYNTAX → TRUTH-CONDITIONS - IDENTICAL IN BOTH APPROACHES]** Sentence objects → Z3 constraints
5. **Primitive Grounding**: Constraints expressed via verify, excludes, part-of
6. **Z3 Construction**: Individual constraints → Complete constraint system

### Extensions Level (Steps 7-9)
7. **Solving**: **[TRUTH-CONDITIONS → EXTENSIONS]** Z3 constraint system → Concrete model
8. **Extraction**: Z3 model → Accessible interpretations 
9. **Interpretation**: Model interpretations → Semantic structures

### Return to Syntax Level (Step 10)
10. **Evaluation**: **[EXTENSIONS → SYNTAX]** Semantic structures → Truth values for original sentences

The critical insight is that the **three-level structure is identical** in both approaches. The difference is in **information flow**: static enforces **linear flow** (Syntax → Truth-Conditions → Extensions) while incremental maintains **circular flow** (Syntax ⇄ Truth-Conditions ⇄ Extensions). The incremental approach preserves the **Extensions → Syntax** information flow needed for exclusion semantics, where truth evaluation requires access to witness information from the Extensions Level.
