# Spatial Subtheory: Hyperintensional Spatial Reasoning

[← Back to Subtheories](../README.md) | [Logos Theory →](../../README.md)

## Directory Structure

```
spatial/
├── README.md                          # This file - spatial subtheory overview
├── __init__.py                        # Module initialization (planned)
├── operators.py                       # Spatial operator definitions (planned)
├── examples.py                        # Example formulas and test cases (planned)
├── notebooks/                         # Interactive Jupyter notebooks (planned)
│   └── spatial_examples.ipynb         # Interactive spatial reasoning examples
└── tests/                             # Test suite (planned)
    └── test_spatial_examples.py       # Integration tests
```

**Implementation Status**: Planned

This subtheory is currently in the documentation phase. The theoretical foundations are complete (based on the Logos Theory spatial chapter), but the Python/Z3 implementation is pending.

## Overview

The **Spatial Subtheory** extends the Logos framework with hyperintensional semantics for reasoning about distances and spatial relationships. Just as the constitutive foundation distinguishes propositions that agree in truth-value but differ in subject-matter, the spatial extension distinguishes distance claims that are necessarily equivalent yet differ in the spatial facts they concern.

The key innovation is a **state-valued metric function** that makes distance information part of the hyperintensional content of propositions. Two claims may be necessarily equivalent---true in exactly the same possible worlds---yet differ in subject-matter. Similarly, two distance claims may agree on whether objects are at a given distance, yet differ in what spatial facts they concern.

The spatial extension builds on the mereological structure from the constitutive subtheory and the modal structure from the modal subtheory, providing the semantic foundation for fine-grained spatial reasoning that goes beyond possible-worlds semantics.

## Subdirectories

### notebooks/ (Planned)

Interactive Jupyter notebooks will demonstrate spatial operators through hands-on examples, including metric states, located parts, internal geometries, and spatial profiles. These will visualize how spatial relationships vary across possible worlds while maintaining hyperintensional distinctions.

### tests/ (Planned)

Test suite will include examples validating the five frame constraints (extension, reflexivity, symmetry, triangularity, exclusion) and derived concepts (located states, n-balls, spatial profiles).

## Documentation

### For New Users

- **[Primitive Reference](#primitive-reference)** - The metric function and its type signature
- **[Frame Constraints](#frame-constraints)** - Five essential constraints defining coherent spatial structure
- **[Derived Concepts](#derived-concepts)** - Located states, located parts, internal geometry, spatial profiles

### For Researchers

- **[Semantic Theory](#semantic-theory)** - Hyperintensional approach to spatial content
- **[Theoretical Background](#theoretical-background)** - Foundation in truthmaker semantics
- **[Academic References](#references)** - Primary sources and related work

### For Developers

- **[Implementation Status](#implementation-status)** - Current development state
- **[Implementation Challenges](#implementation-challenges)** - Technical considerations for Z3 encoding
- **[Dependencies](#dependencies)** - Required subtheories and operators

## Primitive Reference

The spatial extension introduces one fundamental primitive from which all other spatial concepts are derived.

### Metric Function

**Symbol**: `~` (tilde)
**Name**: Metric Function
**Type Signature**: `S -> Q -> S -> S`
**Type**: Primitive operator

**Reading**: Given states `a, b : S` and distance `n : Q`, the metric state `(a ~_n b) : S` asserts "a is at distance n from b".

**Meaning**: The metric function takes two states and a distance value, returning the **metric state** that represents the minimal verifier for the distance claim. This metric state is itself a state in the state space S.

**Key Properties**:

- **State-Valued**: Unlike classical metrics that return scalar distances, this metric returns a state
- **Hyperintensional**: The metric state `(a ~_n b)` is the exact verifier for the distance claim
- **Ternary Structure**: Requires three arguments: two states and a distance value

**Derived Notation**:

| Notation | Type | Reading |
|----------|------|---------|
| `(a ~_n b)` | `S` | "a is at distance n from b" (metric state) |
| `A ⊆ S` | Set | Located states |
| `Loc(s)` | Set | Located parts of s |
| `g_s` | Function | Internal geometry of s |
| `Π(s, t)` | Set | Spatial profile for s and t |

## Frame Constraints

A **spatial frame** extends a task frame with the metric function satisfying five essential constraints. These constraints define what it means to have a coherent spatial structure.

### Essential Frame Constraints

| Label | Axiom | Interpretation |
|-------|-------|----------------|
| **A1** | `a ⊔ b ⊑ (a ~_n b)` | **Extension**: Metric states contain their relata as parts |
| **A2** | If `(a ~_n a) ∈ P`, then `n = 0` | **Reflexivity**: Only self-distance can be zero |
| **A3** | `(a ~_n b) = (b ~_n a)` | **Symmetry**: Distance is symmetric |
| **A4** | If `(a ~_n b) ∘ (b ~_m c) ∘ (a ~_k c)`, then `n ≤ m + k` | **Triangularity**: Triangle inequality holds |
| **A5** | If `(a ~_n b) ∘ (a ~_m b)`, then `n = m` | **Exclusion**: Distance is functional (unique) |

### Constraint Details

#### A1: Extension

```
a ⊔ b ⊑ (a ~_n b)
```

The metric state `(a ~_n b)` contains both `a` and `b` as mereological parts. Without this constraint, distance claims would be disconnected from the objects they concern. This ensures that the subject-matter of a distance claim includes the entities whose distance is being measured.

#### A2: Reflexivity

```
If (a ~_n a) ∈ P, then n = 0
```

If it is possible for a state to have some distance from itself, that distance must be zero. This captures the intuition that an object is always at zero distance from itself. Note that not all states need to have self-distances (abstract states may be unlocated).

#### A3: Symmetry

```
(a ~_n b) = (b ~_n a)
```

The metric state for "a at distance n from b" is identical to the metric state for "b at distance n from a". Distance is symmetric---it doesn't matter which object we measure from.

#### A4: Triangularity (Triangle Inequality)

```
If (a ~_n b) ∘ (b ~_m c) ∘ (a ~_k c), then n ≤ m + k
```

The fundamental coherence condition for metric structure. If three distance claims are compatible (can coexist), then they must satisfy the triangle inequality. This prevents geometrically impossible configurations.

#### A5: Exclusion

```
If (a ~_n b) ∘ (a ~_m b), then n = m
```

If two distance claims about the same pair of states are compatible, they must assign the same distance. This ensures distance is functional---two states have at most one distance in any possible state.

## Derived Concepts

All spatial concepts beyond the metric function are derived from the primitive together with mereological structure (⊑) and modal structure (P).

### Located States

**Definition**: A state `a` is **located** if the metric state `(a ~_0 a) ∈ P` is possible.

```
Located states = {a ∈ S : (a ~_0 a) ∈ P}
```

**Interpretation**: Located states are point-like---they occupy a single position in space. A state being located means it is possible for it to have zero distance from itself, which requires it to have a definite spatial position.

**Three Categories of States**:

1. **Located states**: Point-like, occupy a single position
2. **Extended states**: Spread across multiple locations (have multiple located parts)
3. **Unlocated states**: Abstract or purely qualitative, without spatial position

### Located Parts

**Definition**: Given a state `s`, the **located parts** of `s` are all point-like parts of `s`:

```
Loc(s) = {a ⊑ s : (a ~_0 a) ∈ P}
```

**Interpretation**: `Loc(s)` collects all the point-like parts of a state. For an extended body, this would be all the individual points that make up the body. For an unlocated abstract state, `Loc(s)` may be empty.

### n-Ball (Distance Ball)

**Definition**: The **n-ball around `a`** in state `s` is:

```
B_n^s(a) = {b ∈ Loc(s) : (a ~_m b) ⊑ s for some m ≤ n}
```

**Special Case**: `B_0^s(a)` is the **location of `a` in `s`**---all states located at the same point as `a` within `s`.

**Interpretation**: The n-ball captures all points within distance n of a given point, relative to a particular state. This provides a neighborhood structure for spatial reasoning.

### Internal Geometry

**Definition**: The **internal geometry** of a state `s` is the function `g_s : Loc(s) × Loc(s) → Q` defined by:

```
g_s(a, b) = n where (a ~_n b) ⊑ s
```

**Interpretation**: The internal geometry records all pairwise distances between located parts of a state. This captures the complete metric structure internal to a state---how its parts are spatially arranged relative to each other.

**Properties**:

- The internal geometry is a standard metric on `Loc(s)`
- It inherits reflexivity, symmetry, and triangle inequality from the frame constraints
- Different states may have the same located parts but different internal geometries

### Spatial Profile

**Definition**: The **spatial profile** for states `s` and `t` is:

```
Π(s, t) = {δ : Loc(s) × Loc(t) → Q | ∃w ∈ W. δ is realized in w}
```

where `δ` is **realized in** world `w` iff for all `a ∈ Loc(s)` and `b ∈ Loc(t)`:

```
(a ~_δ(a,b) b) ⊑ w
```

**Interpretation**: The spatial profile collects all possible distance assignments between the located parts of two states across all possible worlds. Each element of the profile represents a way that `s` and `t` could be spatially related.

**Key Insight**: A single scalar distance does not suffice to describe the spatial relationship between extended bodies. Two bodies have many located parts, and their relationship involves all pairwise distances. The spatial profile captures this complete structure.

### Hyperintensional Character

The spatial extension maintains hyperintensional semantics:

**Content Distinction**: Two distance claims may be necessarily equivalent (true in the same possible worlds) yet differ in the spatial facts they concern. The metric state `(a ~_n b)` represents the **exact verifier** for the distance claim---a minimal state that makes the claim true without extraneous content.

**Subject-Matter Sensitivity**: The spatial profile tracks what spatial facts a proposition is about, enabling fine-grained distinctions that possible-worlds semantics cannot capture.

**Hyperintensional Spatial Profiles**: Two states may be necessarily at the same distance (in all worlds where they coexist), yet differ in their spatial profiles because different internal configurations are possible in different worlds.

## Semantic Theory

### Theoretical Background

The spatial extension builds on truthmaker semantics, providing hyperintensional spatial content:

**Truthmaker Semantics Foundation**: Following Fine (2017) and the Logos Theory, propositions are individuated by their verifiers and falsifiers, not just their truth-values across possible worlds.

**Exact Verification**: The metric state `(a ~_n b)` is the **exact verifier** for the distance claim---it makes the claim true without including extraneous information. This enables subject-matter tracking.

**State-Valued Metrics**: Unlike classical metrics that return scalar values, the state-valued metric returns states. This embeds spatial information directly into the hyperintensional content structure.

### Integration with Logos Framework

The spatial extension integrates with other Logos components:

**Mereological Structure**: Uses parthood (⊑) and fusion (⊔) from the constitutive foundation to define located parts and the extension constraint (A1).

**Modal Structure**: Uses possibility (P) from the modal subtheory to define located states and spatial profiles.

**Dynamical Structure**: Extends the task frame structure with spatial constraints, enabling reasoning about how spatial relationships evolve.

## Implementation Status

**Current Status**: Planned

The theoretical foundations for the spatial subtheory are complete, based on the Logos Theory spatial chapter (Chapter 6). The Python/Z3 implementation is pending.

### Planned Components

| Component | Status | Description |
|-----------|--------|-------------|
| `__init__.py` | Planned | Public API exports |
| `operators.py` | Planned | MetricOperator implementation |
| `examples.py` | Planned | Test examples for spatial reasoning |
| `tests/` | Planned | Unit tests and validation |
| `notebooks/` | Planned | Interactive demonstrations |

### Implementation Challenges

Several technical challenges will need to be addressed:

**Ternary Operator Arity**: The metric function requires three arguments (a, n, b) returning a state. This differs from the binary operators in other subtheories and may require custom parser support.

**Distance Values (Q)**: The distance domain Q (rationals or reals) needs appropriate Z3 representation. Options include Z3 Reals or bounded integers.

**Triangle Inequality Verification**: Constraint A4 requires universal quantification over compatible states. Efficient verification strategies may be needed.

**Located State Detection**: Checking whether `(a ~_0 a) ∈ P` requires existential reasoning about possibility.

## Dependencies

The spatial subtheory depends on:

### Required Subtheories

| Subtheory | Required Operators | Usage |
|-----------|-------------------|-------|
| **Extensional** | ⊑ (parthood), ⊔ (fusion) | Mereological structure in constraints A1, derived concepts |
| **Constitutive** | State space structure | Foundation for hyperintensional content |
| **Modal** | P (possibility) | Located states, spatial profiles |

### Conceptual Dependencies

- **Mereological Relations**: Parthood for defining located parts, extension constraint
- **Fusion Operation**: For the extension constraint (A1)
- **Possibility**: For defining located states and spatial profiles
- **State Space**: For the state-valued metric function

## References

### Primary Sources

- Brast-McKie, B. *Logos: A Hyperintensional Semantic Framework*. Chapter 6: Spatial Extension.
- Fine, K. (2017) ["A Theory of Truthmaker Content I"](https://link.springer.com/article/10.1007/s10992-016-9413-y), *Journal of Philosophical Logic*.
- Fine, K. (2017) ["A Theory of Truthmaker Content II"](https://doi.org/10.1007/s10992-016-9419-5), *Journal of Philosophical Logic*.

### Related Resources

- **[Constitutive Subtheory](../constitutive/)** - Hyperintensional content relations
- **[Modal Subtheory](../modal/)** - Necessity and possibility operators
- **[Extensional Subtheory](../extensional/)** - Basic logical operators
- **[Logos Theory](../../README.md)** - Complete framework documentation

---

[← Back to Subtheories](../README.md) | [Logos Theory →](../../README.md)
