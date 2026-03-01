# Research Report: Task #5

**Task**: 5 - logos_spatial_readme
**Started**: 2026-02-28T00:00:00Z
**Completed**: 2026-02-28T00:30:00Z
**Effort**: Medium (documentation synthesis)
**Dependencies**: None
**Sources/Inputs**:
- `/home/benjamin/Projects/Logos/Theory/typst/manual/chapters/06-spatial.typ` (source theory)
- Existing subtheory READMEs (modal, constitutive, extensional) for format patterns
- `Code/src/model_checker/theory_lib/logos/README.md` (main logos documentation)
- `Code/src/model_checker/theory_lib/logos/subtheories/README.md` (subtheory coordination)
**Artifacts**:
- This research report
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- The spatial extension defines a **state-valued metric function** (`~`) as its sole primitive, enabling hyperintensional reasoning about distances
- Five essential frame constraints (A1-A5) define coherent metric structure: extension, reflexivity, symmetry, triangle inequality, and exclusion
- Key derived concepts include **located states**, **located parts**, **internal geometry**, and **spatial profiles**
- The spatial subtheory aligns well with existing logos architecture and can follow established patterns from modal and constitutive subtheories

## Context and Scope

This research examines the spatial extension chapter from the Logos theory manual to inform the creation of a README.md file for a new spatial reasoning subtheory. The goal is to understand what spatial operators and semantics are defined, how they integrate with the existing hyperintensional framework, and what documentation structure would best serve users.

## Findings

### 1. Core Spatial Primitives

The spatial extension introduces one fundamental primitive:

| Category | Symbol | Type Signature | Reading |
|----------|--------|----------------|---------|
| Metric Function | `~` | `S -> Q -> S -> S` | metric function |

From this single primitive, all other spatial concepts are derived:

- **Metric State** `(a ~_n b)` - "a is at distance n from b"
- **Located States** - subset of S where self-distance is possible
- **Located Parts** `Loc(s)` - located parts of state s
- **Internal Geometry** `g_s` - pairwise distances within a state
- **Spatial Profile** `Pi(s,t)` - all possible distance assignments between states

### 2. Frame Constraints (Essential Axioms)

The spatial frame extends the task frame with five essential constraints:

| Label | Axiom | Interpretation |
|-------|-------|----------------|
| **A1** | `a + b <= (a ~_n b)` | Extension: metric states contain their relata |
| **A2** | If `(a ~_n a) in P`, then n = 0 | Reflexivity: only self-distance is zero |
| **A3** | `(a ~_n b) = (b ~_n a)` | Symmetry: distance is symmetric |
| **A4** | Triangle inequality | Triangularity: n <= m + k for compatible distances |
| **A5** | If `(a ~_n b) . (a ~_m b)`, then n = m | Exclusion: distance is functional |

### 3. Key Derived Concepts

**Located States** (Definition):
A state `a` is _located_ if the metric state `(a ~_0 a) in P` is possible. Located states are point-like, occupying a single position. States may also be extended across multiple locations or unlocated (abstract/qualitative).

**Located Parts** (Definition):
```
Loc(s) = {a <= s : (a ~_0 a) in P}
```
The collection of all point-like parts of a state s.

**n-Ball** (Definition):
```
B_n^s(a) = {b in Loc(s) : (a ~_m b) <= s for some m <= n}
```
The distance ball around a point in state s. B_0^s(a) is the location of a in s.

**Internal Geometry** (Definition):
```
g_s : Loc(s) x Loc(s) -> Q
g_s(a, b) = n where (a ~_n b) <= s
```
Records all pairwise distances between located parts of s.

**Spatial Profile** (Definition):
```
Pi(s, t) = {delta : Loc(s) x Loc(t) -> Q | exists w in W. delta is realized in w}
```
The set of all possible distance assignments between two states across possible worlds.

### 4. Hyperintensional Character

The spatial extension maintains hyperintensional semantics:

- **Content Distinction**: Two distance claims may be necessarily equivalent (true in same worlds) yet differ in spatial facts they concern
- **Exact Verifiers**: The metric state `(a ~_n b)` is the minimal state making the distance claim true
- **Subject-Matter Sensitivity**: Tracks what spatial facts a proposition is about

### 5. Integration with Existing Framework

The spatial extension builds on:
- **Constitutive Foundation**: Mereological structure (`<=` parthood) and state space
- **Modal Structure**: Possible states P for defining located states
- **Dynamical Foundation**: Task frame structure (S, Q, =>)

### 6. Existing README Patterns

From analyzing modal and constitutive READMEs, the standard structure is:

1. **Header** with navigation links
2. **Directory Structure** showing files
3. **Overview** (2-3 paragraphs introducing the subtheory)
4. **Subdirectories** (notebooks/, tests/)
5. **Documentation** sections (For New Users, Researchers, Developers)
6. **Operator Reference** with detailed operator documentation
7. **Examples** with categories and running instructions
8. **Semantic Theory** with truth conditions
9. **Testing and Validation** with theorem/countermodel examples
10. **Integration** with dependencies and API reference
11. **Advanced Topics** (optional)
12. **References** with academic sources

### 7. Implementation Considerations

For a spatial subtheory implementation:

**Required Components**:
- `__init__.py` - Public API exports
- `README.md` - Documentation (this task)
- `operators.py` - MetricOperator implementation
- `examples.py` - Test examples for spatial reasoning
- `tests/` - Unit tests and validation

**Z3 Implementation Challenges**:
- Metric function requires three arguments (a, n, b) -> state
- Distance values from Q (rationals or reals) need Z3 representation
- Triangle inequality requires universal quantification over compatible states
- Located state detection requires existential check on possibility

**Dependencies**:
- Extensional subtheory (basic operators)
- Constitutive subtheory (mereological relations)
- Modal subtheory (possibility for located states)

## Decisions

1. **Scope**: The README should focus on the theoretical foundation and operator semantics, with implementation details deferred to actual implementation
2. **Status**: Mark as "planned" since operators.py does not yet exist
3. **Structure**: Follow the constitutive README pattern as closest analogue (content-based relations)
4. **Examples**: Include theoretical examples but note they require implementation

## Risks and Mitigations

| Risk | Mitigation |
|------|------------|
| Metric function has unusual arity (ternary) | Document clearly; may need custom parser support |
| Distance values (Q) not in current framework | Plan for rational/real number support in Z3 |
| Triangle inequality expensive to verify | Consider approximate checking or bounds |
| Located states require modal interaction | Ensure modal subtheory dependency |

## Appendix

### Search Queries Used
- Glob: `Code/src/model_checker/theory_lib/logos/subtheories/**/README.md`
- Glob: `Code/docs/**/*.md`

### Source Files Examined
1. `/home/benjamin/Projects/Logos/Theory/typst/manual/chapters/06-spatial.typ` - Primary source
2. `Code/src/model_checker/theory_lib/logos/README.md` - Main logos documentation
3. `Code/src/model_checker/theory_lib/logos/subtheories/README.md` - Subtheory coordination
4. `Code/src/model_checker/theory_lib/logos/subtheories/modal/README.md` - Modal pattern reference
5. `Code/src/model_checker/theory_lib/logos/subtheories/constitutive/README.md` - Constitutive pattern reference

### Key Terminology Mapping

| Theory Term | Implementation Concept |
|-------------|----------------------|
| Metric function `~` | MetricOperator (ternary) |
| Metric state `(a ~_n b)` | Operator application result |
| Located state | State where self-distance is possible |
| Internal geometry | Distance function over located parts |
| Spatial profile | Set of realizable distance functions |
