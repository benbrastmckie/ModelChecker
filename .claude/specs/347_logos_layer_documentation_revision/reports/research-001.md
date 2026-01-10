# Research Report: Task #347

**Task**: Revise Logos layer documentation for new layer organization
**Date**: 2026-01-09
**Focus**: Analyzing existing documentation structure, FIX tags, and semantic frameworks for new layer organization

## Summary

The existing LAYER_EXTENSIONS.md contains a comprehensive FIX comment (lines 9-36) specifying the new layer organization with five layers: Constitutive, Causal, Epistemic, Normative, and Agential. The FIX tag provides detailed hyperintensional semantics for the Constitutive Layer and intensional semantics for the Causal Layer, with placeholders for remaining layers. The GLOSSARY.md uses the old layer numbering (0-3) and needs updating to match the new five-layer organization.

## Findings

### 1. Current Layer Organization (Old)

The existing documentation uses a four-layer structure:
- **Layer 0 (Core TM)**: Boolean, modal, temporal operators
- **Layer 1 (Explanatory)**: Counterfactual, constitutive, causal operators
- **Layer 2 (Epistemic)**: Belief, probability, knowledge operators
- **Layer 3 (Normative)**: Obligation, permission, preference operators

### 2. New Layer Organization (FIX Tag)

The FIX comment in LAYER_EXTENSIONS.md specifies a five-layer structure:

1. **Constitutive Layer** (Foundation)
   - Frame: Complete lattice of states ordered by parthood
   - Components: Predicates, function symbols, variables, lambda abstractors, extensional connectives, propositional identity operator
   - Semantics: **Hyperintensional** - recursively defines verification and falsification relative to model, variable assignment, and state
   - Logical consequence: Restricted to propositional identity sentences evaluated at null state

2. **Causal Layer** (Extends Constitutive)
   - Frame: Adds totally ordered abelian group of times and three-place task relation with transitivity
   - Concepts: Possible states, compatible states, maximal states, world-states, world-histories
   - Semantics: **Intensional** - evaluates sentences relative to model, world-history, time, and variable assignment
   - Operators: Actuality predicate, quantifier, extensional connectives, modal operators, tense operators, counterfactual conditionals, causation operator

3. **Epistemic Layer** (Extends Causal)
   - Frame: Adds credence function assigning probabilities to state transitions
   - Operators: Belief operators, probability operators, epistemic modals, indicative conditionals
   - Status: Details to be provided later

4. **Normative Layer** (Extends Epistemic)
   - Frame: Adds value orderings over states
   - Operators: Obligation, permission, preference, normative explanation
   - Status: Details to be provided later

5. **Agential Layer** (Extends Normative)
   - Purpose: Multi-agent reasoning
   - Status: Mentioned but not detailed

### 3. Hyperintensional Semantics (Constitutive Layer)

Key semantic definitions from the FIX tag:

#### Model Components
- **Interpretation function** assigns:
  - n-place function symbols → functions from n states to a state (0-place = constants)
  - n-place predicates → ordered pairs (verifier functions, falsifier functions) where each takes n states to a state
  - Sentence letters (0-place predicates) → ordered pairs (verifier states, falsifier states)

- **Variable assignment**: Maps variables to states

- **Extension of terms**: Recursively defined as:
  - Variable `x` → value given by variable assignment
  - `f(a_1,...,a_n)` → interpretation of `f` applied to extensions of arguments

#### Verification/Falsification Clauses

| Formula Type | Verification Condition | Falsification Condition |
|-------------|------------------------|------------------------|
| Atomic `F(a_1,...,a_n)` | Verifier function in `F`'s interpretation returns the state when applied to argument extensions | Falsifier function returns the state |
| Negation `¬A` | State falsifies `A` | State verifies `A` |
| Conjunction `A ∧ B` | State is fusion of verifier for `A` and verifier for `B` | State is falsifier for `A`, or falsifier for `B`, or fusion of both |
| Disjunction `A ∨ B` | State is verifier for `A`, or verifier for `B`, or fusion of both | State is fusion of falsifier for `A` and falsifier for `B` |
| Top `⊤` | Always verified | Only falsified by full state (fusion of all states) |
| Bottom `⊥` | Never verified | Only falsified by null state (fusion of no states) |
| Propositional Identity `A ≡ B` | State is null AND `A` and `B` have same verifiers and falsifiers | State is null AND `A` and `B` differ in verifiers or falsifiers |

#### Logical Consequence (Constitutive Layer)
- Restricted to propositional identity sentences or combinations thereof
- A conclusion is a logical consequence of premises iff the conclusion is verified by the null state in any model where the null state verifies all premises

### 4. Intensional Semantics (Causal Layer)

#### Additional Frame Components
- **Times**: Totally ordered abelian group
- **Task relation**: Three-place relation satisfying transitivity
- **Possible state**: Has null task from itself to itself in zero duration
- **Compatible states**: Fusion is possible
- **Maximal state**: For every compatible state `t`, `t` is part of `s`
- **World-state**: Maximal possible state
- **World-history**: Function `τ` from convex time set `X` to states where `τ(x) ⇒_{y-x} τ(y)` for any `x, y` in `X`

#### Truth Evaluation
- Model, world-history, time, variable assignment makes atomic sentence true/false iff there is a verifier/falsifier state for that sentence which is part of `τ(time)`
- Recursive clauses for all connectives provided
- Logical consequence: Conclusion follows from premises iff any model, world-history, time, variable assignment making premises true also makes conclusion true

### 5. Documents Requiring Revision

| Document | Current State | Required Changes |
|----------|--------------|------------------|
| `LAYER_EXTENSIONS.md` | Contains FIX comment with new structure; body uses old Layer 0-3 naming | Reorganize to five-layer structure; incorporate FIX content |
| `GLOSSARY.md` | Uses old Layer 0-3 terminology; operators mapped to wrong layers | Update layer architecture table; reassign operators to correct layers |
| `RECURSIVE_SEMANTICS.md` | Does not exist | Create new file with full hyperintensional/intensional semantics |

### 6. Content for RECURSIVE_SEMANTICS.md

The new document should include:

1. **Introduction**: Explain recursive semantic framework and layer progression
2. **Constitutive Frame and Model**
   - Complete lattice structure
   - Interpretation function details
   - Variable assignment mechanism
3. **Hyperintensional Semantics**
   - Verification and falsification clauses for all formula types
   - Extension function for terms
   - Logical consequence for constitutive sentences
4. **Causal Frame Extension**
   - Temporal structure (abelian group)
   - Task relation and constraints
   - State modality concepts
   - World-history definition
5. **Intensional Semantics**
   - Truth and falsity clauses
   - Logical consequence for causal sentences
6. **Placeholder sections for Epistemic, Normative, Agential layers**
   - Use [DETAILS] tags for semantics not yet specified
   - Use [QUESTION: ...] tags for uncertain design decisions

### 7. Uncertainty Points Requiring [QUESTION: ...] Tags

Based on analysis of the FIX comment and existing documentation:

1. **Epistemic Layer Frame**: What is the exact structure of the credence function? Does it assign probabilities to individual state transitions or to sets of transitions?

2. **Normative Layer Frame**: How are value orderings structured? Are they complete orderings or partial orderings? Are they agent-relative?

3. **Agential Layer**: What frame extensions are required for multi-agent reasoning? Does this layer add agent indices, or agent-relative accessibility relations?

4. **Layer Interaction**: How do operators from different layers compose semantically? Is evaluation always in the most complex frame, or are there efficiency considerations?

5. **Constitutive-Causal Relationship**: The FIX comment states constitutive semantics cannot evaluate atomic sentences alone because world-states aren't defined yet. How exactly does the transition work when moving to causal semantics?

## Recommendations

1. **Phased Revision Approach**
   - Phase 1: Revise LAYER_EXTENSIONS.md structure to match five-layer organization
   - Phase 2: Update GLOSSARY.md layer terminology and operator mappings
   - Phase 3: Create RECURSIVE_SEMANTICS.md with complete semantic details

2. **Semantic Precision**
   - The hyperintensional semantics for the Constitutive Layer are well-specified in the FIX comment
   - The intensional semantics for the Causal Layer have key definitions but need full recursive clauses
   - Mark Epistemic, Normative, and Agential layer semantics with [DETAILS] tags

3. **Cross-Reference Updates**
   - METHODOLOGY.md references will need updating to new layer names
   - ARCHITECTURE.md references to "Layer 0" should map to the new structure
   - Consider whether existing Lean code layer terminology needs revision

4. **Preserve Existing Examples**
   - The medical treatment, legal evidence, and negotiation examples are valuable
   - Map them to appropriate new layers during revision

## References

- Documentation/Research/LAYER_EXTENSIONS.md (lines 9-36 - FIX comment)
- Documentation/Reference/GLOSSARY.md
- Documentation/UserGuide/METHODOLOGY.md
- Documentation/UserGuide/ARCHITECTURE.md
- Documentation/Research/CONCEPTUAL_ENGINEERING.md

## Next Steps

1. Create implementation plan with phased approach
2. Revise LAYER_EXTENSIONS.md, incorporating FIX tag content into main document body
3. Update GLOSSARY.md layer architecture table
4. Create RECURSIVE_SEMANTICS.md with full semantic specifications
5. Review and update cross-references in other documentation files
