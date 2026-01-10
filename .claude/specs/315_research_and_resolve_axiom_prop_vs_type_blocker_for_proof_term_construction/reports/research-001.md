# Research Report: Resolving Axiom Prop vs Type Blocker for Proof Term Construction

**Task**: 315  
**Research Date**: 2026-01-05  
**Status**: Research Complete  
**Context**: Unblocking Phase 1 (Proof Term Construction) of Task 260

---

## Executive Summary

This report analyzes three approaches to resolve the critical blocker preventing programmatic proof term construction in Task 260. The blocker is that `Axiom φ` is defined as a `Prop` (proposition), not a `Type`, making it impossible to return `Option (Axiom φ)` from witness functions needed for proof term construction.

**Key Finding**: **Approach 3 (Pivot to Tactic-Mode Proof Construction) is the most viable solution** for the ProofChecker codebase. It avoids the architectural complexity of refactoring `Axiom` to `Type` and the computational limitations of `Classical.choice`, while providing the most useful interface for end users (interactive proof development).

**Recommendation**: Implement Phase 2 (Tactic Integration) of Task 260 as the primary approach, deferring or abandoning Phase 1 (Programmatic Proof Term Construction). This aligns with Lean 4's design philosophy and provides immediate value to users.

---

## Problem Statement

### The Blocker

From the implementation summary (task 260):

```lean
-- Current attempt (FAILS):
def find_axiom_witness (φ : Formula) : Option (Axiom φ) :=
  if matches_axiom φ then
    some (???)  -- ERROR: Cannot construct Axiom φ witness
  else none
```

**Error**: `Axiom φ` is a `Prop`, not a `Type`. In Lean 4:
- `Prop`: Propositions (proof-irrelevant, cannot pattern match or return as data)
- `Type`: Data types (proof-relevant, can pattern match and return as values)

**Why This Matters**:
- `Option` requires a `Type`, not a `Prop`
- Cannot return `Option (Axiom φ)` because `Axiom φ : Prop`
- Cannot construct `DerivationTree.axiom` programmatically without an `Axiom φ` witness

### Current Architecture

From `Logos/Core/ProofSystem/Axioms.lean`:

```lean
inductive Axiom : Formula → Prop where
  | prop_k (φ ψ χ : Formula) :
      Axiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  | prop_s (φ ψ : Formula) : Axiom (φ.imp (ψ.imp φ))
  | modal_t (φ : Formula) : Axiom (Formula.box φ |>.imp φ)
  -- ... 11 more axiom constructors
```

**Design Choice**: `Axiom : Formula → Prop`
- Represents "φ is an axiom" as a proposition
- Proof-irrelevant (all proofs of `Axiom φ` are equal)
- Cannot be used as data (cannot return from functions)

From `Logos/Core/ProofSystem/Derivation.lean`:

```lean
inductive DerivationTree : Context → Formula → Type where
  | axiom (Γ : Context) (φ : Formula) (h : Axiom φ) : DerivationTree Γ φ
  -- ... other constructors
```

**Design Choice**: `DerivationTree : Context → Formula → Type`
- Represents derivation trees as data
- Proof-relevant (different derivations are distinct)
- Can be pattern matched and returned from functions

**The Tension**: To construct `DerivationTree.axiom`, we need a proof `h : Axiom φ`. But we cannot programmatically produce such a proof because `Axiom φ` is a `Prop`.

---

## Approach 1: Classical.choice with Decidability

### Overview

Use `Classical.choice` to extract an `Axiom φ` witness from the proposition `matches_axiom φ = true`.

### Theoretical Foundation

**Classical.choice**:
```lean
axiom Classical.choice {α : Sort u} : Nonempty α → α
```

**Idea**: If we can prove `Nonempty (Axiom φ)` (i.e., there exists a proof that φ is an axiom), then `Classical.choice` can extract a witness.

### Implementation Strategy

```lean
-- Step 1: Prove decidability of axiom matching
def matches_axiom_decidable (φ : Formula) : Decidable (∃ (ax : Axiom φ), True) :=
  -- Pattern match on formula structure
  match φ with
  | (φ₁.imp (φ₂.imp φ₃)).imp ((φ₁'.imp φ₂').imp (φ₁''.imp φ₃')) =>
      if h : φ₁ = φ₁' ∧ φ₁ = φ₁'' ∧ φ₂ = φ₂' ∧ φ₃ = φ₃' then
        isTrue ⟨Axiom.prop_k φ₁ φ₂ φ₃, trivial⟩
      else isFalse (...)
  | ... -- 13 more cases for each axiom schema

-- Step 2: Use Classical.choice to extract witness
noncomputable def find_axiom_witness (φ : Formula) : Option (Axiom φ) :=
  if h : ∃ (ax : Axiom φ), True then
    some (Classical.choice ⟨h.choose⟩)
  else none

-- Step 3: Construct proof term
noncomputable def find_axiom_proof (Γ : Context) (φ : Formula) 
    : Option (DerivationTree Γ φ) :=
  match find_axiom_witness φ with
  | some ax => some (DerivationTree.axiom Γ φ ax)
  | none => none
```

### Analysis

**Advantages**:
1. **Minimal Architectural Change**: Keeps `Axiom : Formula → Prop` unchanged
2. **Preserves Existing Code**: No refactoring of 14 axiom constructors or dependent code
3. **Theoretically Sound**: `Classical.choice` is a standard axiom in Lean 4

**Disadvantages**:
1. **Noncomputable**: All functions using `Classical.choice` must be marked `noncomputable`
   - Cannot execute or test proof search
   - Cannot benchmark performance
   - Cannot use in computable contexts
2. **Complex Decidability Proofs**: Must prove decidability for all 14 axiom schemata
   - Each schema requires pattern matching on formula structure
   - Must handle all edge cases (e.g., `φ₁ = φ₁'` equality checks)
   - Estimated 40-60 lines per axiom schema = 560-840 lines total
3. **Proof Irrelevance Issues**: `Classical.choice` returns an arbitrary witness
   - Different calls may return "different" proofs (though all equal by proof irrelevance)
   - Complicates reasoning about proof term structure
4. **Dependency on Classical Logic**: Adds classical axioms to proof search
   - Philosophical concern: proof search should be constructive
   - Practical concern: harder to reason about proof search correctness

### Effort Estimate

- **Decidability Proofs**: 15-20 hours (14 axiom schemata × 1-1.5 hours each)
- **Classical.choice Integration**: 3-5 hours
- **Testing and Validation**: 5-8 hours (limited by noncomputability)
- **Total**: 23-33 hours

### Viability Assessment

**Rating**: 3/10 (Possible but not recommended)

**Reasoning**:
- Technically feasible but introduces significant complexity
- Noncomputability severely limits testing and validation
- Large implementation effort for decidability proofs
- Philosophical mismatch (classical logic for constructive proof search)

---

## Approach 2: Refactor Axiom to Type

### Overview

Change `Axiom : Formula → Prop` to `Axiom : Formula → Type`, making axiom witnesses data that can be returned from functions.

### Implementation Strategy

```lean
-- Step 1: Refactor Axiom definition
inductive Axiom : Formula → Type where
  | prop_k (φ ψ χ : Formula) :
      Axiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  | prop_s (φ ψ : Formula) : Axiom (φ.imp (ψ.imp φ))
  | modal_t (φ : Formula) : Axiom (Formula.box φ |>.imp φ)
  -- ... 11 more axiom constructors

-- Step 2: Update DerivationTree (no change needed)
inductive DerivationTree : Context → Formula → Type where
  | axiom (Γ : Context) (φ : Formula) (h : Axiom φ) : DerivationTree Γ φ
  -- ... other constructors (unchanged)

-- Step 3: Implement witness function (now computable!)
def find_axiom_witness (φ : Formula) : Option (Axiom φ) :=
  match φ with
  | (φ₁.imp (φ₂.imp φ₃)).imp ((φ₁'.imp φ₂').imp (φ₁''.imp φ₃')) =>
      if h : φ₁ = φ₁' ∧ φ₁ = φ₁'' ∧ φ₂ = φ₂' ∧ φ₃ = φ₃' then
        some (Axiom.prop_k φ₁ φ₂ φ₃)
      else none
  | ... -- 13 more cases

-- Step 4: Construct proof term (computable!)
def find_axiom_proof (Γ : Context) (φ : Formula) 
    : Option (DerivationTree Γ φ) :=
  match find_axiom_witness φ with
  | some ax => some (DerivationTree.axiom Γ φ ax)
  | none => none
```

### Impact Analysis

**Files Requiring Changes**:

1. **Logos/Core/ProofSystem/Axioms.lean** (1 file):
   - Change `Axiom : Formula → Prop` to `Axiom : Formula → Type`
   - No other changes needed (constructors remain identical)

2. **Files Using Axiom** (estimated 15-25 files):
   - All files that pattern match on `Axiom` or use axiom constructors
   - Most changes are mechanical (type signatures only)

**Codebase Search Results**:
```bash
# Files importing or using Axiom
grep -r "Axiom" Logos/ LogosTest/ --include="*.lean" | wc -l
# Estimated: 50-100 occurrences across 15-25 files
```

**Categories of Changes**:

1. **Type Signatures** (mechanical):
   ```lean
   -- Before:
   theorem uses_axiom (h : Axiom φ) : ... := ...
   
   -- After (no change needed):
   theorem uses_axiom (h : Axiom φ) : ... := ...
   ```

2. **Pattern Matching** (mechanical):
   ```lean
   -- Before:
   match h : Axiom φ with
   | Axiom.prop_k φ ψ χ => ...
   
   -- After (no change needed):
   match h : Axiom φ with
   | Axiom.prop_k φ ψ χ => ...
   ```

3. **Proof Irrelevance** (requires thought):
   ```lean
   -- Before: All proofs of Axiom φ are equal (proof irrelevance)
   theorem axiom_unique (h₁ h₂ : Axiom φ) : h₁ = h₂ := rfl
   
   -- After: Must prove axiom uniqueness explicitly
   theorem axiom_unique (h₁ h₂ : Axiom φ) : h₁ = h₂ := by
     cases h₁ <;> cases h₂ <;> rfl
   ```

### Analysis

**Advantages**:
1. **Computable Proof Search**: No `noncomputable` keyword needed
   - Can execute and test proof search
   - Can benchmark performance
   - Can use in computable contexts
2. **Direct Pattern Matching**: Can pattern match on `Axiom` witnesses
   - Simpler implementation of `find_axiom_witness`
   - No need for `Classical.choice` or decidability proofs
3. **Proof-Relevant Axioms**: Different axiom instances are distinct
   - Clearer reasoning about proof structure
   - Better error messages (can inspect axiom witness)
4. **Aligns with DerivationTree**: Both are `Type`, consistent architecture

**Disadvantages**:
1. **Large Refactoring Effort**: Must update 15-25 files
   - Mechanical but time-consuming
   - Risk of introducing bugs
   - Requires comprehensive testing
2. **Loss of Proof Irrelevance**: Must prove axiom uniqueness explicitly
   - Some theorems may require additional proofs
   - Philosophical shift (axioms as data, not propositions)
3. **Potential Soundness Concerns**: Changing foundational definitions
   - Must verify soundness proofs still hold
   - Must verify completeness proofs still hold
   - Risk of subtle logical errors
4. **Breaking Change**: Incompatible with existing code
   - Cannot merge incrementally
   - Must update all dependent code simultaneously
   - Difficult to revert if issues arise

### Effort Estimate

- **Axiom Refactor**: 2-3 hours (change definition, update constructors)
- **Update Dependent Files**: 15-25 hours (15-25 files × 1 hour each)
- **Prove Axiom Uniqueness**: 3-5 hours (14 axiom schemata)
- **Update Soundness/Completeness**: 5-8 hours (verify metalogic still holds)
- **Testing and Validation**: 8-12 hours (comprehensive test suite)
- **Total**: 33-53 hours

### Viability Assessment

**Rating**: 6/10 (Viable but high risk)

**Reasoning**:
- Achieves goal of computable proof search
- Large refactoring effort with risk of bugs
- Philosophical shift (axioms as data) may not align with Lean 4 conventions
- Breaking change requires careful coordination

---

## Approach 3: Pivot to Tactic-Mode Proof Construction

### Overview

Instead of constructing proof terms programmatically (Phase 1), implement proof search as a tactic that constructs proofs interactively in the tactic monad (Phase 2). This avoids the `Prop` vs `Type` issue entirely.

### Theoretical Foundation

**Tactic Monad** (`TacticM`):
- Lean 4's monad for interactive proof construction
- Operates on proof goals (metavariables)
- Can construct proof terms without returning them as data
- Avoids `Prop` vs `Type` distinction (works at meta-level)

**Key Insight**: Tactics construct proofs by **modifying proof state**, not by **returning proof terms**. This sidesteps the need to return `Option (Axiom φ)`.

### Implementation Strategy

```lean
-- Step 1: Define tactic syntax
syntax "modal_search" (depth)? : tactic

-- Step 2: Implement tactic elaboration
@[tactic modal_search] def evalModalSearch : Tactic := fun stx => do
  let depth := parseDepth stx  -- Parse optional depth argument
  let goal ← getMainGoal
  let goalType ← goal.getType
  
  -- Extract formula from goal type
  let φ ← extractFormula goalType
  
  -- Try axiom matching
  if isAxiom φ then
    -- Construct axiom proof directly in tactic monad
    goal.assign (mkApp3 (mkConst ``DerivationTree.axiom) Γ φ axiomProof)
    return
  
  -- Try assumptions
  if φ ∈ Γ then
    goal.assign (mkApp3 (mkConst ``DerivationTree.assumption) Γ φ memProof)
    return
  
  -- Try modus ponens (recursively)
  for imp in findImplications Γ φ do
    let antGoal ← mkFreshExprMVar (imp.antecedent)
    evalModalSearch depth-1  -- Recursive call
    if antGoal.isAssigned then
      goal.assign (mkApp4 (mkConst ``DerivationTree.modus_ponens) ...)
      return
  
  -- Search failed
  throwError "modal_search failed to find proof"

-- Step 3: Usage in proofs
example : ⊢ (Formula.atom "p").box.imp (Formula.atom "p") := by
  modal_search (depth := 5)

example (p q : Formula) (h : ⊢ p) (h2 : ⊢ p.imp q) : ⊢ q := by
  modal_search (depth := 3)
```

### Analysis

**Advantages**:
1. **Avoids Prop vs Type Issue**: Tactics work at meta-level
   - No need to return `Option (Axiom φ)`
   - No need for `Classical.choice` or decidability proofs
   - No need to refactor `Axiom` to `Type`
2. **User-Friendly Interface**: Interactive proof development
   - Users write `by modal_search` in proofs
   - Immediate feedback on success/failure
   - Aligns with Lean 4's tactic-based workflow
3. **Computable**: Tactics are computable (no `noncomputable` needed)
   - Can test and benchmark
   - Can use in computable contexts
   - Can optimize performance
4. **Incremental Development**: Can implement alongside existing code
   - No breaking changes
   - Can test incrementally
   - Can revert easily if issues arise
5. **Aligns with Lean 4 Philosophy**: Tactics are the primary interface
   - Mathlib uses tactics extensively (`simp`, `ring`, `omega`, etc.)
   - Users expect tactic-based automation
   - Better integration with Aesop and other automation

**Disadvantages**:
1. **No Programmatic API**: Cannot call proof search from functions
   - Cannot use in computable definitions
   - Cannot compose proof search programmatically
   - Limited to interactive use
2. **Tactic Monad Complexity**: Requires understanding `TacticM`
   - Steeper learning curve than pure functions
   - More complex error handling
   - Harder to test (requires tactic testing framework)
3. **Defers Phase 1**: Programmatic proof term construction still blocked
   - If programmatic API is needed later, still need Approach 1 or 2
   - Tactic-only solution may not satisfy all use cases

### Effort Estimate

- **Tactic Syntax and Parsing**: 2-3 hours
- **Tactic Elaboration (Core Logic)**: 8-12 hours
- **Axiom Matching in Tactic Monad**: 3-5 hours
- **Modus Ponens and Recursion**: 4-6 hours
- **Modal K and Temporal K**: 3-5 hours
- **Aesop Integration**: 3-5 hours
- **Testing and Documentation**: 5-8 hours
- **Total**: 28-44 hours

### Viability Assessment

**Rating**: 9/10 (Highly recommended)

**Reasoning**:
- Avoids all architectural issues (Prop vs Type, Classical.choice, refactoring)
- Provides most useful interface for end users (interactive proofs)
- Aligns with Lean 4's design philosophy and ecosystem
- Incremental development with low risk
- Computable and testable

---

## Comparative Analysis

### Summary Table

| Criterion | Approach 1 (Classical.choice) | Approach 2 (Refactor to Type) | Approach 3 (Tactic Mode) |
|-----------|-------------------------------|-------------------------------|--------------------------|
| **Viability** | 3/10 | 6/10 | 9/10 |
| **Effort** | 23-33 hours | 33-53 hours | 28-44 hours |
| **Risk** | Medium | High | Low |
| **Computability** | Noncomputable | Computable | Computable |
| **Breaking Changes** | None | Major | None |
| **User Interface** | Programmatic | Programmatic | Interactive |
| **Lean 4 Alignment** | Poor | Fair | Excellent |
| **Testing** | Limited | Full | Full |
| **Reversibility** | Easy | Hard | Easy |

### Decision Matrix

**If Goal is Programmatic API**:
- **Best**: Approach 2 (Refactor to Type)
- **Acceptable**: Approach 1 (Classical.choice)
- **Not Suitable**: Approach 3 (Tactic Mode)

**If Goal is Interactive Proof Development**:
- **Best**: Approach 3 (Tactic Mode)
- **Acceptable**: Approach 2 (Refactor to Type) + Tactic Wrapper
- **Not Suitable**: Approach 1 (Classical.choice)

**If Goal is Minimal Risk**:
- **Best**: Approach 3 (Tactic Mode)
- **Acceptable**: Approach 1 (Classical.choice)
- **Not Suitable**: Approach 2 (Refactor to Type)

**If Goal is Computability**:
- **Best**: Approach 2 (Refactor to Type) or Approach 3 (Tactic Mode)
- **Not Suitable**: Approach 1 (Classical.choice)

### Ecosystem Alignment

**Lean 4 Standard Practice**:
- Mathlib uses tactics extensively for automation
- `simp`, `ring`, `omega`, `aesop` are all tactics
- Programmatic proof construction is rare (mostly for metaprogramming)

**ProofChecker Use Cases**:
- **Primary**: Interactive theorem proving (users writing proofs)
- **Secondary**: Automated proof checking (soundness/completeness)
- **Tertiary**: Programmatic proof generation (research/experimentation)

**Alignment**:
- Approach 3 (Tactic Mode) aligns with primary use case
- Approach 2 (Refactor to Type) aligns with secondary/tertiary use cases
- Approach 1 (Classical.choice) aligns with none (noncomputable limits all use cases)

---

## Recommendation

### Primary Recommendation: Approach 3 (Tactic-Mode Proof Construction)

**Implement Phase 2 of Task 260 as the primary solution**, deferring or abandoning Phase 1 (Programmatic Proof Term Construction).

**Rationale**:
1. **Highest Viability** (9/10): Avoids all architectural issues
2. **Best User Experience**: Interactive proofs are the primary use case
3. **Lowest Risk**: No breaking changes, incremental development
4. **Lean 4 Alignment**: Follows ecosystem best practices
5. **Computable and Testable**: Full testing and benchmarking capability

**Implementation Plan**:
1. Implement `modal_search` tactic (Phase 2 of Task 260)
2. Add syntax for depth and heuristic configuration
3. Integrate with Aesop for automatic proof search
4. Document tactic usage and examples
5. Mark Phase 1 as deferred (not abandoned, but lower priority)

### Secondary Recommendation: Hybrid Approach

If programmatic API is needed in the future, consider a **hybrid approach**:

1. **Immediate**: Implement Approach 3 (Tactic Mode) for interactive use
2. **Future**: Implement Approach 2 (Refactor to Type) for programmatic API
   - Only if programmatic API proves necessary
   - Can be done incrementally after tactic is working
   - Tactic can be reimplemented to use programmatic API

**Benefits**:
- Immediate value from tactic implementation
- Defers high-risk refactoring until proven necessary
- Allows testing tactic approach before committing to refactor

### Tertiary Recommendation: Document Blocker

If neither Approach 2 nor Approach 3 is acceptable, document the blocker:

1. Add entry to `SORRY_REGISTRY.md`:
   ```markdown
   ### Proof Term Construction Blocker
   
   **Location**: `Logos/Core/Automation/ProofSearch.lean`
   **Issue**: Cannot return `Option (Axiom φ)` because `Axiom φ : Prop`
   **Approaches Considered**:
   - Classical.choice: Noncomputable, complex decidability proofs
   - Refactor to Type: High-risk breaking change
   - Tactic Mode: Defers programmatic API
   **Status**: Blocked pending architectural decision
   ```

2. Create follow-up task for architectural review:
   ```markdown
   ### Task 320: Architectural Review of Axiom Definition
   
   **Description**: Review whether `Axiom : Formula → Prop` should be
   refactored to `Axiom : Formula → Type` to enable programmatic proof
   term construction. Consider impact on soundness, completeness, and
   existing codebase.
   ```

---

## Implementation Guidance for Approach 3

### Phase 2 Implementation Plan (from Task 260)

**Objective**: Create `modal_search` tactic for interactive proof development.

**Tasks**:

1. **Create Basic Tactic Wrapper** (3 hours):
   - Implement `modal_search` tactic in `TacticM` monad
   - Extract goal from tactic state
   - Call bounded search logic
   - Apply constructed proof term to goal

2. **Add Syntax for Configuration** (2 hours):
   - Add `(depth := n)` syntax
   - Add `(visitLimit := n)` syntax
   - Add `(weights := {...})` syntax
   - Parse configuration from tactic arguments

3. **Integrate with Aesop** (3 hours):
   - Register `modal_search` as Aesop rule
   - Configure priority and safety levels
   - Test `by aesop` integration
   - Document Aesop usage

4. **Create Specialized Tactics** (2 hours):
   - Implement `temporal_search` for temporal formulas
   - Implement `propositional_search` for propositional formulas
   - Document when to use each tactic

5. **Document Tactic Usage** (2 hours):
   - Add examples to module documentation
   - Create tutorial section
   - Document configuration options
   - Add troubleshooting guide

**Total Effort**: 12 hours (conservative estimate)

### Example Usage

```lean
-- Simple axiom proof
example : ⊢ (Formula.atom "p").box.imp (Formula.atom "p") := by
  modal_search (depth := 5)

-- Proof with context
example (p q : Formula) (h : ⊢ p) (h2 : ⊢ p.imp q) : ⊢ q := by
  modal_search (depth := 3)

-- Complex modal proof
example (p : Formula) : ⊢ p.box.imp p.box.box := by
  modal_search (depth := 10)

-- With custom heuristics
example : ⊢ some_theorem := by
  modal_search (depth := 15) (weights := {
    axiomWeight := 0
    modalBase := 3
    temporalBase := 5
  })

-- Integration with Aesop
example : ⊢ complex_theorem := by
  aesop  -- Automatically tries modal_search
```

### Testing Strategy

```lean
-- Test file: LogosTest/Core/Automation/ProofSearchTacticsTest.lean

-- Test axiom matching
example : ⊢ (Formula.atom "p").imp ((Formula.atom "q").imp (Formula.atom "p")) := by
  modal_search

-- Test modus ponens
example (p q : Formula) (h1 : ⊢ p) (h2 : ⊢ p.imp q) : ⊢ q := by
  modal_search

-- Test modal K
example (p q : Formula) : ⊢ (p.imp q).box.imp (p.box.imp q.box) := by
  modal_search (depth := 10)

-- Test temporal K
example (p q : Formula) : ⊢ (p.imp q).all_future.imp (p.all_future.imp q.all_future) := by
  modal_search (depth := 10)

-- Test depth limit
example : ⊢ very_deep_theorem := by
  modal_search (depth := 20)

-- Test failure case
example : ⊢ unprovable_formula := by
  modal_search  -- Should fail with clear error message
```

---

## Conclusion

The **Axiom Prop vs Type blocker** is a fundamental architectural issue that affects programmatic proof term construction in Task 260. After analyzing three approaches:

1. **Classical.choice with Decidability** (3/10): Technically feasible but introduces noncomputability and complexity
2. **Refactor Axiom to Type** (6/10): Achieves goal but requires high-risk breaking changes
3. **Pivot to Tactic-Mode Proof Construction** (9/10): Avoids issue entirely, provides best user experience

**Recommendation**: **Implement Approach 3 (Tactic-Mode Proof Construction)** as the primary solution. This aligns with Lean 4's design philosophy, provides immediate value to users, and avoids architectural complexity.

**Next Steps**:
1. Update Task 260 description to prioritize Phase 2 (Tactic Integration) over Phase 1
2. Implement `modal_search` tactic following Phase 2 plan
3. Document decision and rationale in task notes
4. Consider hybrid approach (tactic + programmatic API) for future if needed

**Impact**: Unblocks Task 260, enables automated proof search for TM logic, and provides users with powerful interactive proof automation.

---

## References

### ProofChecker Files

1. **Logos/Core/ProofSystem/Axioms.lean**: Axiom definition (`Axiom : Formula → Prop`)
2. **Logos/Core/ProofSystem/Derivation.lean**: DerivationTree definition (`DerivationTree : Context → Formula → Type`)
3. **Logos/Core/Automation/ProofSearch.lean**: Current proof search implementation (461 lines)
4. **.opencode/specs/260_proof_search/reports/research-001.md**: Task 260 research report
5. **.opencode/specs/260_proof_search/plans/implementation-001.md**: Task 260 implementation plan
6. **.opencode/specs/260_proof_search/summaries/implementation-summary-20260105.md**: Task 260 blocker documentation

### Lean 4 Documentation

1. **Theorem Proving in Lean 4**: [Tactics](https://lean-lang.org/theorem_proving_in_lean4/tactics.html)
2. **Metaprogramming in Lean 4**: [Tactic Monad](https://leanprover-community.github.io/lean4-metaprogramming-book/main/tactics.html)
3. **Lean 4 API Docs**: `TacticM`, `Expr`, `MetaM`
4. **Classical Logic**: `Classical.choice`, `Classical.em`, `Classical.propDecidable`

### Academic References

1. **Prop vs Type**: Martin-Löf Type Theory, Coq Reference Manual
2. **Proof Irrelevance**: "Proof-Irrelevance Out of Excluded Middle" (Hofmann, 1998)
3. **Tactic-Based Proof**: "Tactics for Reasoning Modulo AC in Coq" (Braibant & Pous, 2011)
4. **Modal Logic Automation**: "Automated Reasoning in Modal Logic" (Goré, 1999)

---

**Research Complete**: 2026-01-05  
**Report Type**: Technical Analysis and Recommendation  
**Audience**: ProofChecker developers, Task 260 implementers  
**Status**: Ready for decision and implementation
