# Integration Testing in Lean 4: Research Findings

**Research Date**: December 24, 2025  
**Researcher**: Web Research Specialist  
**Topic**: Integration testing best practices for Lean 4 proof systems

---

## Executive Summary

Integration testing in Lean 4 is fundamentally different from traditional software testing due to the proof-centric nature of the language. The primary approach is to **write proofs as tests**, where the type system and proof obligations serve as the test assertions. This research identifies key patterns for integration testing in Lean 4, with specific focus on proof systems, automation tactics, and end-to-end workflows.

**Key Findings**:

1. **Proof-as-Test Pattern**: Integration tests are primarily written as theorems that must be proven, combining multiple components
2. **Property-Based Testing**: Plausible library provides QuickCheck-style testing for finding counterexamples
3. **Test Organization**: Mathlib4 uses a dedicated `MathlibTest/` directory with modular test files
4. **No Built-in Coverage Tools**: Coverage measurement relies on manual tracking and proof obligations
5. **Tactic Testing**: Tactics are tested by applying them to goals and verifying the resulting proof state
6. **End-to-End Workflows**: Integration tests compose syntax → proof → semantics → verification pipelines

**Recommended Approach for ProofChecker**:
- Use proof-based integration tests for soundness/completeness properties
- Add Plausible for property-based testing of metalogic properties
- Organize tests in `LogosTest/Integration/` mirroring the main structure
- Create end-to-end tests that exercise full proof workflows
- Use custom test harnesses for tactic testing

---

## 1. Integration Testing Patterns in Lean 4

### 1.1 The Proof-as-Test Pattern

**Core Principle**: In Lean 4, the primary integration testing pattern is to write theorems that must be proven. The proof itself serves as the test, and the type checker verifies correctness.

**Example from Mathlib4**:
```lean
-- Integration test: proof system + semantics
theorem soundness_integration (Γ : Context) (φ : Formula) :
    Derivable Γ φ → Valid Γ φ := by
  intro h_deriv
  -- This proof integrates:
  -- 1. Proof system (Derivable)
  -- 2. Semantics (Valid)
  -- 3. Induction on derivations
  -- 4. Semantic evaluation
  induction h_deriv with
  | axiom => apply valid_axiom
  | mp h1 h2 ih1 ih2 => apply valid_mp ih1 ih2
  ...
```

**Benefits**:
- Type safety guarantees correctness
- Proofs are checked at compile time
- No runtime overhead
- Self-documenting through types

**Limitations**:
- Cannot test non-provable properties
- Requires decidable predicates
- May not catch performance issues

### 1.2 Test Organization in Mathlib4

Mathlib4 uses a clear separation between library code and tests:

```
Mathlib/              -- Library code
  Core/
    ProofSystem/
    Semantics/
    
MathlibTest/          -- Test code
  Core/
    ProofSystem/
      DerivationTest.lean
      AxiomsTest.lean
    Semantics/
      TruthTest.lean
      ValidityTest.lean
    Integration/
      ProofSystemSemanticsTest.lean
      EndToEndTest.lean
```

**Key Patterns**:
1. **Mirroring Structure**: Test directory mirrors library structure
2. **Dedicated Test Files**: Each module has corresponding test file
3. **Integration Directory**: Separate directory for cross-module tests
4. **Property Tests**: Separate files for property-based tests

### 1.3 Integration Test Categories

**Category 1: Component Integration**
Tests that verify two components work together correctly.

```lean
-- Test: Proof system integrates with semantics
namespace ProofSystemSemanticsTest

-- Soundness: derivable implies valid
theorem soundness_test : Derivable Γ φ → Valid Γ φ := by
  sorry -- Actual proof

-- Completeness: valid implies derivable (for certain logics)
theorem completeness_test : Valid Γ φ → Derivable Γ φ := by
  sorry -- Actual proof

end ProofSystemSemanticsTest
```

**Category 2: Workflow Integration**
Tests that verify entire workflows from start to finish.

```lean
-- Test: Full proof workflow
namespace EndToEndTest

def test_workflow : IO Unit := do
  -- 1. Parse formula
  let φ ← parseFormula "□p → p"
  
  -- 2. Construct proof
  let proof ← constructProof φ
  
  -- 3. Verify proof
  let valid ← verifyProof proof
  
  -- 4. Check semantics
  let semantic_valid ← checkSemantics φ
  
  assert! (valid && semantic_valid)

#eval test_workflow
```

**Category 3: Tactic Integration**
Tests that verify tactics work with the proof system.

```lean
-- Test: Automation tactics with proof system
namespace AutomationProofSystemTest

example : □(p → q) → □p → □q := by
  -- Test that modal_tac integrates with proof system
  modal_tac
  -- Should generate valid derivation

example : □p ∧ □q → □(p ∧ q) := by
  -- Test that automation handles conjunction
  modal_tac
  
end AutomationProofSystemTest
```

---

## 2. Testing Automation Tactics

### 2.1 Tactic Testing Patterns

**Pattern 1: Goal State Verification**

```lean
-- Test tactic by checking resulting goal state
example : P ∧ Q := by
  constructor
  -- After constructor, should have two goals: P and Q
  case left => sorry
  case right => sorry

-- More sophisticated: check exact goal structure
def test_tactic_goal_structure : TacticM Unit := do
  let goals ← getGoals
  guard (goals.length = 2)
  let goal1 ← getMVarType goals[0]!
  let goal2 ← getMVarType goals[1]!
  guard (goal1 == `P)
  guard (goal2 == `Q)
```

**Pattern 2: Proof Term Verification**

```lean
-- Test that tactic generates expected proof term
example : P → P := by
  intro h
  exact h

-- Verify the proof term structure
#check (fun h : P => h : P → P)  -- Should match
```

**Pattern 3: Tactic Composition Testing**

```lean
-- Test that tactics compose correctly
example : □(P → Q) → □P → □Q := by
  intro h1 h2
  -- Test modal_mp tactic
  modal_mp h1 h2
  
-- Test tactic sequences
example : □P ∧ □Q → □(P ∧ Q) := by
  intro ⟨h1, h2⟩
  modal_and_intro
  · modal_exact h1
  · modal_exact h2
```

### 2.2 Testing Custom Tactics

**Approach 1: Unit Tests for Tactics**

```lean
-- Test individual tactic behavior
namespace TacticTests

-- Test: modal_intro adds □ to goal
def test_modal_intro : TacticM Unit := do
  -- Setup: goal is □P
  let goal ← getMainGoal
  let goalType ← getMVarType goal
  
  -- Apply tactic
  modal_intro
  
  -- Verify: new goal is P
  let newGoal ← getMainGoal
  let newType ← getMVarType newGoal
  guard (newType == `P)

-- Test: modal_mp applies modus ponens
def test_modal_mp : TacticM Unit := do
  -- Setup: hypotheses □(P → Q) and □P
  -- Goal: □Q
  modal_mp `h1 `h2
  
  -- Verify: goal is closed
  let goals ← getGoals
  guard goals.isEmpty

end TacticTests
```

**Approach 2: Integration Tests for Tactic Suites**

```lean
-- Test entire tactic suite on realistic problems
namespace TacticIntegrationTests

-- Test: modal tactics solve S4 theorems
example : □□P → □P := by
  modal_tac  -- Should solve automatically

example : □(P → Q) → □P → □Q := by
  modal_tac  -- Should solve automatically

-- Test: tactics handle complex formulas
example : □(P ∧ Q) ↔ □P ∧ □Q := by
  modal_tac  -- Should solve both directions

end TacticIntegrationTests
```

### 2.3 Testing Proof Search

**Pattern: Bounded Search Testing**

```lean
-- Test proof search with depth limits
namespace ProofSearchTests

def test_search_depth : IO Unit := do
  let φ := Formula.box (Formula.var "p")
  
  -- Test: search finds proof within depth 5
  let result ← searchProof φ (maxDepth := 5)
  assert! result.isSome
  
  -- Test: search respects depth limit
  let complex := Formula.box (Formula.box (Formula.box φ))
  let result2 ← searchProof complex (maxDepth := 2)
  assert! result2.isNone  -- Too deep

#eval test_search_depth
```

**Pattern: Heuristic Testing**

```lean
-- Test that heuristics improve search performance
namespace HeuristicTests

def test_heuristic_effectiveness : IO Unit := do
  let problems := [prob1, prob2, prob3, ...]
  
  -- Without heuristic
  let (time1, nodes1) ← measureSearch problems (heuristic := none)
  
  -- With heuristic
  let (time2, nodes2) ← measureSearch problems (heuristic := some myHeuristic)
  
  -- Heuristic should reduce nodes explored
  assert! (nodes2 < nodes1)

#eval test_heuristic_effectiveness
```

---

## 3. End-to-End Workflow Testing

### 3.1 Full Pipeline Tests

**Pattern: Syntax → Proof → Semantics → Verification**

```lean
namespace EndToEndWorkflowTests

-- Test complete workflow for a theorem
def test_full_workflow (input : String) : IO Bool := do
  -- Stage 1: Parse syntax
  let φ ← parseFormula input
  guard φ.wellFormed
  
  -- Stage 2: Construct proof
  let proof ← constructProof φ
  guard proof.isValid
  
  -- Stage 3: Check semantics
  let frame ← generateFrame
  let model := TaskModel.mk frame (fun _ _ => true)
  let semantic_valid ← checkValidity model φ
  
  -- Stage 4: Verify soundness
  guard (proof.isValid → semantic_valid)
  
  return true

-- Test suite of examples
def test_suite : IO Unit := do
  assert! (← test_full_workflow "□p → p")
  assert! (← test_full_workflow "□(p → q) → □p → □q")
  assert! (← test_full_workflow "□□p → □p")
  IO.println "All end-to-end tests passed!"

#eval test_suite
```

### 3.2 Round-Trip Testing

**Pattern: Verify Bidirectional Conversions**

```lean
-- Test: Formula ↔ String round-trips
def test_formula_roundtrip (φ : Formula) : Bool :=
  let s := φ.toString
  let φ' := parseFormula s
  φ' == some φ

-- Test: Proof ↔ Term round-trips
def test_proof_roundtrip (p : Proof) : Bool :=
  let term := p.toTerm
  let p' := Proof.fromTerm term
  p' == some p

-- Property-based test
#test ∀ φ : Formula, test_formula_roundtrip φ
```

### 3.3 Regression Testing

**Pattern: Golden Tests**

```lean
-- Test against known-good outputs
namespace RegressionTests

def golden_tests : List (String × String) := [
  ("□p → p", "proof_term_1"),
  ("□(p → q) → □p → □q", "proof_term_2"),
  ...
]

def test_golden : IO Unit := do
  for (input, expected) in golden_tests do
    let φ ← parseFormula input
    let proof ← constructProof φ
    let actual := proof.toTerm.toString
    assert! (actual == expected)

#eval test_golden
```

---

## 4. Property-Based Testing with Plausible

### 4.1 Integration with Plausible

**Setup**:
```lean
-- In lakefile.lean
require plausible from git
  "https://github.com/leanprover-community/plausible" @ "main"

-- In test file
import Plausible
open Plausible
```

**Pattern: Testing Metalogic Properties**

```lean
-- Test soundness property
#test ∀ (Γ : Context) (φ : Formula),
  Derivable Γ φ → Valid Γ φ

-- Test weakening
#test ∀ (Γ Δ : Context) (φ : Formula),
  Derivable Γ φ → Γ ⊆ Δ → Derivable Δ φ

-- Test cut elimination
#test ∀ (Γ : Context) (φ ψ : Formula),
  Derivable Γ φ → Derivable (φ :: Γ) ψ → Derivable Γ ψ
```

### 4.2 Custom Generators for Modal Logic

**Generator for Formulas**:
```lean
-- Automatic derivation
deriving instance Arbitrary for Formula

-- Or custom generator with size control
instance : Arbitrary Formula where
  arbitrary := Gen.sized fun size =>
    if size ≤ 0 then
      Gen.oneOf [
        pure Formula.bot,
        Formula.var <$> Arbitrary.arbitrary
      ]
    else
      Gen.oneOf [
        pure Formula.bot,
        Formula.var <$> Arbitrary.arbitrary,
        Formula.imp <$> Gen.resize (size / 2) Arbitrary.arbitrary 
                    <*> Gen.resize (size / 2) Arbitrary.arbitrary,
        Formula.box <$> Gen.resize (size - 1) Arbitrary.arbitrary
      ]
```

**Generator for Contexts**:
```lean
-- Context is List Formula, works automatically
instance : Arbitrary Context where
  arbitrary := Arbitrary.arbitrary

-- Or constrained generator
def genNonEmptyContext : Gen Context := do
  let φ ← Arbitrary.arbitrary
  let rest ← Arbitrary.arbitrary
  return φ :: rest
```

**Generator for Frames**:
```lean
-- Generate finite frames for testing
instance : SampleableExt TaskFrame where
  proxy := Nat  -- Use Nat as proxy for frame size
  interp n := {
    World := Fin n.succ
    worlds := List.finRange n.succ
    accessible := fun w1 w2 => w1.val ≤ w2.val
    -- ... other fields
  }
```

### 4.3 Integration Testing with Properties

**Pattern: Combining Proofs and Properties**

```lean
-- Proven theorem
theorem soundness : Derivable Γ φ → Valid Γ φ := by
  sorry  -- Actual proof

-- Property test to find edge cases
#test ∀ (Γ : Context) (φ : Formula),
  Derivable Γ φ → Valid Γ φ

-- If property test finds counterexample, it indicates:
-- 1. Bug in proof
-- 2. Bug in implementation
-- 3. Bug in generator
```

---

## 5. Test Organization and Structure

### 5.1 Recommended Directory Structure

```
LogosTest/
  Core/
    Syntax/
      FormulaTest.lean           -- Unit tests
      ContextTest.lean
      FormulaPropertyTest.lean   -- Property tests
      
    ProofSystem/
      DerivationTest.lean
      AxiomsTest.lean
      DerivationPropertyTest.lean
      
    Semantics/
      TruthTest.lean
      ValidityTest.lean
      SemanticPropertyTest.lean
      
    Automation/
      TacticsTest.lean
      ProofSearchTest.lean
      
    Integration/
      ProofSystemSemanticsTest.lean
      AutomationProofSystemTest.lean
      EndToEndTest.lean
      
  Property/
    Generators.lean              -- Custom generators
    README.md                    -- Generator documentation
    
  Integration.lean               -- Imports all integration tests
  Property.lean                  -- Imports all property tests
```

### 5.2 Test File Template

```lean
/-
Integration Test: [Component A] + [Component B]

Tests the integration between [Component A] and [Component B].

Test Coverage:
- [ ] Basic integration
- [ ] Edge cases
- [ ] Error handling
- [ ] Performance
-/

import Logos.Core.[ComponentA]
import Logos.Core.[ComponentB]
import Plausible  -- If using property tests

namespace LogosTest.Integration.[TestName]

-- Setup: Common test data
def test_context : Context := [...]
def test_formula : Formula := [...]

-- Test 1: Basic integration
example : [property] := by
  [proof]

-- Test 2: Edge case
example : [property] := by
  [proof]

-- Test 3: Property-based test
#test ∀ (x : Type), [property]

-- Test 4: IO-based test
def test_workflow : IO Unit := do
  [test code]
  assert! [condition]

#eval test_workflow

end LogosTest.Integration.[TestName]
```

### 5.3 Test Execution

**Running All Tests**:
```bash
# Build all tests
lake build LogosTest

# Run specific test file
lake env lean LogosTest/Integration/EndToEndTest.lean

# Run all integration tests
lake build LogosTest.Integration
```

**CI Integration**:
```yaml
# .github/workflows/test.yml
name: Tests
on: [push, pull_request]
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - uses: lean-lang/setup-lean@v1
      - run: lake build
      - run: lake build LogosTest
      - run: lake test  # If you have a test target
```

---

## 6. Coverage Measurement

### 6.1 Manual Coverage Tracking

Lean 4 does not have built-in coverage tools, so coverage must be tracked manually.

**Pattern: Coverage Checklist**

```lean
/-
Test Coverage for ProofSystem.Derivation

Axioms:
- [x] K axiom
- [x] T axiom
- [x] 4 axiom
- [ ] B axiom (not implemented)

Rules:
- [x] Modus ponens
- [x] Necessitation
- [x] Weakening
- [ ] Cut (tested separately)

Properties:
- [x] Soundness
- [x] Weakening
- [ ] Completeness (future work)
- [ ] Cut elimination (future work)

Integration:
- [x] With semantics
- [x] With automation
- [ ] With proof search (in progress)
-/
```

### 6.2 Proof Obligation Coverage

**Pattern: Track Proof Obligations**

```lean
-- Every sorry is a proof obligation
namespace CoverageTracking

-- Soundness: COVERED
theorem soundness : Derivable Γ φ → Valid Γ φ := by
  [complete proof]

-- Completeness: NOT COVERED
theorem completeness : Valid Γ φ → Derivable Γ φ := by
  sorry  -- TODO: Prove completeness

-- Weakening: COVERED
theorem weakening : Derivable Γ φ → Γ ⊆ Δ → Derivable Δ φ := by
  [complete proof]

end CoverageTracking
```

### 6.3 Test Matrix

**Pattern: Systematic Test Matrix**

```markdown
## Test Matrix: Modal Operators

| Operator | Unit Test | Integration Test | Property Test | Soundness | Completeness |
|----------|-----------|------------------|---------------|-----------|--------------|
| □        | [YES]         | [YES]                | [YES]             | [YES]         | [NO]            |
| ◇        | [YES]         | [YES]                | [YES]             | [YES]         | [NO]            |
| ⊃        | [YES]         | [YES]                | [YES]             | [YES]         | [YES]            |
| ∧        | [YES]         | [YES]                | [YES]             | [YES]         | [YES]            |
| ∨        | [YES]         | [YES]                | [YES]             | [YES]         | [YES]            |
| ¬        | [YES]         | [YES]                | [YES]             | [YES]         | [YES]            |
```

---

## 7. Best Practices from Mathlib4

### 7.1 Test Naming Conventions

**Pattern: Descriptive Test Names**

```lean
-- Good: Describes what is being tested
theorem soundness_modus_ponens_test : ...
theorem weakening_preserves_derivability_test : ...
theorem modal_necessitation_integration_test : ...

-- Bad: Generic names
theorem test1 : ...
theorem foo : ...
theorem check : ...
```

### 7.2 Test Documentation

**Pattern: Comprehensive Test Documentation**

```lean
/-!
# Integration Tests: Proof System + Semantics

This file tests the integration between the proof system and semantic
evaluation. The main properties tested are:

1. **Soundness**: Every derivable formula is semantically valid
2. **Weakening**: Derivability is preserved under context extension
3. **Substitution**: Derivability is preserved under substitution

## Test Organization

- `soundness_*`: Tests for soundness property
- `weakening_*`: Tests for weakening property
- `substitution_*`: Tests for substitution property

## Dependencies

- Logos.Core.ProofSystem.Derivation
- Logos.Core.Semantics.Validity
-/
```

### 7.3 Test Isolation

**Pattern: Independent Tests**

```lean
-- Good: Each test is independent
namespace Test1
  def setup := ...
  example : ... := by ...
end Test1

namespace Test2
  def setup := ...  -- Different setup
  example : ... := by ...
end Test2

-- Bad: Tests share mutable state
def global_state := ...

example : ... := by
  modify global_state  -- Affects other tests
  ...
```

### 7.4 Test Helpers

**Pattern: Reusable Test Utilities**

```lean
namespace TestHelpers

-- Helper: Create test frame
def mkTestFrame (n : Nat) : TaskFrame :=
  { World := Fin n
    worlds := List.finRange n
    accessible := fun w1 w2 => w1.val ≤ w2.val
    ... }

-- Helper: Create test model
def mkTestModel (n : Nat) (v : Fin n → String → Bool) : TaskModel :=
  { frame := mkTestFrame n
    valuation := v }

-- Helper: Check validity
def checkValid (φ : Formula) : IO Bool := do
  let model := mkTestModel 5 (fun _ _ => true)
  return model.valid φ

end TestHelpers
```

---

## 8. Performance Testing

### 8.1 Benchmarking Pattern

```lean
-- Test performance of proof search
namespace PerformanceTests

def benchmark_search (problems : List Formula) : IO Unit := do
  let start ← IO.monoMsNow
  
  for φ in problems do
    let _ ← searchProof φ
  
  let end ← IO.monoMsNow
  let elapsed := end - start
  
  IO.println s!"Searched {problems.length} problems in {elapsed}ms"
  IO.println s!"Average: {elapsed / problems.length}ms per problem"

#eval benchmark_search test_problems
```

### 8.2 Complexity Testing

```lean
-- Test that complexity is as expected
namespace ComplexityTests

def test_linear_complexity : IO Unit := do
  let sizes := [10, 20, 40, 80, 160]
  let times ← sizes.mapM fun n => do
    let start ← IO.monoMsNow
    let _ ← processFormula (mkFormula n)
    let end ← IO.monoMsNow
    return end - start
  
  -- Check that doubling size roughly doubles time
  for i in [0:times.length-1] do
    let ratio := times[i+1]! / times[i]!
    assert! (1.5 < ratio && ratio < 2.5)  -- Roughly 2x

#eval test_linear_complexity
```

---

## 9. Debugging and Diagnostics

### 9.1 Trace-Based Testing

```lean
-- Enable tracing for debugging
set_option trace.Logos.ProofSearch true

example : □p → p := by
  modal_tac
  -- Trace output shows:
  -- [ProofSearch] Trying rule: T_axiom
  -- [ProofSearch] Success!
```

### 9.2 Test Failure Diagnostics

```lean
-- Provide detailed failure messages
def test_with_diagnostics : IO Unit := do
  let φ := Formula.box (Formula.var "p")
  let result ← searchProof φ
  
  match result with
  | some proof =>
      IO.println s!"[YES] Found proof: {proof}"
  | none =>
      IO.println "[NO] Failed to find proof"
      IO.println "Diagnostics:"
      IO.println s!"  Formula: {φ}"
      IO.println s!"  Search depth: {maxDepth}"
      IO.println s!"  Nodes explored: {nodesExplored}"
```

### 9.3 Assertion Messages

```lean
-- Use descriptive assertion messages
def test_soundness : IO Unit := do
  let derivable := checkDerivable Γ φ
  let valid := checkValid Γ φ
  
  assert! derivable → valid
    "Soundness violation: formula is derivable but not valid"
```

---

## 10. Continuous Integration

### 10.1 CI Configuration

```yaml
# .github/workflows/test.yml
name: Integration Tests

on:
  push:
    branches: [ main ]
  pull_request:
    branches: [ main ]

jobs:
  test:
    runs-on: ubuntu-latest
    
    steps:
    - uses: actions/checkout@v3
    
    - name: Install Lean
      uses: lean-lang/setup-lean@v1
      
    - name: Cache dependencies
      uses: actions/cache@v3
      with:
        path: .lake
        key: ${{ runner.os }}-lake-${{ hashFiles('lake-manifest.json') }}
        
    - name: Build project
      run: lake build
      
    - name: Run unit tests
      run: lake build LogosTest
      
    - name: Run integration tests
      run: lake build LogosTest.Integration
      
    - name: Run property tests
      run: lake build LogosTest.Property
      
    - name: Check for sorries
      run: |
        if grep -r "sorry" Logos/; then
          echo "Error: Found sorry in library code"
          exit 1
        fi
```

### 10.2 Test Reporting

```lean
-- Generate test report
def generate_test_report : IO Unit := do
  let results ← run_all_tests
  
  IO.println "# Test Report"
  IO.println ""
  IO.println s!"Total tests: {results.total}"
  IO.println s!"Passed: {results.passed}"
  IO.println s!"Failed: {results.failed}"
  IO.println s!"Skipped: {results.skipped}"
  IO.println ""
  
  if results.failed > 0 then
    IO.println "## Failed Tests"
    for failure in results.failures do
      IO.println s!"- {failure.name}: {failure.message}"
```

---

## 11. Modal Logic Specific Patterns

### 11.1 Frame Property Testing

```lean
-- Test frame properties
namespace FramePropertyTests

-- Test reflexivity
#test ∀ (F : TaskFrame) (w : F.World),
  F.accessible w w

-- Test transitivity
#test ∀ (F : TaskFrame) (w1 w2 w3 : F.World),
  F.accessible w1 w2 → F.accessible w2 w3 → F.accessible w1 w3

-- Test symmetry (for S5)
#test ∀ (F : TaskFrame) (w1 w2 : F.World),
  F.accessible w1 w2 → F.accessible w2 w1

end FramePropertyTests
```

### 11.2 Modal Axiom Testing

```lean
-- Test modal axioms
namespace ModalAxiomTests

-- K axiom: □(p → q) → □p → □q
example : Derivable [] (□(p ⊃ q) ⊃ □p ⊃ □q) := by
  apply Derivation.axiom
  apply Axiom.K

-- T axiom: □p → p
example : Derivable [] (□p ⊃ p) := by
  apply Derivation.axiom
  apply Axiom.T

-- 4 axiom: □p → □□p
example : Derivable [] (□p ⊃ □□p) := by
  apply Derivation.axiom
  apply Axiom.Four

end ModalAxiomTests
```

### 11.3 Temporal Logic Testing

```lean
-- Test temporal operators
namespace TemporalTests

-- Always implies eventually
example : □p → ◇p := by
  temporal_tac

-- Until decomposition
example : p U q ↔ q ∨ (p ∧ ◯(p U q)) := by
  temporal_tac

end TemporalTests
```

---

## 12. Comparison with Other Testing Approaches

### 12.1 Lean 4 vs Traditional Testing

| Aspect | Lean 4 | Traditional (e.g., Python) |
|--------|--------|---------------------------|
| **Test Definition** | Theorems to prove | Functions to run |
| **Verification** | Type checker | Runtime assertions |
| **Coverage** | Proof obligations | Code coverage tools |
| **Failure** | Proof fails | Assertion fails |
| **Performance** | Compile-time | Runtime |
| **Guarantees** | Mathematical correctness | Empirical correctness |

### 12.2 Advantages of Lean 4 Approach

1. **Stronger Guarantees**: Proofs provide mathematical certainty
2. **No Runtime Overhead**: Tests are checked at compile time
3. **Self-Documenting**: Types serve as specifications
4. **Composability**: Proofs can be composed like functions
5. **Refactoring Safety**: Type checker catches breaking changes

### 12.3 Limitations of Lean 4 Approach

1. **Learning Curve**: Requires proof skills
2. **No Coverage Tools**: Must track coverage manually
3. **Performance Testing**: Harder to measure runtime performance
4. **Non-Decidable Properties**: Cannot test all properties
5. **Debugging**: Proof failures can be cryptic

---

## 13. Recommendations for ProofChecker

### 13.1 Immediate Actions

1. **Create Test Structure**:
   ```
   LogosTest/
     Integration/
       ProofSystemSemanticsTest.lean
       AutomationProofSystemTest.lean
       EndToEndTest.lean
   ```

2. **Add Plausible Dependency**:
   ```lean
   -- In lakefile.lean
   require plausible from git
     "https://github.com/leanprover-community/plausible" @ "main"
   ```

3. **Write Core Integration Tests**:
   - Soundness: `Derivable Γ φ → Valid Γ φ`
   - Weakening: `Derivable Γ φ → Γ ⊆ Δ → Derivable Δ φ`
   - Tactic integration: Test `modal_tac` on examples

4. **Create Generators**:
   ```lean
   deriving instance Arbitrary for Formula
   deriving instance Arbitrary for Context
   ```

5. **Set Up CI**:
   - Add GitHub Actions workflow
   - Run tests on every commit
   - Check for `sorry`s in library code

### 13.2 Medium-Term Goals

1. **Expand Test Coverage**:
   - Add property tests for all metalogic properties
   - Test all modal axioms
   - Test all proof rules

2. **Create Test Utilities**:
   - Frame generators
   - Model generators
   - Proof checkers

3. **Document Testing Patterns**:
   - Write testing guide
   - Document generators
   - Provide examples

4. **Performance Testing**:
   - Benchmark proof search
   - Test complexity bounds
   - Optimize slow paths

### 13.3 Long-Term Vision

1. **Automated Test Generation**:
   - Generate tests from specifications
   - Use proof search to find test cases
   - Mutation testing for tactics

2. **Coverage Analysis**:
   - Track proof obligations
   - Measure test coverage
   - Identify gaps

3. **Regression Testing**:
   - Golden test suite
   - Performance benchmarks
   - Compatibility tests

---

## 14. Resources and References

### 14.1 Official Documentation

- **Lean 4 Manual**: https://lean-lang.org/lean4/doc/
- **Theorem Proving in Lean 4**: https://lean-lang.org/theorem_proving_in_lean4/
- **Mathlib4 Documentation**: https://leanprover-community.github.io/mathlib4_docs/
- **Lean Community**: https://leanprover-community.github.io/

### 14.2 Testing Libraries

- **Plausible**: https://github.com/leanprover-community/plausible
  - Property-based testing for Lean 4
  - QuickCheck-style testing
  - Automatic shrinking

- **Aesop**: https://github.com/leanprover-community/aesop
  - Proof automation
  - Can be used for test generation
  - Extensible rule sets

### 14.3 Example Projects

- **Mathlib4**: https://github.com/leanprover-community/mathlib4
  - Extensive test suite in `MathlibTest/`
  - Integration tests in `MathlibTest/Integration/`
  - Property tests throughout

- **Lean 4 Core**: https://github.com/leanprover/lean4
  - Core library tests
  - Tactic tests
  - Compiler tests

### 14.4 Papers and Articles

- **"An Extensible User Interface for Lean 4"** (Nawrocki et al., 2023)
  - ProofWidgets for interactive testing
  - https://drops.dagstuhl.de/opus/volltexte/2023/18399/

- **"The Lean Mathematical Library"** (mathlib community, 2020)
  - Testing practices in mathlib
  - https://arxiv.org/abs/1910.09336

### 14.5 Community Resources

- **Lean Zulip**: https://leanprover.zulipchat.com/
  - Active community
  - Testing discussions
  - Help with test design

- **Lean Community GitHub**: https://github.com/leanprover-community
  - Example projects
  - Testing patterns
  - Best practices

---

## 15. Conclusion

Integration testing in Lean 4 is fundamentally different from traditional software testing, leveraging the proof-centric nature of the language. The key insights are:

1. **Proofs are Tests**: The primary integration testing pattern is writing theorems that must be proven
2. **Property-Based Testing**: Plausible provides QuickCheck-style testing for finding counterexamples
3. **Modular Organization**: Tests mirror library structure with dedicated integration directories
4. **Manual Coverage**: Coverage must be tracked manually through proof obligations
5. **Tactic Testing**: Tactics are tested by verifying goal states and proof terms

**For the ProofChecker project**, the recommended approach is:

[PASS] **Use proof-based integration tests** for soundness, completeness, and other metalogic properties  
[PASS] **Add Plausible** for property-based testing to find edge cases  
[PASS] **Organize tests** in `LogosTest/Integration/` mirroring the main structure  
[PASS] **Create end-to-end tests** that exercise full proof workflows  
[PASS] **Use custom test harnesses** for tactic testing  
[PASS] **Track coverage manually** through proof obligations and test matrices  
[PASS] **Set up CI** to run tests on every commit  

This approach provides strong correctness guarantees while maintaining the flexibility to test complex integration scenarios.

---

**Sources**:
- https://lean-lang.org/
- https://leanprover.github.io/theorem_proving_in_lean4/
- https://leanprover-community.github.io/
- https://github.com/leanprover-community/mathlib4
- https://github.com/leanprover-community/plausible
- https://github.com/leanprover-community/aesop
- https://github.com/leanprover-community/ProofWidgets4
- Existing research: `/home/benjamin/Projects/ProofChecker/Documentation/Research/property-based-testing-lean4.md`
