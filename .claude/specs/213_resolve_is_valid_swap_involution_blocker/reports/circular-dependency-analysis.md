# Circular Dependency Analysis: Truth.lean ↔ Soundness.lean

**Date**: 2025-12-28  
**Task**: 213  
**Type**: Technical Analysis  
**Author**: System Analysis

---

## Executive Summary

This report provides a detailed analysis of the circular dependency between `Truth.lean` and `Soundness.lean` discovered during task 213 implementation, explains why it occurs, and provides concrete architectural solutions to avoid such dependencies in the future.

**Key Finding**: The temporal_duality case in `derivable_implies_swap_valid` theorem requires the soundness theorem to complete, but soundness is proven in `Soundness.lean`, which transitively imports `Truth.lean`. This creates a circular dependency that cannot be resolved without architectural changes.

**Immediate Solution**: Accept the `sorry` in Truth.lean and complete the temporal_duality soundness case in Soundness.lean after the main soundness theorem is proven.

**Long-term Solution**: Restructure the module hierarchy to separate semantic properties from proof system properties, following established patterns from Lean's mathlib.

---

## Table of Contents

1. [Circular Dependency Explained](#circular-dependency-explained)
2. [Root Cause Analysis](#root-cause-analysis)
3. [Why This Dependency is Problematic](#why-this-dependency-is-problematic)
4. [Current Dependency Graph](#current-dependency-graph)
5. [The Attempted Solution and Why It Failed](#the-attempted-solution-and-why-it-failed)
6. [Architectural Solutions](#architectural-solutions)
7. [Recommended Refactoring Plan](#recommended-refactoring-plan)
8. [Prevention Strategies](#prevention-strategies)
9. [Lessons Learned](#lessons-learned)

---

## Circular Dependency Explained

### What is the Circular Dependency?

The circular dependency occurs in the following module import chain:

```
Truth.lean
  → (needs soundness theorem to complete temporal_duality case)
  → Soundness.lean
    → imports Validity.lean
      → imports Truth.lean
        → (circular!)
```

### Detailed Import Chain

```lean
-- Soundness.lean (line 1-2)
import Logos.Core.ProofSystem.Derivation
import Logos.Core.Semantics.Validity

-- Validity.lean (line 1-2)
import Logos.Core.Semantics.Truth
import Logos.Core.Syntax.Context

-- Truth.lean (line 1-5)
import Logos.Core.Semantics.TaskModel
import Logos.Core.Semantics.WorldHistory
import Logos.Core.Syntax.Formula
import Logos.Core.ProofSystem.Axioms
import Logos.Core.ProofSystem.Derivation
```

**Dependency Path**:
```
Soundness.lean → Validity.lean → Truth.lean
```

**Problem**: Truth.lean needs to use the soundness theorem from Soundness.lean, but Soundness.lean transitively imports Truth.lean.

### The Specific Case

In `Truth.lean` at lines 1233-1256, the `temporal_duality` case of `derivable_implies_swap_valid`:

```lean
| temporal_duality ψ' h_ψ' ih =>
  intro h_eq
  -- Temporal duality: from Derivable [] ψ', conclude Derivable [] ψ'.swap
  -- Goal: is_valid (ψ'.swap).swap
  -- By involution: (ψ'.swap).swap = ψ', so goal is: is_valid ψ'
  
  -- NOTE: This case requires the soundness theorem to complete.
  -- We have h_ψ' : DerivationTree [] ψ' and need is_valid T ψ'.
  -- The soundness theorem states: DerivationTree [] φ → is_valid T φ.
  -- However, soundness is proven in Soundness.lean, which imports this file.
  -- Therefore, we cannot use soundness here without creating a circular dependency.
  
  sorry
```

**What we have**: `h_ψ' : DerivationTree [] ψ'`  
**What we need**: `is_valid T ψ'`  
**What bridges the gap**: Soundness theorem `DerivationTree [] φ → is_valid T φ`  
**Where it's defined**: `Soundness.lean`  
**Why we can't use it**: `Soundness.lean` imports `Truth.lean` (transitively via `Validity.lean`)

---

## Root Cause Analysis

### 1. Architectural Design Issue

The root cause is a **violation of the dependency hierarchy principle**: higher-level modules (soundness/metalogic) should depend on lower-level modules (semantics), but lower-level modules should never depend on higher-level modules.

**Current Hierarchy Violation**:
```
Layer 3: Soundness.lean (metalogic - highest level)
   ↑
Layer 2: Validity.lean (semantic consequence)
   ↑
Layer 1: Truth.lean (semantic truth)
   ↓ (VIOLATION: trying to use soundness from Layer 3)
Layer 3: Soundness.lean
```

### 2. Mixing Concerns

`Truth.lean` contains two different kinds of theorems:

1. **Pure semantic theorems**: Properties of `truth_at` and `is_valid` that don't reference the proof system
2. **Bridge theorems**: Theorems that connect the proof system (derivations) to semantics (validity)

The `derivable_implies_swap_valid` theorem is a **bridge theorem** because it starts with a derivation (`DerivationTree`) and proves a semantic property (`is_valid`).

**Problem**: Bridge theorems naturally require both proof system properties AND semantic properties, making them prone to circular dependencies.

### 3. Temporal Duality Rule Special Case

The temporal duality rule is unique because:

1. It's a **self-referential rule**: `DerivationTree [] ψ` implies `DerivationTree [] ψ.swap`
2. Proving its soundness requires knowing that derivable formulas are valid (i.e., soundness itself)
3. Other rules (axiom, modus_ponens, necessitation) can be proven sound using only semantic reasoning

**Why other rules don't have this problem**:
- **Axiom case**: Axioms are valid by semantic definition (proven in `axiom_swap_valid`)
- **Modus ponens case**: If premises are valid, conclusion is valid (direct semantic reasoning)
- **Necessitation case**: If ψ is valid, □ψ is valid (semantic property of □)
- **Temporal duality case**: If ψ is derivable, ψ.swap is derivable, so ψ.swap is valid... **WAIT, HOW DO WE KNOW DERIVABLE IMPLIES VALID?** That's the soundness theorem!

### 4. The Involution Trap

The original implementation attempted to use `is_valid_swap_involution`:
```lean
theorem is_valid_swap_involution : is_valid T φ.swap → is_valid T φ
```

This seemed like a pure semantic theorem that would avoid the soundness dependency. However:

1. Task 213 research proved this theorem is **semantically false** for arbitrary formulas
2. It only holds for **derivable** formulas (where temporal_duality guarantees swap preservation)
3. Therefore, any proof would still require derivability, leading back to soundness

**Circular reasoning**:
- To prove `is_valid_swap_involution` for derivable formulas, we need soundness
- But we're trying to use `is_valid_swap_involution` to prove part of soundness
- This is circular!

---

## Why This Dependency is Problematic

### 1. Compilation Failure

Circular dependencies prevent compilation:
```
Error: cyclic dependency detected
Soundness.lean → Validity.lean → Truth.lean → Soundness.lean
```

Lean's module system strictly forbids circular imports to ensure:
- Unambiguous initialization order
- Deterministic type checking
- Sound proof checking

### 2. Logical Unsoundness Risk

Circular dependencies in theorem proving can lead to **logical inconsistencies**:

```lean
-- In Truth.lean
axiom soundness : DerivationTree [] φ → is_valid T φ

-- In Soundness.lean (using Truth.lean)
theorem soundness : DerivationTree [] φ → is_valid T φ := by
  -- Proof uses Truth.lean
  ...
```

This is circular reasoning: we assume soundness to prove soundness!

### 3. Maintainability Issues

Circular dependencies make code:
- **Hard to understand**: Developers must understand both modules simultaneously
- **Hard to modify**: Changes in one module may break the other unpredictably
- **Hard to test**: Cannot test modules independently
- **Hard to reuse**: Cannot use one module without the other

### 4. Violation of Mathematical Structure

In mathematical logic, there's a natural hierarchy:

```
Syntax (formulas, derivations)
   ↓
Semantics (models, truth, validity)
   ↓
Metalogic (soundness, completeness, decidability)
```

Circular dependencies violate this structure, making the formalization unclear and error-prone.

---

## Current Dependency Graph

### Module-Level Dependencies

```
┌─────────────────────────────────────────────────────────────┐
│                      METALOGIC LAYER                        │
│  ┌─────────────────────────────────────────────────────┐   │
│  │ Soundness.lean                                      │   │
│  │ • Proves: Derivable → Valid                         │   │
│  │ • Imports: Validity, Derivation                     │   │
│  └──────────────────┬──────────────────────────────────┘   │
└─────────────────────┼───────────────────────────────────────┘
                      │
                      ↓ (imports)
┌─────────────────────────────────────────────────────────────┐
│                     SEMANTICS LAYER                         │
│  ┌─────────────────────────────────────────────────────┐   │
│  │ Validity.lean                                       │   │
│  │ • Defines: semantic consequence (Γ ⊨ φ)             │   │
│  │ • Imports: Truth, Context                           │   │
│  └──────────────────┬──────────────────────────────────┘   │
│                     ↓ (imports)                             │
│  ┌─────────────────────────────────────────────────────┐   │
│  │ Truth.lean                                          │   │
│  │ • Defines: truth_at, is_valid                       │   │
│  │ • Contains: derivable_implies_swap_valid            │   │
│  │ • WANTS: soundness (from Soundness.lean) ← PROBLEM! │   │
│  │ • Imports: TaskModel, Formula, Derivation           │   │
│  └──────────────────┬──────────────────────────────────┘   │
└─────────────────────┼───────────────────────────────────────┘
                      │
                      ↓ (imports)
┌─────────────────────────────────────────────────────────────┐
│                    PROOF SYSTEM LAYER                       │
│  ┌─────────────────────────────────────────────────────┐   │
│  │ Derivation.lean                                     │   │
│  │ • Defines: DerivationTree ([] ⊢ φ)                  │   │
│  │ • Imports: Axioms, Context, Formula                 │   │
│  └─────────────────────────────────────────────────────┘   │
│  ┌─────────────────────────────────────────────────────┐   │
│  │ Axioms.lean                                         │   │
│  │ • Defines: Axiom type (prop_k, modal_t, etc.)       │   │
│  │ • Imports: Formula                                  │   │
│  └─────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────┘
```

### The Circular Path

```
Truth.lean (wants soundness)
   ↑
   │ (imports)
   │
Validity.lean
   ↑
   │ (imports)
   │
Soundness.lean (defines soundness)
   │
   └──→ (circular!)
```

---

## The Attempted Solution and Why It Failed

### Attempt 1: Use `is_valid_swap_involution`

**Idea**: Prove a pure semantic theorem `is_valid T φ.swap → is_valid T φ` and use it to avoid soundness dependency.

**Implementation**:
```lean
theorem is_valid_swap_involution (φ : Formula) (h : is_valid T φ.swap) : is_valid T φ
```

**Why it failed**: Task 213 research proved this theorem is **semantically false** for arbitrary formulas:

**Counterexample**:
```lean
φ = all_past(atom "p")  -- "p was always true in the past"
Model M where:
  - p is false at all past times (s < t)
  - p is true at all future times (s > t)

φ.swap = all_future(atom "p")  -- "p will always be true in the future"

is_valid M φ.swap = true   -- p is true in all future times
is_valid M φ = false       -- p is false in all past times

∴ is_valid φ.swap ↛ is_valid φ  (theorem is false!)
```

**Fundamental issue**: `swap` exchanges `all_past` ↔ `all_future`, which quantify over **different time ranges** (past s<t vs future s>t). These are not symmetric in arbitrary temporal models.

### Attempt 2: Restrict to Derivable Formulas

**Idea**: The theorem IS true for derivable formulas because the temporal_duality rule guarantees swap preservation.

**Implementation**:
```lean
theorem derivable_valid_swap_involution {φ : Formula} 
    (h_deriv : DerivationTree [] φ.swap) : is_valid T φ
```

**Why it failed**: To prove this, we need to:
1. Use soundness to get `is_valid T φ.swap` from `h_deriv`
2. Then somehow get `is_valid T φ`

But step 2 requires knowing that φ is derivable (to use temporal_duality), which requires:
- `DerivationTree [] φ` from `DerivationTree [] φ.swap`
- This is temporal_duality **backward**
- To prove temporal_duality is sound, we need... soundness!

**Circular!**

### Attempt 3: Derivation Induction

**Idea**: Prove `derivable_implies_swap_valid` by induction on the derivation structure.

**Implementation**: This is the current approach in Truth.lean (lines 1192-1274).

**Why it partially worked**: All cases EXCEPT temporal_duality can be proven:
- Axiom case: Proven via semantic reasoning on axioms
- Modus ponens: Proven via semantic reasoning on implication
- Necessitation: Proven via semantic reasoning on □
- Temporal necessitation: Proven via semantic reasoning on F/P

**Why temporal_duality case fails**:
```lean
| temporal_duality ψ' h_ψ' ih =>
  -- We have: DerivationTree [] ψ' (the premise)
  -- We need: is_valid T ψ' (to complete the proof)
  -- The bridge: soundness theorem
  -- The problem: soundness is in Soundness.lean!
```

The IH gives us `is_valid T ψ'.swap`, but we need `is_valid T ψ'`. The only way to get this from `DerivationTree [] ψ'` is to use soundness.

---

## Architectural Solutions

### Solution 1: Accept the Sorry (Current Approach)

**Approach**: Leave the temporal_duality case as `sorry` in Truth.lean and complete it in Soundness.lean after proving the main soundness theorem.

**Implementation**:
```lean
-- In Truth.lean (current)
| temporal_duality ψ' h_ψ' ih =>
  sorry  -- Completed in Soundness.lean

-- In Soundness.lean (future work)
theorem derivable_implies_swap_valid_complete :
    ∀ {φ : Formula}, DerivationTree [] φ → is_valid T φ.swap_past_future := by
  intro φ h_deriv
  -- Now we can use the main soundness theorem!
  have h_sound : is_valid T φ := soundness h_deriv
  -- And complete the temporal_duality case properly
  ...
```

**Pros**:
- [PASS] Simple and immediate
- [PASS] No architectural changes needed
- [PASS] Clearly documented why the sorry exists
- [PASS] Clear path to completion (in Soundness.lean)

**Cons**:
- [FAIL] Leaves a sorry in the codebase (but documented and intentional)
- [FAIL] Doesn't solve the structural problem for future similar cases

**Status**: **Implemented** (current solution)

### Solution 2: Extract Bridge Theorems to Separate Module

**Approach**: Create a new module `Soundness/DualityLemmas.lean` (or similar) that contains bridge theorems requiring both proof system and semantics.

**Module Structure**:
```
Soundness/
  ├── DualityLemmas.lean     (NEW - contains derivable_implies_swap_valid)
  ├── Soundness.lean         (imports DualityLemmas)
  └── AxiomValidity.lean     (pure semantic proofs)

Semantics/
  ├── Truth.lean             (NO LONGER has derivable_implies_swap_valid)
  ├── Validity.lean
  └── TaskModel.lean
```

**Dependency Graph**:
```
Soundness.lean
   ↓ (imports)
DualityLemmas.lean
   ↓ (imports)
Truth.lean (no longer needs Soundness!)
```

**Implementation**:
```lean
-- In DualityLemmas.lean (new file)
import Logos.Core.Semantics.Truth
import Logos.Core.ProofSystem.Derivation
-- Note: Does NOT import Soundness

theorem derivable_implies_swap_valid_partial :
    ∀ {φ : Formula}, DerivationTree [] φ → is_valid T φ.swap_past_future := by
  -- All cases except temporal_duality (uses axiom_swap_valid from Truth.lean)
  ...
  | temporal_duality ψ' h_ψ' ih =>
    sorry  -- Completed in Soundness.lean

-- In Soundness.lean
import Logos.Core.Soundness.DualityLemmas

theorem soundness : DerivationTree Γ φ → Γ ⊨ φ := by
  -- Main soundness proof
  ...

theorem derivable_implies_swap_valid_complete :
    ∀ {φ : Formula}, DerivationTree [] φ → is_valid T φ.swap_past_future := by
  -- Complete the temporal_duality case using soundness
  ...
```

**Pros**:
- [PASS] Cleaner module organization
- [PASS] Separates pure semantics from proof-system bridges
- [PASS] Makes dependencies explicit
- [PASS] Easier to understand what depends on what

**Cons**:
- [WARN] Requires creating new module
- [WARN] Need to move `derivable_implies_swap_valid` from Truth.lean
- [WARN] Need to update imports in multiple files

**Status**: **Recommended for future refactoring**

### Solution 3: Split Truth.lean into Semantic and Metatheoretic Parts

**Approach**: Divide Truth.lean into:
1. `Truth.lean` - Pure semantic theorems only
2. `TruthMetatheory.lean` - Theorems connecting derivations to semantics

**Module Structure**:
```
Semantics/
  ├── Truth.lean              (pure semantic theorems)
  └── TruthMetatheory.lean    (NEW - bridge theorems)

Metalogic/
  ├── Soundness.lean          (imports TruthMetatheory)
  └── Completeness.lean
```

**What goes where**:

**Truth.lean** (pure semantics):
- `truth_at` definition
- `is_valid` definition
- `truth_at_swap_swap` helper lemma
- Pure semantic lemmas about truth and validity

**TruthMetatheory.lean** (bridge):
- `axiom_swap_valid` (connects Axiom to is_valid)
- `derivable_implies_swap_valid` (connects DerivationTree to is_valid)
- Any theorem that mentions both `DerivationTree` and `is_valid`

**Dependency Graph**:
```
Soundness.lean
   ↓
TruthMetatheory.lean
   ↓                    ↓
Truth.lean       Derivation.lean
```

**Pros**:
- [PASS] Very clean separation of concerns
- [PASS] Pure semantics module (Truth.lean) has no proof system dependencies
- [PASS] Bridge theorems clearly identified in TruthMetatheory.lean
- [PASS] Follows mathlib patterns for similar separations

**Cons**:
- [WARN] More significant refactoring required
- [WARN] Need to update many import statements
- [WARN] Need to decide boundary between Truth and TruthMetatheory

**Status**: **Best practice for large-scale refactoring**

### Solution 4: Use Mutual Recursion / Mutual Import (NOT RECOMMENDED)

**Approach**: Make Truth.lean and Soundness.lean mutually recursive.

**Why this is a bad idea**:
- [FAIL] Lean does not support mutual imports between files
- [FAIL] Would require combining both files into one (losing modularity)
- [FAIL] Would make the codebase much harder to understand
- [FAIL] Would violate logical layering principles

**Status**: **Rejected**

---

## Recommended Refactoring Plan

### Phase 1: Short-term (Current - Complete)

[PASS] **Accept the sorry** in Truth.lean with clear documentation  
[PASS] **Document the circular dependency** in comments  
[PASS] **Plan to complete in Soundness.lean** after main soundness theorem

**Status**: Implemented in task 213

### Phase 2: Medium-term (Next 6-12 months)

**Goal**: Extract bridge theorems to separate module

**Steps**:
1. Create `Logos/Core/Metalogic/SoundnessLemmas.lean` (or similar name)
2. Move `derivable_implies_swap_valid` from Truth.lean to SoundnessLemmas.lean
3. Move `axiom_swap_valid` and related lemmas to SoundnessLemmas.lean
4. Update imports in Soundness.lean to import SoundnessLemmas
5. Complete the temporal_duality case in Soundness.lean using main soundness theorem
6. Update tests and documentation

**Effort**: ~4-6 hours

**Benefits**:
- Clean module organization
- No sorries in codebase
- Clear separation of pure semantics from metatheory

### Phase 3: Long-term (Future Major Refactoring)

**Goal**: Split Truth.lean into semantic and metatheoretic parts (Solution 3)

**Steps**:
1. Analyze all theorems in Truth.lean
2. Classify as "pure semantic" vs "bridge/metatheoretic"
3. Create new Truth/Metatheory.lean module
4. Move bridge theorems to Metatheory.lean
5. Update all imports across the codebase
6. Verify all proofs still compile
7. Update documentation and module organization guide

**Effort**: ~12-16 hours

**Benefits**:
- Best practice module organization
- Follows mathlib patterns
- Clear conceptual boundaries
- Prevents future circular dependencies
- Makes codebase easier to navigate and understand

---

## Prevention Strategies

### Strategy 1: Module Dependency Policy

**Policy**: Establish strict layering rules for module dependencies.

**Layers**:
```
Layer 4: Applications (Examples, Tests)
   ↓ (may import)
Layer 3: Metalogic (Soundness, Completeness, Decidability)
   ↓ (may import)
Layer 2: Semantics (Truth, Validity, Models)
   ↓ (may import)
Layer 1: Syntax + Proof System (Formulas, Derivations, Axioms)
   ↓ (may import)
Layer 0: Foundations (List, Nat, basic definitions)
```

**Rule**: Higher layers may import lower layers, but **never** the reverse.

**Enforcement**:
- Document layer membership in module headers
- Code review checklist: "Does this import violate layering?"
- Automated linting (if possible): Check for upward imports

**Example Module Header**:
```lean
/-!
# Truth - Semantic Truth Definitions

**Layer**: 2 (Semantics)
**Imports**: Layer 1 (Syntax, Proof System), Layer 0 (Foundations)
**Imported by**: Layer 3 (Metalogic), Layer 2 (Validity)
-/
```

### Strategy 2: Bridge Module Pattern

**Pattern**: Create intermediate "bridge" modules for theorems that connect two layers.

**Structure**:
```
Layer N+1:  Metalogic
   ↓
Layer N+0.5: MetalogicBridges   (NEW - contains bridge theorems)
   ↓
Layer N:    Semantics
```

**Example**:
- `Soundness.lean` (Layer 3) uses theorems from `SoundnessLemmas.lean` (Layer 2.5)
- `SoundnessLemmas.lean` (Layer 2.5) imports `Truth.lean` (Layer 2) and `Derivation.lean` (Layer 1)
- No circular dependencies!

**Benefits**:
- Clear home for theorems that connect layers
- Prevents circular dependencies by design
- Makes dependencies explicit and understandable

### Strategy 3: Design-Time Dependency Analysis

**Process**: Before adding a new theorem, ask:

1. **What does this theorem import?** (What definitions/theorems does it use?)
2. **What layer does it belong to?** (Based on its imports)
3. **Who will import this theorem?** (What will use it?)
4. **Would this create a cycle?** (Check if any imports would try to import this)

**Example Analysis** for `derivable_implies_swap_valid`:

1. **Imports**: `DerivationTree` (Layer 1), `is_valid` (Layer 2)
2. **Layer**: Layer 2.5 (bridge - connects derivations to semantics)
3. **Imported by**: `Soundness.lean` (Layer 3)
4. **Cycle check**: Soundness.lean imports Validity.lean imports Truth.lean. If Truth.lean contains this theorem, and it tries to use soundness, that's a cycle! → Move to separate module.

**Decision**: Move `derivable_implies_swap_valid` to `SoundnessLemmas.lean` (Layer 2.5)

### Strategy 4: Completion Tracking

**Pattern**: For theorems with `sorry` placeholders, document:

1. **Why the sorry exists** (e.g., circular dependency)
2. **Where it will be completed** (module + rough timeline)
3. **What's needed to complete it** (e.g., main soundness theorem)

**Example**:
```lean
| temporal_duality ψ' h_ψ' ih =>
  -- TODO: Complete in Soundness.lean after main soundness theorem proven
  -- Requires: DerivationTree [] φ → is_valid T φ
  -- Blocked by: Circular dependency (Soundness.lean imports this file)
  -- Timeline: After task 135 (soundness proof completion)
  -- Tracked in: SORRY_REGISTRY.md, line 42
  sorry
```

**Benefits**:
- Clear understanding of why sorries exist
- Clear path to completion
- Prevents forgotten sorries
- Enables tracking of proof progress

### Strategy 5: Automatic Dependency Checking

**Tool**: Create a script to detect potential circular dependencies before they cause compilation errors.

**Implementation**:
```python
# scripts/check_dependencies.py
import os
import re
from collections import defaultdict, deque

def extract_imports(filepath):
    """Extract all import statements from a Lean file."""
    with open(filepath, 'r') as f:
        content = f.read()
    imports = re.findall(r'import\s+([\w.]+)', content)
    return imports

def build_dependency_graph(root_dir):
    """Build a dependency graph of all Lean files."""
    graph = defaultdict(list)
    for root, dirs, files in os.walk(root_dir):
        for file in files:
            if file.endswith('.lean'):
                filepath = os.path.join(root, file)
                module = filepath_to_module(filepath, root_dir)
                imports = extract_imports(filepath)
                graph[module] = imports
    return graph

def detect_cycles(graph):
    """Detect circular dependencies using DFS."""
    visited = set()
    rec_stack = set()
    cycles = []
    
    def dfs(node, path):
        if node in rec_stack:
            # Found a cycle
            cycle_start = path.index(node)
            cycles.append(path[cycle_start:] + [node])
            return
        if node in visited:
            return
        
        visited.add(node)
        rec_stack.add(node)
        
        for neighbor in graph.get(node, []):
            dfs(neighbor, path + [neighbor])
        
        rec_stack.remove(node)
    
    for node in graph:
        dfs(node, [node])
    
    return cycles

# Usage
graph = build_dependency_graph('Logos/')
cycles = detect_cycles(graph)
if cycles:
    print("WARNING: Circular dependencies detected!")
    for cycle in cycles:
        print(" → ".join(cycle))
else:
    print("No circular dependencies found.")
```

**Integration**:
- Run as pre-commit hook
- Run in CI/CD pipeline
- Run before major refactorings

---

## Lessons Learned

### Lesson 1: Semantic vs. Metatheoretic Theorems

**Insight**: Carefully distinguish between:
- **Semantic theorems**: Properties of truth, validity, models (e.g., `truth_at_swap_swap`)
- **Metatheoretic theorems**: Properties connecting syntax to semantics (e.g., soundness, completeness)

**Application**: Semantic theorems belong in `Semantics/` modules, metatheoretic theorems belong in `Metalogic/` or bridge modules.

### Lesson 2: The Involution Property is Not Universal

**Insight**: Just because a syntactic operation has an algebraic property (e.g., `φ.swap.swap = φ`) doesn't mean the corresponding semantic property holds (e.g., `is_valid φ.swap → is_valid φ`).

**Application**: Always verify semantic properties independently, even if the syntax suggests they should hold.

**Example**: Task 213 discovered that `is_valid_swap_involution` is false for arbitrary formulas, even though swap is syntactically an involution.

### Lesson 3: Temporal Operators Break Symmetry

**Insight**: Temporal operators `all_past` and `all_future` quantify over different time ranges (past s<t vs future s>t), making them fundamentally asymmetric in arbitrary temporal models.

**Application**: Theorems about temporal duality must account for this asymmetry and typically require derivability constraints (proof system) rather than pure semantic constraints.

### Lesson 4: Circular Dependencies Signal Design Issues

**Insight**: When you encounter a circular dependency, it's usually not just a technical problem - it's a sign that the module organization doesn't match the logical structure of the formalization.

**Application**: Instead of trying to "work around" circular dependencies, redesign the module structure to respect the natural layering of concepts.

### Lesson 5: Document Sorries with Context

**Insight**: Sorries are acceptable in development, but must be clearly documented with:
- Why the sorry exists
- What's needed to complete it
- Where it will be completed
- Who owns it (which task/module)

**Application**: Every sorry should have a comment block explaining its purpose and completion plan.

### Lesson 6: Bridge Theorems Need Special Handling

**Insight**: Theorems that connect two layers (e.g., proof system to semantics) often create dependency challenges and deserve their own module.

**Application**: Create dedicated "bridge" or "lemma" modules for cross-layer theorems to prevent circular dependencies.

### Lesson 7: Plan Module Structure Upfront

**Insight**: Module dependencies should be planned during design, not discovered during implementation.

**Application**: Before implementing a major feature:
1. Sketch the module dependency graph
2. Identify which layer each module belongs to
3. Check for potential cycles
4. Design bridge modules if needed

---

## Conclusion

The circular dependency between Truth.lean and Soundness.lean is a **structural design issue** that cannot be resolved without architectural changes. The immediate solution (accepting the sorry with clear documentation) is pragmatic and allows forward progress.

The long-term solution involves **separating semantic theorems from metatheoretic bridge theorems**, following established patterns from Lean's mathlib and respecting the natural layering of logical concepts.

**Key Recommendations**:

1. [PASS] **Short-term**: Accept documented sorries (current approach - implemented)
2. ⏭️ **Medium-term**: Extract bridge theorems to `SoundnessLemmas.lean` or similar
3. [TARGET] **Long-term**: Split Truth.lean into pure semantics and metatheory modules
4. [CLIPBOARD] **Process**: Adopt module layering policy and dependency checking
5. [DOCS] **Culture**: Train team on recognizing and avoiding circular dependencies

**Impact**: Following these recommendations will prevent similar circular dependencies in future development and make the codebase more maintainable, understandable, and extensible.

---

## References

- Task 213 Research Report: `.opencode/specs/213_resolve_is_valid_swap_involution_blocker/reports/research-001.md`
- Task 213 Implementation Summary: `.opencode/specs/213_resolve_is_valid_swap_involution_blocker/summaries/implementation-summary-20251228.md`
- Truth.lean: `Logos/Core/Semantics/Truth.lean` (lines 1233-1256)
- Soundness.lean: `Logos/Core/Metalogic/Soundness.lean`
- Validity.lean: `Logos/Core/Semantics/Validity.lean`
- Mathlib module organization: https://leanprover-community.github.io/contribute/naming.html
- Lean module system documentation: https://lean-lang.org/lean4/doc/modules.html
