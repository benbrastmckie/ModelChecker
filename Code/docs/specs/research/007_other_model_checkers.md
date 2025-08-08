# Research 004: How Other Model Checkers Handle Iteration

[← Back to Research](README.md) | [Previous: Solver Integration →](003_solver_integration_approach.md)

## Executive Summary

This research examines how established model checkers handle the challenge of finding multiple models, particularly when semantic functions (like verify/falsify) can vary between models. The findings reveal that most model checkers avoid this problem through architectural choices rather than solving it directly.

## Model Checkers Surveyed

### 1. Alloy Analyzer

**Approach**: Static Universe, Fixed Semantics

Alloy uses a fundamentally different approach:
- **Fixed Interpretation**: Relations have fixed interpretations across all models
- **Static Signatures**: The universe of atoms is predetermined
- **No Semantic Variation**: No equivalent to varying verify/falsify functions
- **Iteration Method**: Simply adds "differ from previous" constraints

```alloy
// Alloy's approach - relations are fixed
sig State {}
sig Letter {}
pred verify[s: State, l: Letter] { 
  // This predicate has ONE interpretation across all models
}

// Finding multiple models
run {} for 3 but 2 State, 2 Letter
// Alloy automatically enumerates distinct models
```

**Key Insight**: By fixing semantic functions, Alloy sidesteps the entire problem.

### 2. NuSMV / nuXmv

**Approach**: State-Based, Temporal Logic

Model checkers for temporal logic handle iteration differently:
- **Fixed Kripke Structure**: The transition relation is fixed
- **Path Enumeration**: Find different paths, not different models
- **No Semantic Variation**: Atomic propositions have fixed valuations

```smv
MODULE main
VAR
  state : {s0, s1, s2};
  
ASSIGN
  init(state) := s0;
  next(state) := case
    state = s0 : {s1, s2};
    state = s1 : s2;
    TRUE : state;
  esac;

-- Multiple traces, but same model structure
```

**Key Insight**: Temporal model checkers iterate over executions, not model structures.

### 3. TLA+ / TLC

**Approach**: State Space Exploration

TLA+ explores states rather than models:
- **Fixed Actions**: State transitions are predetermined
- **Behavioral Properties**: Focus on sequences of states
- **No Model Variation**: One model, many behaviors

```tla
Init == x = 0
Next == x' = x + 1 \/ x' = x - 1

-- TLC explores all possible behaviors of THIS model
-- Not different models with different semantics
```

**Key Insight**: Like NuSMV, focuses on behaviors within a model, not model variation.

### 4. Isabelle/HOL

**Approach**: Proof Assistant with Model Finding

Isabelle's Nitpick tool finds countermodels:
- **Fixed Interpretation Functions**: Functions have consistent definitions
- **Type-Based Universe**: Fixed type structure
- **Enumeration Strategy**: Systematic search through interpretations

```isabelle
-- Functions have fixed definitions
definition verify :: "'state ⇒ 'letter ⇒ bool" where
  "verify s l = ..."  -- This definition doesn't change

-- Nitpick finds models by varying extensions, not definitions
nitpick [expect = genuine]
```

**Key Insight**: Separates function definitions from their extensions.

### 5. Z3 (Pure SMT)

**Approach**: Constraint-Based, No Built-in Iteration

Z3 itself doesn't have built-in model iteration:
- **Single Model**: Returns one satisfying assignment
- **User-Driven Iteration**: Users must add difference constraints
- **No Semantic Awareness**: Treats all functions uniformly

```python
# Z3's approach - user manages iteration
solver = Solver()
solver.add(constraints)

models = []
while solver.check() == sat:
    model = solver.model()
    models.append(model)
    
    # User must create difference constraint
    diff = Or([var != model[var] for var in model])
    solver.add(diff)
```

**Key Insight**: Puts iteration logic entirely on the user.

## Specialized Modal Logic Tools

### 6. LoTREC

**Approach**: Tableau-Based Reasoning

- **Fixed Semantics**: Modal operators have fixed interpretations
- **Tableau Rules**: Systematic expansion of formulas
- **Multiple Models**: Through branching in tableau

**Key Insight**: Different models arise from branching, not semantic variation.

### 7. MSPASS

**Approach**: First-Order Modal Logic

- **Skolemization**: Converts modal formulas to first-order
- **Fixed Accessibility**: Relations are fixed during solving
- **Standard Resolution**: Uses established theorem proving

**Key Insight**: Reduces modal logic to first-order, avoiding the issue.

## Common Patterns and Solutions

### Pattern 1: Fix the Semantics

Most model checkers fix interpretation functions:
- Functions have one definition throughout solving
- Models vary in structure, not semantic functions
- Avoids the self-reference problem entirely

### Pattern 2: Separate Phases

Some tools use distinct phases:
1. **Definition Phase**: Define all semantic functions
2. **Solving Phase**: Find models with those functions
3. **No Feedback**: Models don't affect function definitions

### Pattern 3: Syntactic Iteration

Many tools iterate syntactically:
- Add "differ from previous" constraints
- Don't consider semantic consistency
- Leave correctness to the user

### Pattern 4: Single Model Focus

Many tools only find one model:
- Return first satisfying assignment
- Leave iteration to external tools
- Avoid the complexity entirely

## Implications for ModelChecker

### Key Differences

ModelChecker is unusual in that:
1. **Semantic functions** (verify/falsify) are part of the model
2. **Self-reference** is possible (model determines its own semantics)
3. **Hyperintensional** features require this flexibility

### Why Others Avoid This

The research reveals why other tools avoid variable semantics:
1. **Complexity**: Self-referential constraints are hard
2. **Decidability**: May lead to undecidable problems
3. **Performance**: Iteration becomes much slower
4. **Debugging**: Hard to understand why models are invalid

### Possible Design Changes

Based on this research, ModelChecker could:

1. **Option A**: Fix verify/falsify per iteration
   - Define functions before finding each model
   - Similar to Alloy's approach
   - Loses some theoretical flexibility

2. **Option B**: Two-level semantics
   - Separate "structural" from "semantic" variation
   - Fix semantic functions, vary structure
   - Compromise between flexibility and tractability

3. **Option C**: Explicit phases
   - Phase 1: Find candidate structures
   - Phase 2: Assign consistent semantics
   - Similar to how Isabelle separates concerns

## Recommendations

### Short Term: Evaluation Override

Given that other model checkers avoid this problem entirely, the evaluation override approach seems most practical:
- Acknowledges the unique challenge
- Provides working solution
- Maintains theoretical flexibility

### Long Term: Architectural Review

Consider whether varying semantic functions during iteration is necessary:
- Document use cases requiring this feature
- Evaluate theoretical vs practical tradeoffs
- Consider fixing semantics per iteration run

### Research Direction

This is genuinely novel territory:
- Few tools handle self-referential semantic variation
- Opportunity for theoretical contribution
- May require new solving techniques

## Conclusion

The research reveals that ModelChecker faces a unique challenge not addressed by other model checkers. Most tools avoid variable semantic functions entirely, suggesting this is a genuinely hard problem. The evaluation override approach is reasonable given the lack of established solutions in the field.

---

[← Back to Research](README.md) | [Next: Summary Report →](005_summary_recommendations.md)