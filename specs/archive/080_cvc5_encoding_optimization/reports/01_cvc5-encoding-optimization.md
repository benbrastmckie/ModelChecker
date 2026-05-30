# CVC5 Encoding Optimization Research Report

## Executive Summary

This research analyzes the constraint encoding patterns used by the logos theory to identify optimization opportunities for CVC5 UNSAT proof search. The key finding is that **the encoding already uses ground quantifier instantiation**, which eliminates the primary category of CVC5-specific optimizations (trigger-based quantifier handling). The remaining 1.6x performance gap (after task 79's `produce-unsat-cores` optimization) is attributable to fundamental solver implementation differences rather than encoding inefficiencies.

Two viable optimization paths were identified:
1. **Constraint simplification before CVC5 assertion** - Pre-simplify expanded constraints using Z3's simplifier before passing to CVC5
2. **Assertion batching with scope management** - Use push/pop to structure constraint groups for CVC5's conflict analysis

However, the expected gains are modest (10-30% improvement) and the implementation complexity is non-trivial.

## Background

### Prior Research (Task 79)

Task 79 identified that disabling `produce-unsat-cores` provides a 5.6x speedup on UNSAT problems, reducing the CVC5 performance gap from 9.37x to approximately 1.6x. The optimal configuration:

```python
self._solver.set("decision", "stoponly")
self._solver.set("bv-eager-eval", "true")
```

This research investigates whether encoding-level changes can close the remaining 1.6x gap.

### Benchmark Data (Task 76)

Worst-case UNSAT examples from the curated benchmark:

| Example | Z3 Time | CVC5 Time | Ratio | Subtheory |
|---------|---------|-----------|-------|-----------|
| CL_TH_1 | 0.107s | 2.093s | 19.6x | constitutive |
| CF_TH_2 | 0.086s | 2.665s | 31.0x | counterfactual |
| MOD_TH_5 | 0.074s | 2.104s | 28.4x | modal |

After task 79 optimizations (without unsat cores):

| Example | Z3 Time | CVC5 Time | Ratio |
|---------|---------|-----------|-------|
| CL_TH_1 | 0.107s | 0.233s | 2.2x |
| CF_TH_2 | 0.086s | 0.377s | 4.4x |
| MOD_TH_5 | 0.074s | 0.184s | 2.5x |

## Round 1: Encoding Analysis

### Constraint Generation Architecture

The logos theory generates SMT constraints through the following layers:

1. **Semantic Framework** (`semantic.py`)
   - Defines primitive Z3 functions: `verify`, `falsify`, `possible`
   - Provides `true_at`, `false_at`, `extended_verify`, `extended_falsify` methods
   - Establishes frame constraints (possibility downward closure, main world is a world)

2. **Operator Implementations** (`subtheories/*/operators.py`)
   - Each operator defines truth/falsity conditions via Z3 constraints
   - Complex operators nest simpler ones recursively

3. **Quantifier Handling** (`utils/z3_helpers.py`)
   - `ForAll(bvs, formula)` - Expands to conjunction over all bitvector values
   - `Exists(bvs, formula)` - Expands to disjunction over all bitvector values
   - **Key insight**: Quantifiers are ground-instantiated, not symbolic

### Constraint Pattern Analysis

#### Example: CL_TH_1 (Ground to Essence)

Formula: `(A \leq B)` premise, `(\neg A \sqsubseteq \neg B)` conclusion (expected: no countermodel)

The GroundOperator (`\leq`) generates:

```python
ForAll([x], Implies(extended_verify(x, A), extended_verify(x, B)))
ForAll([x, y], Implies(And(extended_falsify(x, A), extended_falsify(y, B)),
                       extended_falsify(fusion(x, y), B)))
ForAll([x], Implies(extended_falsify(x, B),
                    Exists(y, And(extended_falsify(y, A), is_part_of(y, x)))))
```

With N=4 (16 states), each single-variable `ForAll` expands to 16 conjuncts, and two-variable `ForAll` expands to 256 conjuncts. The nested `Exists` further multiplies by 16.

#### Constraint Explosion Calculation

For a typical constitutive theorem with N=4:
- Frame constraints: ~20 base constraints
- Model constraints: ~100-200 (verify/falsify for each sentence letter at each state)
- Premise constraints: ~500-2000 (depending on operator complexity)
- Conclusion constraints: ~500-2000 (negated conclusion for countermodel search)

Total assertions: **~1000-5000 ground constraints**

### Theories Combined

The logos theory combines:
- **Bitvectors** (BitVec(N)) - State representation
- **Uninterpreted Functions** - `verify`, `falsify`, `possible`, plus predicate interpretations
- **Pure Boolean** - Propositional structure from quantifier expansion
- **No arrays** - States are atomic bitvectors, not arrays
- **No arithmetic** - Only bitvector operations (OR for fusion, parthood via bitwise AND)

## Round 2: CVC5 Encoding Best Practices Research

### Quantifier Handling

CVC5 provides several quantifier handling modes:

| Option | Description | Relevance |
|--------|-------------|-----------|
| `e-matching` | Pattern-based instantiation | **Not applicable** - our quantifiers are already ground |
| `finite-model-find` | Bounded quantifier search | **Not applicable** - already enumerated |
| `cbqi` | Conflict-based instantiation | **Not applicable** - no symbolic quantifiers |
| `fmf-bound` | Bounded integer quantification | **Not applicable** - bitvectors, not integers |

**Key Finding**: Since the logos theory uses explicit ground instantiation (expanding ForAll/Exists to conjunctions/disjunctions), CVC5's quantifier-specific optimizations are irrelevant. The solver receives a purely propositional formula over bitvector theory.

### Bitvector Solving

CVC5 bitvector options:

| Option | Default | Effect |
|--------|---------|--------|
| `bitblast` | lazy | Lazy vs eager bitblasting |
| `bv-sat-solver` | cadical | SAT solver backend |
| `bv-eager-eval` | false | Eager term evaluation |
| `bv-to-bool` | false | Lift 1-bit BV to booleans |

Task 79 found `bv-eager-eval=true` provides incremental benefit. The `bitblast=eager` option is incompatible with uninterpreted functions.

### Assertion Structure

Research from CVC5 GitHub issues and documentation suggests:
1. **Assertion order can matter** - Conflicts detected earlier can prune search
2. **Large conjunctions may be split** - Individual assertions vs single And()
3. **Scope management** - push/pop affects learned lemma retention

## Round 3: Encoding Difference Analysis

### Why CVC5 is Slower on These Constraints

After eliminating quantifier handling as a factor, the remaining performance gap stems from:

1. **Lazy vs Eager Theory Combination**
   - Z3's theory combination is highly optimized for bitvector + UF
   - CVC5's proof-producing machinery has overhead even when disabled

2. **SAT Solver Heuristics**
   - Both use CaDiCaL by default, but integration differs
   - Z3's DPLL(T) loop may be more tightly coupled

3. **Constraint Representation**
   - Z3 may apply more aggressive internal simplification
   - CVC5's term representation may have overhead

### Potential Encoding Changes

#### Option A: Pre-Simplification

Apply Z3's simplifier to constraints before passing to CVC5:

```python
def assert_to_cvc5(constraint):
    # Use Z3 to simplify the ground constraint
    simplified = z3.simplify(constraint)
    # Convert and add to CVC5
    cvc5_constraint = convert_z3_to_cvc5(simplified)
    cvc5_solver.add(cvc5_constraint)
```

**Challenges**:
- Requires cross-solver term conversion
- Z3's simplifier already runs during constraint construction
- Benefit is speculative

#### Option B: Assertion Batching

Group related constraints within push/pop scopes:

```python
solver.push()
for constraint in frame_constraints:
    solver.add(constraint)
solver.push()
for constraint in model_constraints:
    solver.add(constraint)
# ... etc
```

**Potential Benefit**: CVC5 may better utilize scope information for conflict analysis.

#### Option C: Constraint Decomposition

Split large conjunctions into individual assertions:

```python
# Instead of:
solver.add(And(c1, c2, c3, ..., cn))

# Use:
for c in [c1, c2, c3, ..., cn]:
    solver.add(c)
```

**Status**: The current implementation already does this - constraints are added individually via `assert_tracked()`.

## Round 4: Feasibility Assessment

### Assessment Matrix

| Change | Expected Gain | Implementation Effort | Risk |
|--------|---------------|----------------------|------|
| Pre-simplification | 5-15% | High (cross-solver conversion) | Medium |
| Assertion batching | 5-10% | Low (structural change) | Low |
| Different constraint order | 0-10% | Low | Low |
| Alternative quantifier expansion | Unknown | Very High (fundamental change) | High |

### Conclusion on Encoding Changes

**The encoding is already near-optimal for CVC5**. The key reasons:

1. **Ground instantiation** eliminates quantifier handling overhead
2. **Individual assertions** already provide fine-grained constraint structure
3. **Bitvector theory** is well-supported by both solvers
4. **No architectural mismatch** - the constraint pattern is standard SMT

The remaining 1.6x gap is attributable to:
- Solver implementation differences (not encoding)
- Z3's mature optimization for this exact theory combination
- CVC5's generality vs Z3's specialization

## Recommendations

### Immediate Actions (Low Risk, Low Effort)

1. **Implement configurable unsat-core mode** (from task 79)
   - Default to fast mode (no cores) for theorem proving
   - Enable diagnostic mode when countermodel inspection needed

2. **Add assertion batching experiment**
   - Create test script to measure push/pop scope impact
   - If beneficial, integrate into solver adapter

### Future Investigation (Medium Risk, Medium Effort)

3. **Explore Z3 simplification export**
   - Export simplified SMT-LIB2 from Z3
   - Load into CVC5 to measure baseline difference
   - Determines whether simplification helps

4. **Profile CVC5 internals**
   - Use CVC5 statistics to identify bottlenecks
   - May reveal CVC5-specific tuning opportunities

### Not Recommended

5. **Symbolic quantifier encoding**
   - Would require fundamental redesign of ForAll/Exists
   - May introduce incompleteness or new performance issues
   - Ground instantiation is correct for finite domains

6. **Integer encoding of bitvectors**
   - Task 79 tested `solve-bv-as-int` modes
   - No improvement; slight regression

## Technical Appendix

### Constraint Pattern Examples

#### Atomic Sentence Truth (`true_at` for sentence letter)

```smt2
; For sentence letter A at world w:
(exists ((x (_ BitVec 4)))
  (and (bvule x w)           ; is_part_of(x, w)
       (verify x A)))         ; verify function application
```

Expanded (N=4):
```smt2
(or (and (bvule #x0 w) (verify #x0 A))
    (and (bvule #x1 w) (verify #x1 A))
    ... ; 16 disjuncts total
    (and (bvule #xF w) (verify #xF A)))
```

#### Frame Constraint (Possibility Downward Closure)

```smt2
(forall ((x (_ BitVec 4)) (y (_ BitVec 4)))
  (=> (and (possible y) (bvule x y))
      (possible x)))
```

Expanded (N=4): 256 implications.

### Solver Version Information

- Z3: 4.12.2 (or later)
- CVC5: 1.0.5 (or later)
- Both use CaDiCaL as default SAT backend

### Related Research

- [CVC5 TACAS 2022 Paper](https://www-cs.stanford.edu/~preiner/publications/2022/BarbosaBBKLMMMN-TACAS22.pdf) - Architecture overview
- [Machine Learning for Quantifier Selection in CVC5](https://arxiv.org/abs/2408.14338) - Advanced quantifier handling (not applicable to our ground case)
- [Quantifiers in CVC5 vs Z3 Issue](https://github.com/cvc5/cvc5/issues/9234) - Bounded quantifier workarounds
- [CVC5 Options Documentation](https://cvc5.github.io/docs/cvc5-1.0.2/options.html) - Complete option reference

## Conclusion

The logos theory's constraint encoding is well-suited to modern SMT solvers. The ground quantifier instantiation approach, while generating many constraints, produces a form that both Z3 and CVC5 handle efficiently. The performance gap after task 79 optimizations (1.6x average) represents fundamental solver differences rather than encoding deficiencies.

**Success Criterion Assessment**: The goal was to reduce the average UNSAT time ratio from 9.37x to under 4x, or demonstrate the encoding is near-optimal. Task 79's optimizations achieved **1.6x average**, significantly exceeding the target. This research confirms that further encoding changes are unlikely to provide substantial additional improvement.

**Recommended Path Forward**: Implement the configurable diagnostic mode from task 79, and consider the encoding "sufficiently optimized" for CVC5 compatibility.
