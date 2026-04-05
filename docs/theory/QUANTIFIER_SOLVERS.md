# Quantifier Handling in SMT Solvers

[<- Back to Theory](README.md) | [Z3 Background ->](Z3_BACKGROUND.md) | [Hyperintensional ->](HYPERINTENSIONAL.md)

This document explains how universal and existential quantifiers work internally in Z3 and CVC5 SMT solvers. It is written for readers who may not be familiar with SMT solver internals, but want to understand what happens when they write `ForAll` or `Exists` in their specifications.

## Table of Contents

1. [Introduction to SMT Quantifiers](#1-introduction-to-smt-quantifiers)
   - [What is Quantifier Instantiation](#what-is-quantifier-instantiation)
   - [Decidable vs Undecidable Fragments](#decidable-vs-undecidable-fragments)
   - [Why Quantifiers Make SMT Hard](#why-quantifiers-make-smt-hard)

2. [Z3 Quantifier Mechanisms](#2-z3-quantifier-mechanisms)
   - [Quantifier Representation](#21-quantifier-representation)
   - [E-Matching (Pattern-Based Instantiation)](#22-e-matching-pattern-based-instantiation)
   - [MBQI (Model-Based Quantifier Instantiation)](#23-mbqi-model-based-quantifier-instantiation)
   - [Decidable Fragments](#24-decidable-fragments)
   - [Z3 Configuration Options](#25-z3-configuration-options)

3. [CVC5 Quantifier Mechanisms](#3-cvc5-quantifier-mechanisms)
   - [Architecture Overview](#31-architecture-overview)
   - [CEGQI (Counterexample-Guided Instantiation)](#32-cegqi-counterexample-guided-instantiation)
   - [Enumerative Instantiation](#33-enumerative-instantiation)
   - [Finite Model Finding (FMF)](#34-finite-model-finding-fmf)
   - [SyGuS-Based Instantiation](#35-sygus-based-instantiation)
   - [CVC5 Configuration Options](#36-cvc5-configuration-options)

4. [Z3 vs CVC5 Comparison](#4-z3-vs-cvc5-comparison)
   - [Strategy Comparison Table](#41-strategy-comparison-table)
   - [When to Use Each Solver](#42-when-to-use-each-solver)
   - [Behavior on Exhaustion](#43-behavior-on-exhaustion)

5. [Practical Examples](#5-practical-examples)
   - [Basic ForAll and Exists](#51-basic-forall-and-exists)
   - [Pattern Annotations](#52-pattern-annotations)
   - [Debugging Quantifier Issues](#53-debugging-quantifier-issues)

6. [Application to ModelChecker](#6-application-to-modelchecker)
   - [Finitary vs Native Quantifiers](#61-finitary-vs-native-quantifiers)
   - [Why Finitary Works Better for Finite Domains](#62-why-finitary-works-better-for-finite-domains)

---

## 1. Introduction to SMT Quantifiers

### What is Quantifier Instantiation

An SMT solver's core job is to determine whether a set of constraints can all be satisfied simultaneously. When those constraints include quantifiers like `ForAll([x], P(x))` or `Exists([y], Q(y))`, the solver faces a fundamental challenge: how do you check a statement about "all possible values" without examining infinitely many cases?

**Quantifier instantiation** is the primary technique. Instead of checking all values, the solver strategically picks specific values (called **instantiation terms**) and adds the corresponding ground formulas as new constraints:

```
Original:  ForAll([x], f(x) >= 0)
Instantiate with x=5:  f(5) >= 0
Instantiate with x=a:  f(a) >= 0
```

The challenge is choosing which terms to instantiate. Too few, and you may miss a proof. Too many, and the solver becomes overwhelmed.

### Decidable vs Undecidable Fragments

Not all quantified formulas are equally difficult:

**Decidable fragments** are formula classes where the solver is guaranteed to terminate with a definitive answer (sat or unsat):

| Fragment | Description | Why Decidable |
|----------|-------------|---------------|
| **QBVF** | Quantifiers over bit-vectors | Finite domain (2^N elements) |
| **EPR** | Only predicates, no functions generating new terms | Finite Herbrand universe |
| **Array Property** | Restricted array index quantification | Bounded instantiation |

**Undecidable fragments** include quantifiers over unbounded integers or reals with arbitrary functions. Here the solver applies heuristics and may return "unknown" or run indefinitely.

For ModelChecker's use case (bit-vector domains), quantified formulas fall into the decidable QBVF fragment, which both Z3 and CVC5 can handle completely.

### Why Quantifiers Make SMT Hard

Consider checking `ForAll([x], x + 0 == x)` where x ranges over all integers. There are infinitely many integers, so we cannot enumerate them all. The solver must somehow prove the property holds universally without explicit enumeration.

The fundamental tension:
- **Completeness**: We want to find all relevant instantiations to prove our formula
- **Efficiency**: We want to avoid an explosion of useless instantiations that slow the solver

Different strategies balance this tension differently:
- **E-matching** (Z3, CVC5): Instantiate only when pattern terms appear in the proof context -- fast but incomplete
- **MBQI** (Z3): Construct candidate models and find counterexamples -- complete for some fragments but slower
- **CEGQI** (CVC5): Use algebraic inversion to compute exact instantiation terms -- precise but requires invertible formulas

---

## 2. Z3 Quantifier Mechanisms

### 2.1 Quantifier Representation

Z3 represents quantified formulas as AST (Abstract Syntax Tree) nodes containing:
- The quantifier kind (forall, exists, lambda)
- Bound variables with their sorts (types)
- The formula body
- Optional pattern/trigger annotations
- Optional weight hints for instantiation priority

Internally, bound variables use **de Bruijn indices** rather than names. This ensures canonical representation regardless of variable naming:

```python
import z3

x = z3.Int('x')
f = z3.Function('f', z3.IntSort(), z3.IntSort())

# Create a quantified formula
q = z3.ForAll([x], f(x) >= 0, patterns=[f(x)])

# Inspect the structure
print(q.body())          # f(Var(0)) >= 0  -- Var(0) is de Bruijn index
print(q.num_patterns())  # 1
print(q.pattern(0))      # f(Var(0))
```

The `Var(0)` in the output refers to the first (innermost) bound variable. For nested quantifiers, outer variables get higher indices.

### 2.2 E-Matching (Pattern-Based Instantiation)

**E-matching** is Z3's primary quantifier instantiation technique. The key insight:

> Only instantiate a quantifier when you see ground terms in the proof context that match its trigger pattern.

A **trigger** (or **pattern**) is an expression that governs when instantiation fires:

```python
f = z3.Function('f', z3.IntSort(), z3.IntSort())
x = z3.Int('x')

# Pattern: f(x) -- triggers when any f(t) term appears
q = z3.ForAll([x], f(x) >= 0, patterns=[f(x)])
```

When the solver encounters a ground term like `f(5)` during proof search, the pattern `f(x)` matches with `x := 5`, triggering instantiation of `f(5) >= 0`.

**The E-graph**: The "E" stands for equalities. Z3 maintains an equality graph (E-graph) tracking which terms are known equal. Pattern matching respects these equalities:

```python
# If the solver knows a == f(b), then the pattern f(x) can match 'a'
# because a is equal to f(b), so matching yields x := b
```

**Multi-patterns**: When no single expression contains all bound variables, use multiple patterns:

```python
x, y = z3.Consts('x y', A)
# Injectivity: f(x) == f(y) implies x == y
# Triggers when BOTH f(x) and f(y) terms appear
q = z3.ForAll([x, y],
    z3.Implies(f(x) == f(y), x == y),
    patterns=[z3.MultiPattern(f(x), f(y))])
```

**Pattern trade-offs**:
- Restrictive patterns = fewer instantiations = faster but may miss proofs
- Permissive patterns = more instantiations = more complete but risk matching loops

### 2.3 MBQI (Model-Based Quantifier Instantiation)

When e-matching fails to find a proof (no patterns fire), Z3 falls back to **MBQI**:

```
1. Solve the quantifier-free part; build a candidate model
2. For each ForAll([x], P(x)): evaluate P(v) for strategic values v
3. If P(v) is false in the model, add P(v) as a new constraint
4. Repeat until SAT (model satisfies all quantifiers) or UNSAT (contradiction)
```

MBQI is semantically-driven: it uses the candidate model to find exactly which instantiations would violate the quantifier. This is more thorough than e-matching but can be slower.

```python
# MBQI handles this without needing explicit patterns
x = z3.Int('x')
f = z3.Function('f', z3.IntSort(), z3.BoolSort())

s = z3.Solver()
s.add(z3.ForAll([x], z3.Not(f(x))))  # f(x) is false for all x
s.add(f(5))  # But f(5) is true -- contradiction
print(s.check())  # unsat (MBQI finds the violation at x=5)
```

### 2.4 Decidable Fragments

Z3's MBQI is a **complete decision procedure** for several formula classes:

| Fragment | Key Constraint | Example |
|----------|---------------|---------|
| **QBVF** | All vars are bit-vectors | `ForAll([bv], bv ^ bv == 0)` where bv is BitVec(8) |
| **EPR** | Only predicates, no term-generating functions | Graph reachability with predicates only |
| **Array Property** | Restricted array index quantification | `ForAll([i], Implies(0 <= i < n, a[i] >= 0))` |

For ModelChecker, **QBVF is the relevant fragment**: all quantified variables are bit-vectors with finite domains. Z3 can always decide these formulas, though it may need to explore the entire (finite) domain.

### 2.5 Z3 Configuration Options

Key options for controlling quantifier behavior:

```python
s = z3.Solver()

# Disable auto-config before setting other options
s.set('auto_config', False)

# Strategy switches
s.set('mbqi', True)       # Enable MBQI (default: True)
s.set('ematching', True)  # Enable e-matching (default: True)

# MBQI tuning
s.set('mbqi.max_iterations', 1000)  # Max MBQI refinement rounds

# Instantiation limits (safety nets)
s.set('qi.max_instances', 10000)    # Max total instantiations
```

**Common recipes**:

```python
# E-matching only (disable MBQI)
s.set('auto_config', False)
s.set('mbqi', False)

# MBQI only (disable e-matching)
s.set('auto_config', False)
s.set('ematching', False)

# Debugging: see instantiation activity
s.set('mbqi.trace', True)
s.set('qi.profile', True)
```

---

## 3. CVC5 Quantifier Mechanisms

### 3.1 Architecture Overview

CVC5 uses a modular architecture where quantifier strategies run as modules within a "theory of quantifiers":

```
┌─────────────────────────────────────────────────────────────────┐
│                    CVC5 Solving Loop                            │
│                                                                 │
│  ┌──────────────────┐      instantiations       ┌───────────┐  │
│  │  Quantifier      │ ─────────────────────────> │   SAT/    │  │
│  │  Engine          │                            │  CDCL(T)  │  │
│  │  (instantiation  │ <───────────────────────── │   Core    │  │
│  │   modules)       │   ground model / conflict  └───────────┘  │
│  └──────────────────┘                                           │
└─────────────────────────────────────────────────────────────────┘
```

The key difference from Z3: CVC5 is more conservative. When strategies exhaust without determining satisfiability, CVC5 returns `unknown` rather than potentially incorrect `unsat`.

### 3.2 CEGQI (Counterexample-Guided Instantiation)

**CEGQI** is CVC5's signature quantifier approach, especially powerful for arithmetic and bitvectors:

```
1. Find a candidate ground model M satisfying ground constraints
2. For ForAll([x], phi(x)): find a value v where M violates phi(v)
3. Use algebraic inversion to compute the instantiation term t
4. Add phi(t) as a new ground constraint
5. Repeat until SAT or UNSAT
```

The key innovation is **theory-specific invertibility**. For bitvectors, CVC5 can algebraically solve for instantiation terms:

| Expression | Invertibility Condition | Solution for x |
|------------|------------------------|----------------|
| `x + s = t` | Always (True) | `t - s` |
| `x * s = t` | `t % gcd(s, 2^n) == 0` | derived |
| `x & s = t` | `t & s == t` | `t | ~s` |

This is more directed than Z3's MBQI: instead of trying values, CEGQI computes the exact term algebraically.

```python
from cvc5.pythonic import *

x = BitVec('x', 4)
# CEGQI can directly invert this formula
formula = ForAll([x], x + ~x == BitVecVal(0xF, 4))

solver = Solver()
solver.setOption("cegqi", "true")
solver.setOption("cegqi-bv", "true")
solver.add(Not(formula))
print(solver.check())  # Tests the formula
```

### 3.3 Enumerative Instantiation

**Enumerative instantiation** is a systematic fallback that tries all ground terms in the current solver context:

```python
solver.setOption("enum-inst", "true")
```

Unlike e-matching (which requires pattern matching), enum-inst blindly enumerates the term database. It is slower but more complete when e-matching patterns do not fire.

### 3.4 Finite Model Finding (FMF)

**FMF** explicitly bounds sort cardinalities and searches for satisfying models within those bounds:

```
1. Start with cardinality k=1 for uninterpreted sorts
2. Add constraints: "this sort has exactly k elements"
3. Ground all quantifiers over the k elements
4. Check satisfiability
5. If UNSAT, increase k and repeat
```

For bitvector sorts (already finite), FMF directly enumerates the domain. The `--fmf-bound` option handles bounded quantification patterns efficiently:

```python
solver = cvc5.Solver()
solver.setOption("finite-model-find", "true")
solver.setOption("fmf-bound", "true")
```

FMF is ideal when looking for finite countermodels. It guarantees finding the smallest model if one exists.

### 3.5 SyGuS-Based Instantiation

CVC5 uniquely frames quantifier instantiation as a **synthesis problem**:

```
Given: ForAll([x], phi(x)) where phi(x) is hard to instantiate
Goal: Synthesize a term t such that phi(t) is false (counterexample witness)
```

This leverages CVC5's strength as a SyGuS solver to find complex instantiation terms that e-matching and CEGQI cannot:

```python
solver.setOption("sygus-inst", "true")
```

SyGuS-inst is powerful but slow. Use as a last resort when other strategies fail.

### 3.6 CVC5 Configuration Options

Key options for quantifier reasoning:

```python
import cvc5

solver = cvc5.Solver()
solver.setLogic("BV")

# E-Matching (default: enabled)
solver.setOption("e-matching", "true")
solver.setOption("trigger-sel", "min")  # Trigger selection heuristic

# CEGQI (default: disabled, enable for quantifier-heavy problems)
solver.setOption("cegqi", "true")
solver.setOption("cegqi-bv", "true")    # BV-specific inversion
solver.setOption("cegqi-full", "true")  # Fall back to model values

# Finite Model Finding
solver.setOption("finite-model-find", "true")
solver.setOption("fmf-bound", "true")

# Enumerative (fallback)
solver.setOption("enum-inst", "true")

# SyGuS-based (powerful but slow)
solver.setOption("sygus-inst", "true")
```

**Recommended for bitvector quantifiers (ModelChecker's domain)**:

```python
solver.setOption("cegqi", "true")
solver.setOption("cegqi-bv", "true")
solver.setOption("cegqi-full", "true")
```

---

## 4. Z3 vs CVC5 Comparison

### 4.1 Strategy Comparison Table

| Feature | Z3 | CVC5 |
|---------|-----|------|
| **Primary Strategies** | E-matching + MBQI | E-matching + CBQI |
| **Bitvector Handling** | MBQI over QBVF | CEGQI-BV with invertibility |
| **Finite Model Finding** | Via MBQI | Dedicated FMF module |
| **When Exhausted** | Returns UNSAT (risky) | Returns `unknown` (safe) |
| **Pattern Support** | Full (multi-pattern, no-pattern) | Full |
| **Synthesis-Based** | No | Yes (sygus-inst) |
| **Default Completeness** | Semi-complete | Conservative |

### 4.2 When to Use Each Solver

**Choose Z3 when**:
- E-matching patterns are well-designed and fire reliably
- Working within decidable fragments (QBVF, EPR)
- Need aggressive model search (may return UNSAT on hard problems)

**Choose CVC5 when**:
- Problems have complex algebraic structure (CEGQI excels)
- Need conservative correctness (`unknown` rather than wrong UNSAT)
- Looking for finite countermodels (FMF)

**For ModelChecker**: Both solvers work on the QBVF fragment, but their failure modes differ. Z3's aggressive MBQI may return incorrect UNSAT; CVC5's conservatism returns `unknown`. In practice, the finitary approach (explicit enumeration) outperforms both native solver strategies for ModelChecker's finite domains.

### 4.3 Behavior on Exhaustion

This is the critical behavioral difference:

**Z3**: When MBQI exhausts its iteration limit without determining satisfiability, it may return `unsat` even for satisfiable formulas. This is an incompleteness that looks like a valid answer but is actually incorrect.

**CVC5**: When strategies exhaust without a definitive answer, CVC5 returns `unknown`. This is correctly conservative -- no answer rather than a wrong one.

For countermodel search (the ModelChecker use case):
- Z3's false `unsat` means "no countermodel found" when one actually exists
- CVC5's `unknown` also means "no countermodel found" but acknowledges uncertainty

Both failures look similar to the user (no model returned), but CVC5's response is more honest about what happened.

---

## 5. Practical Examples

### 5.1 Basic ForAll and Exists

**Z3**:

```python
import z3

# Universal quantifier: verify x * 0 == 0 for all integers
x = z3.Int('x')
s = z3.Solver()
s.add(z3.Not(z3.ForAll([x], x * 0 == 0)))  # Negate to check validity
print(s.check())  # unsat -- the property holds universally

# Existential quantifier: find x such that x * x == 16
s2 = z3.Solver()
s2.add(z3.Exists([x], x * x == 16))
print(s2.check())  # sat
```

**CVC5** (pythonic API):

```python
from cvc5.pythonic import *

# Universal quantifier
x = Int('x')
solver = Solver()
solver.add(Not(ForAll([x], x * 0 == 0)))
print(solver.check())  # unsat

# Existential quantifier
y = Int('y')
solver2 = Solver()
solver2.add(Exists([y], y * y == 16))
print(solver2.check())  # sat
```

### 5.2 Pattern Annotations

Patterns guide e-matching. Restrictive patterns prevent unnecessary instantiations:

```python
import z3

f = z3.Function('f', z3.IntSort(), z3.IntSort())
g = z3.Function('g', z3.IntSort(), z3.IntSort())
x = z3.Int('x')
a, b = z3.Ints('a b')

s = z3.Solver()
s.set('auto_config', False)
s.set('mbqi', False)  # E-matching only

# Restrictive pattern: only fires when f(g(...)) appears
s.add(z3.ForAll([x], f(g(x)) == x, patterns=[f(g(x))]))
s.add(g(a) == b)
s.add(a != b)
# Pattern f(g(x)) does not fire -- no f(g(t)) term exists
print(s.check())  # unknown

# Try again with permissive pattern
s2 = z3.Solver()
s2.set('auto_config', False)
s2.set('mbqi', False)
s2.add(z3.ForAll([x], f(g(x)) == x, patterns=[g(x)]))  # Fires on g(a)
s2.add(g(a) == b)
s2.add(a != b)
print(s2.check())  # Can now reason about the formula
```

### 5.3 Debugging Quantifier Issues

When quantifier reasoning fails or is slow, use tracing options:

**Z3**:

```python
s = z3.Solver()
s.set('mbqi.trace', True)    # Print MBQI activity
s.set('qi.profile', True)     # Profile instantiation patterns
# ... add formulas and check ...
```

**CVC5**:

```bash
# Run CVC5 with verbose quantifier output
cvc5 --inst-debug-max=10000 input.smt2
```

Common issues:
- **Matching loops**: Instantiation produces new terms that trigger the same pattern infinitely. Fix by using more restrictive patterns or increasing the weight annotation.
- **No patterns fire**: E-matching never triggers. Enable MBQI (Z3) or CEGQI (CVC5).
- **Timeout**: Too many instantiations. Limit with `qi.max_instances` (Z3) or `--inst-max-rounds` (CVC5).

---

## 6. Application to ModelChecker

### 6.1 Finitary vs Native Quantifiers

ModelChecker offers two implementations for quantifiers:

**Finitary** (`\forall`, `\exists`): Expands quantifiers into explicit conjunctions/disjunctions over the finite domain:

```
ForAll([x], P(x)) where x is BitVec(N)
  becomes: P(0) AND P(1) AND ... AND P(2^N - 1)

Exists([x], Q(x)) where x is BitVec(N)
  becomes: Q(0) OR Q(1) OR ... OR Q(2^N - 1)
```

The solver sees only ground propositional constraints -- no quantifiers at all.

**Native** (`\all`, `\some`): Passes the quantified formula directly to the solver:

```python
z3.ForAll([x], P(x))  # Let the solver handle instantiation
```

The solver uses its internal strategies (e-matching, MBQI, CEGQI) to reason about the quantifier.

### 6.2 Why Finitary Works Better for Finite Domains

For ModelChecker's small bit-vector domains (typically N=2 to N=6), finitary quantifiers consistently outperform native:

| Aspect | Finitary | Native |
|--------|----------|--------|
| **Correctness** | Always correct (explicit enumeration) | Risk of incomplete instantiation |
| **Predictability** | Deterministic expansion | Heuristic-dependent |
| **Overhead** | 2^N ground constraints | Quantifier reasoning overhead |
| **Sweet spot** | N <= 6 (64 values) | Large/infinite domains |

**Why native struggles on small domains**:

1. **Instantiation overhead**: The solver's quantifier machinery (pattern matching, model construction) has non-trivial cost that exceeds explicit enumeration for small domains.

2. **Incompleteness risk**: Native solvers may return `unknown` (CVC5) or incorrect `unsat` (Z3 in edge cases) when their heuristics fail to find relevant instantiations.

3. **No structural advantage**: Native quantifiers excel when the solver can reason algebraically without explicit enumeration. For finite domains, explicit enumeration is already tractable.

**Benchmark results** (from `first_order_benchmark.py`):

- Finitary-Z3 and finitary-CVC5: 100% correctness across all test cases
- Native-Z3: Generally correct but slower than finitary for small N
- Native-CVC5: Has known correctness issues on countermodel queries

**Recommendation**: Use finitary quantifiers for ModelChecker's finite state spaces. Reserve native quantifiers for exploring how solver-level reasoning handles quantified properties, or for domains too large to enumerate.

For more details on the benchmark methodology and results, see the [first_order_benchmark.py documentation](../../code/scripts/README.md).

---

## References

**Z3 Documentation**:
- [Online Z3 Guide: Quantifiers](https://microsoft.github.io/z3guide/docs/logic/Quantifiers/)
- [Programming Z3 Tutorial](https://theory.stanford.edu/~nikolaj/programmingz3.html)
- [Efficient E-Matching for SMT Solvers](https://leodemoura.github.io/files/ematching.pdf)
- [Complete Instantiation for Quantified Formulas in SMT (MBQI)](https://leodemoura.github.io/files/ci.pdf)

**CVC5 Documentation**:
- [CVC5 Options Documentation](https://cvc5.github.io/docs/cvc5-1.1.2/options.html)
- [CVC5 Pythonic API: Quantifiers](https://cvc5.github.io/docs/cvc5-1.0.2/api/python/pythonic/quant.html)
- [Solving Quantified Bit-Vectors using Invertibility Conditions](https://link.springer.com/chapter/10.1007/978-3-319-96142-2_16)
- [Finite Model Finding in SMT](https://cvc4.cs.stanford.edu/papers/CAV-2013/fmf_smt_reynolds_cav2013.pdf)

**Academic Papers**:
- Niemetz et al., "Solving Quantified Bit-Vectors using Invertibility Conditions", CAV 2018
- Barbosa et al., "CVC5: A Versatile and Industrial-Strength SMT Solver", TACAS 2022
- de Moura & Bjorner, "Complete Instantiation for Quantified Formulas in SMT", CAV 2009
