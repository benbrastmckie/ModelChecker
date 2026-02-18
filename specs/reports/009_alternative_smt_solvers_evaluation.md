# Alternative SMT Solvers Evaluation for ModelChecker

## Metadata
- **Date**: 2025-10-02
- **Scope**: Evaluation of CVC5, Yices, and other SMT solvers as alternatives to Z3
- **Primary Directory**: ModelChecker framework (all theories)
- **Context**: Witness predicate non-determinism issues with Z3 (Reports 007, 008)
- **Files Analyzed**: 109 files with Z3 dependencies across codebase
- **Focus**: Quantifier handling, determinism, Python API support, migration feasibility

## Executive Summary

This report evaluates whether alternative SMT solvers (CVC5, Yices, veriT, or portfolio approaches) could provide better solutions to the quantifier instantiation non-determinism issues encountered with Z3 in the witness predicate implementation.

### Key Findings

1. **CVC5**: Most promising Z3 alternative with similar capabilities but mixed quantifier performance
2. **Yices**: Strong for specific theories, lacks some advanced features needed by ModelChecker
3. **pySMT**: Unified Python API enabling portfolio solving across multiple solvers
4. **Quantifier-free approach**: Still recommended regardless of solver choice (Plan 103)

### Bottom Line

While alternative solvers show promise, **switching solvers is a high-risk, high-effort endeavor** with **uncertain benefits**. The quantifier-free witness encoding (Option D, Plan 103) eliminates the core quantifier instantiation issue that motivated this investigation, making it the **pragmatic first choice**. Solver diversification should be considered as a **future optimization** after quantifier-free implementation proves successful.

## Background

### Problem Context

**Current Issue** (Reports 007, 008):
- Z3's ForAll quantifier instantiation exhibits non-deterministic behavior
- Witness predicate falsity constraint works once, then fails on subsequent runs
- BM_CM_1 example times out without finding countermodel

**Proposed Solution** (Plan 103):
- Option D: Quantifier-free witness encoding
- Eliminates ForAll quantifiers by enumerating (world, time) pairs
- Generates propositional constraints instead of quantified formulas

**This Investigation**:
- Could a different SMT solver handle quantifiers more deterministically?
- Would switching solvers provide better performance or reliability?
- What are the costs and benefits of solver migration?

### ModelChecker's Z3 Usage

**Scope**: 109 files import Z3 across:
- Theory implementations (bimodal, exclusion, imposition, logos)
- Core model infrastructure (constraints, structure, semantics)
- Iterator system for model enumeration
- Builder and utility modules

**Z3 Features Used**:
- `z3.Solver()` - Core constraint solving
- `z3.Function()` - Uninterpreted functions (witness predicates)
- `z3.ForAll()`, `z3.Exists()` - Quantifiers
- `z3.And()`, `z3.Or()`, `z3.Implies()` - Boolean logic
- `z3.Int()`, `z3.IntSort()` - Integer arithmetic
- `z3.Bool()` - Boolean variables
- `z3.check()`, `z3.model()` - Solving and model extraction
- `solver.set()` - Configuration options
- Context isolation for multiple examples

**Critical Dependencies**:
- Witness predicates use `z3.Function()` for Skolemization
- Quantifiers in modal operators (Box, Diamond, Future, Past)
- Model iteration requires constraint manipulation and solving
- Framework assumes Z3 API conventions throughout

## Alternative SMT Solvers Analysis

### 1. CVC5 (Cooperating Validity Checker 5)

**Overview**:
- Successor to CVC4, actively developed (2022-present)
- Comprehensive theory support comparable to Z3
- Focus on industrial-strength verification

#### Capabilities

**Theories Supported**:
- ✅ All standard SMT-LIB theories
- ✅ Uninterpreted functions (needed for witness predicates)
- ✅ Integer arithmetic (used in bimodal world/time)
- ✅ Boolean logic (core to all theories)
- ✅ Quantifiers (ForAll, Exists)

**Advanced Features**:
- ✅ Higher-order reasoning
- ✅ Syntax-guided synthesis (SyGuS)
- ✅ Machine learning-guided instantiation (2024-2025 research)
- ✅ Theory-agnostic enumerative quantifier instantiation

**Python API**:
- ✅ Native Python bindings
- ✅ Compatible with pySMT for unified interface
- ✅ Similar API structure to Z3

#### Quantifier Handling

**Instantiation Techniques**:
1. **E-matching**: Like Z3, uses pattern-based instantiation
2. **Conflict-based instantiation (cbqi)**: Similar to Z3's approach
3. **Enumerative instantiation**: Unique to CVC5, syntax-guided term generation
4. **Neural-guided**: Recent research (2025) using GNNs for term selection

**Performance Characteristics**:
- ✅ Comparable to Z3 on most benchmarks
- ⚠️ Some cases where CVC5 returns "unknown" while Z3 finds sat/unsat
- ⚠️ Some cases where Z3 returns "unknown" while CVC5 succeeds
- ✅ Active development with SMT-COMP 2024 participation

#### Pros for ModelChecker

1. **Similar feature set**: Minimal API changes needed
2. **Active development**: Regular updates and improvements
3. **Quantifier innovations**: New techniques beyond Z3's E-matching
4. **Neural guidance**: Could improve quantifier instantiation (though adds complexity)
5. **Portfolio potential**: Run CVC5 and Z3 in parallel via pySMT

#### Cons for ModelChecker

1. **No guaranteed determinism**: CVC5 also uses heuristic quantifier instantiation
2. **Different failure modes**: May fail on formulas Z3 handles, vice versa
3. **API differences**: Some Z3 idioms may not translate directly
4. **Unknown performance**: Need empirical testing on ModelChecker workloads
5. **Migration effort**: High (~2-4 weeks for full testing)

### 2. Yices2

**Overview**:
- Developed by SRI International
- Strong performance on specific theories
- Emphasis on efficiency and scalability

#### Capabilities

**Theories Supported**:
- ✅ Uninterpreted functions with equality
- ✅ Integer and real arithmetic (linear and nonlinear)
- ✅ Bitvectors
- ✅ Scalar types and tuples
- ⚠️ Limited quantifier support

**Quantifier Support**:
- ⚠️ **Bounded integer quantification** (special case)
- ⚠️ Less mature than Z3/CVC5 for general quantifiers
- ✅ Efficient for quantifier-free fragments

**Python API**:
- ✅ Python bindings available
- ✅ pySMT support
- ⚠️ API less similar to Z3 than CVC5

#### Performance Characteristics

**Strengths**:
- ✅ Very fast on linear arithmetic
- ✅ Portfolio mode (parallel solver instances)
- ✅ Efficient for quantifier-free problems

**Weaknesses**:
- ❌ Weaker quantifier handling than Z3/CVC5
- ❌ Some formulas with quantifiers may return "unknown"
- ❌ Less comprehensive theory support

#### Assessment for ModelChecker

**Verdict**: ❌ **Not Recommended**

**Reasons**:
1. Quantifier support insufficient for modal operators (Box, Diamond)
2. Witness predicates + quantifiers are core to ModelChecker
3. Would require significant architectural changes to work around limitations
4. Gains (performance on arithmetic) don't offset losses (quantifier capability)

**Potential Use Case**:
- Could be part of portfolio for quantifier-free examples
- Might excel at logos theory (truthmaker semantics, less quantification)

### 3. veriT

**Overview**:
- Developed in Nancy, France
- Proof-producing SMT solver
- Focus on verification and proof checking

#### Capabilities

**Theories Supported**:
- ✅ Uninterpreted functions
- ✅ Linear arithmetic (real and integer)
- ✅ Good quantifier support (explicitly mentioned)
- ✅ Proof production (unique feature)

**Python API**:
- ⚠️ Less mature Python bindings than Z3/CVC5
- ✅ Available through pySMT
- ⚠️ API documentation less comprehensive

#### Quantifier Handling

- ✅ Explicitly noted as having "good support for quantifiers"
- ⚠️ Less research and benchmarking than Z3/CVC5
- ⚠️ Performance characteristics not well-documented

#### Assessment for ModelChecker

**Verdict**: ⚠️ **Low Priority**

**Reasons**:
1. Less mature tooling and documentation
2. Proof production is interesting but not needed for ModelChecker
3. Quantifier performance unknown compared to Z3/CVC5
4. API integration would require more effort

**Potential Use Case**:
- If proof traces become valuable for debugging
- As portfolio member for diversity

### 4. Portfolio Solving (pySMT)

**Overview**:
- Run multiple solvers in parallel on same problem
- Return result as soon as any solver succeeds
- Unified Python API across solvers

#### pySMT Library

**Features**:
- ✅ Unified interface for Z3, CVC5, Yices, veriT, MathSAT
- ✅ Automatic formula translation between solver APIs
- ✅ Portfolio solving with parallel execution
- ✅ Solver-agnostic formula construction

**Architecture**:
```python
from pysmt.shortcuts import Solver, get_model

# Unified API
with Solver(name="z3") as s:
    s.add_assertion(formula)
    if s.solve():
        model = s.get_model()

# Or portfolio
with Solver(name="portfolio", portfolio=["z3", "cvc5", "yices"]) as s:
    s.add_assertion(formula)
    # Whichever solves first wins
```

#### Pros for ModelChecker

1. **Solver diversity**: Best-of-breed for different problem types
2. **Risk mitigation**: If one solver fails/times out, others may succeed
3. **Empirical optimization**: Benchmark to find best solver per theory
4. **Future-proof**: Easy to add new solvers as they emerge
5. **Unified codebase**: One API for all solvers

#### Cons for ModelChecker

1. **Migration effort**: Convert all Z3 code to pySMT abstractions
2. **Performance overhead**: Translation layer adds latency
3. **Feature limitations**: pySMT lowest-common-denominator of supported solvers
4. **Advanced features**: Z3-specific optimizations may not translate
5. **Debugging complexity**: Harder to debug when abstraction leaks
6. **Determinism**: Portfolio introduces inherent non-determinism (race)

#### Assessment for ModelChecker

**Verdict**: ⚠️ **Interesting for Future, Not Immediate**

**Reasons**:
1. High migration effort (weeks to months)
2. Benefits uncertain without quantifiers (if Plan 103 succeeds)
3. Portfolio non-determinism may be worse than Z3 non-determinism
4. Better as optimization after core issues resolved

**Potential Use Case**:
- Long-term architecture for theory diversity
- Experimentation framework for solver comparison
- Production fallback for robustness

## Migration Feasibility Analysis

### Effort Estimation

#### Minimal Migration (Single Solver Swap)

**Scope**: Replace Z3 with CVC5 throughout codebase

**Tasks**:
1. API translation (~1-2 weeks)
   - Convert Z3 imports to CVC5 imports
   - Map Z3 API calls to CVC5 equivalents
   - Handle API differences (configuration, context, etc.)
2. Test suite updates (~1 week)
   - Re-run all tests
   - Fix broken tests due to API differences
   - Verify results match expected behavior
3. Performance benchmarking (~1 week)
   - Time all examples with both solvers
   - Compare constraint solving times
   - Identify regressions
4. Bug fixes (~1-2 weeks contingency)
   - Address solver-specific failures
   - Handle edge cases differently
   - Tuning solver settings

**Total Estimate**: 4-6 weeks full-time effort

**Risk**: Medium-High
- Unknown API compatibility issues
- Potential performance regressions
- May not solve non-determinism

#### Comprehensive Migration (pySMT Portfolio)

**Scope**: Abstract solver layer, support multiple solvers

**Tasks**:
1. Architecture design (~1 week)
   - Design solver abstraction layer
   - Plan gradual migration strategy
   - Define testing approach
2. pySMT integration (~2-3 weeks)
   - Convert formula construction to pySMT API
   - Abstract solver instantiation
   - Handle theory-specific code
3. Solver-specific testing (~2 weeks)
   - Test with Z3, CVC5, Yices
   - Identify solver-specific issues
   - Document solver capabilities per theory
4. Portfolio implementation (~1 week)
   - Parallel solver execution
   - Result collection and merging
   - Timeout and error handling
5. Optimization and tuning (~2 weeks)
   - Benchmark portfolio configurations
   - Optimize solver selection per theory
   - Performance profiling
6. Bug fixes and edge cases (~2-3 weeks contingency)

**Total Estimate**: 10-13 weeks full-time effort

**Risk**: High
- Major architectural change
- Complex debugging scenarios
- May introduce new failure modes

### API Compatibility Analysis

#### Z3 → CVC5 Translation

**Close Matches** (Easy):
```python
# Z3                          # CVC5
import z3                     import cvc5
s = z3.Solver()               s = cvc5.Solver()
s.add(constraint)             s.assertFormula(constraint)
result = s.check()            result = s.checkSat()
m = s.model()                 m = s.getValue(var)  # Different approach
```

**API Differences** (Medium):
- Configuration: `solver.set(key, val)` vs `solver.setOption(key, val)`
- Context: Z3 uses contexts, CVC5 uses `Solver` as context
- Model extraction: Different model querying APIs
- Type creation: `z3.IntSort()` vs `cvc5.IntSort()`

**Complex Differences** (Hard):
- Quantifier patterns: Syntax differs
- Configuration options: Different names and values
- Error handling: Different exception types
- Advanced features: Tactics, optimization not in CVC5

#### Z3 → pySMT Translation

**Good Abstractions** (Easy):
- Boolean logic: And, Or, Not, Implies, Iff
- Arithmetic: Plus, Minus, Times, LE, LT, etc.
- Quantifiers: ForAll, Exists
- Basic types: Int, Real, Bool

**Missing Abstractions** (Hard):
- Configuration options: Solver-specific
- Advanced Z3 features: Tactics, optimization, fixedpoint
- Context isolation: Framework-level concept
- Model iteration: Custom logic per solver

### Risk Assessment

#### Risk 1: No Determinism Improvement

**Likelihood**: Medium-High
**Impact**: Critical

**Analysis**: CVC5 also uses heuristic quantifier instantiation (E-matching, cbqi). Non-determinism may persist.

**Mitigation**:
- Test CVC5 on BM_CM_1 before full migration
- If non-determinism persists, quantifier-free approach still needed
- Portfolio doesn't help determinism (adds race conditions)

#### Risk 2: Performance Regression

**Likelihood**: Medium
**Impact**: High

**Analysis**: CVC5 and Z3 have different strengths. Some examples may be faster, others slower.

**Mitigation**:
- Comprehensive benchmarking before migration
- Keep Z3 as fallback option
- Portfolio approach if performance varies by example

#### Risk 3: Subtle Correctness Issues

**Likelihood**: Low-Medium
**Impact**: Critical

**Analysis**: Different solvers may interpret formulas differently, leading to incorrect results.

**Mitigation**:
- Extensive testing on all examples
- Cross-validate results between solvers
- Use pySMT for consistent formula semantics

#### Risk 4: Loss of Advanced Features

**Likelihood**: Low
**Impact**: Medium

**Analysis**: Z3-specific features (tactics, optimization) may not have CVC5 equivalents.

**Mitigation**:
- Audit usage of Z3-specific features
- Find CVC5 equivalents or workarounds
- Document feature gaps

#### Risk 5: Maintenance Burden

**Likelihood**: High
**Impact**: Medium

**Analysis**: Supporting multiple solvers increases maintenance complexity.

**Mitigation**:
- Abstract solver dependencies where possible
- Comprehensive test coverage
- Document solver-specific workarounds

## Empirical Evaluation (Recommended)

Before committing to migration, run empirical tests:

### Phase 1: Feasibility Test (1-2 days)

**Objective**: Can CVC5 handle ModelChecker's quantifier patterns?

**Tasks**:
1. Install CVC5 Python bindings
2. Manually translate BM_CM_1 witness constraints to CVC5 API
3. Test if CVC5 finds countermodel
4. Test for determinism (run 5-10 times)
5. Compare timing with Z3

**Success Criteria**:
- CVC5 finds countermodel consistently
- Timing comparable to Z3 (~0.2-2s)
- No solver crashes or errors

**If Fails**: Abandon CVC5 migration, proceed with Plan 103

### Phase 2: Compatibility Test (1 week)

**Objective**: How much code needs changing for CVC5?

**Tasks**:
1. Identify all Z3 API calls in bimodal theory
2. Map to CVC5 equivalents
3. Estimate translation effort
4. Identify incompatible patterns
5. Test 3-5 examples with manual CVC5 translation

**Success Criteria**:
- <20% of API calls need significant changes
- All test examples work with CVC5
- Performance within 2× of Z3

**If Fails**: CVC5 too incompatible, consider pySMT or stay with Z3

### Phase 3: Performance Benchmark (1 week)

**Objective**: Is CVC5 faster, slower, or comparable to Z3?

**Tasks**:
1. Fully translate bimodal theory to CVC5
2. Run all 12 active examples
3. Measure solving time for each
4. Compare with Z3 baseline
5. Test logos, exclusion, imposition theories if possible

**Success Criteria**:
- CVC5 median time ≤ 1.5× Z3
- No examples timeout with CVC5 that work with Z3
- At least 3 examples faster with CVC5

**If Fails**: CVC5 not worth migration effort, proceed with Z3 + Plan 103

## Recommendations

### Immediate Actions (Next 1-2 Weeks)

1. **✅ Proceed with Plan 103 (Quantifier-Free Encoding)**
   - Eliminates the quantifier instantiation issue that motivated this investigation
   - Lower risk, lower effort than solver migration
   - Deterministic by design (no quantifiers = no instantiation heuristics)
   - Works with Z3, CVC5, or any SMT solver

2. **⚠️ Run Phase 1 Feasibility Test (Optional)**
   - If curious about CVC5, spend 1-2 days testing BM_CM_1
   - Low effort, provides empirical data
   - Informs long-term strategy
   - Don't block Plan 103 on this

3. **📝 Document Solver Dependency**
   - Add note in WITNESS_PREDICATES.md about solver choice
   - Mention quantifier-free approach is solver-agnostic
   - Reference this report for future consideration

### Medium-Term (1-3 Months)

4. **🔬 Monitor CVC5 Development**
   - Track quantifier instantiation improvements
   - Watch for relevant research (neural-guided instantiation)
   - Revisit if CVC5 shows breakthrough in deterministic solving

5. **📊 Collect Solver Performance Data**
   - Log Z3 solving times for all examples
   - Establish performance baseline
   - Use for future solver comparisons

### Long-Term (6+ Months)

6. **🎯 Consider pySMT Migration (If Needed)**
   - Only if multiple theories show solver-specific issues
   - Only if portfolio approach shows clear benefits
   - Design as incremental migration (one theory at a time)

7. **🚀 Portfolio for Robustness (Optional)**
   - If examples exhibit high variance in Z3 solving time
   - If timeouts become a production issue
   - Use pySMT to run Z3 + CVC5 in parallel

## Conclusion

### Summary

Alternative SMT solvers (CVC5, Yices, veriT) exist and have interesting features, but **none guarantee better determinism for quantified formulas**. All use heuristic instantiation strategies that can exhibit non-deterministic behavior.

### Key Insight

**The quantifier-free approach (Plan 103) solves the determinism problem regardless of solver choice**. Eliminating quantifiers eliminates the heuristic instantiation that causes non-determinism. This makes solver migration **orthogonal** to fixing the immediate issue.

### Decision Tree

```
Is quantifier-free encoding viable?
│
├─ YES → Implement Plan 103 (recommended)
│   │
│   └─ Does it solve BM_CM_1?
│       │
│       ├─ YES → DONE (no solver migration needed)
│       │
│       └─ NO → Reconsider solver options
│
└─ NO → Must use quantified formulas
    │
    └─ Is Z3 non-determinism unacceptable?
        │
        ├─ YES → Run Phase 1-3 empirical tests
        │   │
        │   └─ CVC5 better? → Migrate to CVC5
        │       CVC5 same?  → Consider portfolio
        │       CVC5 worse? → Investigate Z3 configuration
        │
        └─ NO → Stay with Z3, accept non-determinism
```

### Recommendation

**✅ PRIMARY**: Implement Plan 103 (quantifier-free witness encoding)
- Addresses root cause (quantifier instantiation)
- Works with any SMT solver
- Lower risk and effort than migration

**⚠️ SECONDARY**: Optional CVC5 feasibility test (1-2 days)
- Gather empirical data for future decisions
- Don't block on this

**❌ NOT RECOMMENDED**: Immediate solver migration
- High effort, uncertain benefits
- Quantifier-free approach makes it unnecessary
- Revisit only if Plan 103 fails

## References

### Academic Sources

**CVC5**:
- Barbosa, H., et al. (2022). "cvc5: A Versatile and Industrial-Strength SMT Solver". TACAS 2022.
- Reynolds, A., et al. (2024). "Machine Learning for Quantifier Selection in cvc5". arXiv:2408.14338.
- Dubrava, A., et al. (2025). "First Experiments with Neural cvc5". arXiv:2501.09379.

**SMT Solver Comparison**:
- Reynolds, A. "An Overview of Quantifier Instantiation in Modern SMT Solvers". SSFT 2021.

**Yices**:
- SRI International. "The Yices SMT Solver". https://yices.csl.sri.com/

**veriT**:
- Bouton, T., et al. (2009). "veriT: An Open, Trustable and Efficient SMT-Solver". CADE 2009.

**pySMT**:
- Gario, M., & Micheli, A. (2015). "pySMT: A Library for SMT Formulae Manipulation and Solving". Workshop on Satisfiability Modulo Theories.

### Internal Documentation

**Context**:
- [Report 007: Box Countermodel Failure Investigation](007_box_countermodel_failure_investigation.md)
- [Report 008: Witness Falsity Constraint Non-Determinism](008_witness_falsity_constraint_nondeterminism.md)
- [Plan 103: Quantifier-Free Witness Encoding](../plans/103_quantifier_free_witness_encoding.md)

**Technical Documentation**:
- [WITNESS_PREDICATES.md](../Code/src/model_checker/theory_lib/bimodal/docs/WITNESS_PREDICATES.md)
- [ARCHITECTURE.md](../Code/src/model_checker/theory_lib/bimodal/docs/ARCHITECTURE.md)

**Code References**:
- 109 files with Z3 dependencies across ModelChecker codebase
- Core solver integration: `Code/src/model_checker/models/structure.py`
- Witness predicates: `Code/src/model_checker/theory_lib/bimodal/semantic/`

### External Resources

**Solver Repositories**:
- Z3: https://github.com/Z3Prover/z3
- CVC5: https://github.com/cvc5/cvc5
- Yices2: https://github.com/SRI-CSL/yices2
- pySMT: https://github.com/pysmt/pysmt

**Documentation**:
- Z3 API: https://z3prover.github.io/api/html/namespacez3py.html
- CVC5 Docs: https://cvc5.github.io/
- pySMT Docs: https://pysmt.readthedocs.io/

**SMT-LIB**:
- SMT-LIB Standard: http://smtlib.cs.uiowa.edu/
- Solver List: https://smt-lib.org/solvers.shtml

## Appendix: CVC5 Feasibility Test Plan

If pursuing Phase 1 empirical testing:

### Setup (30 minutes)

```bash
# Install CVC5 Python bindings
pip install cvc5

# Verify installation
python -c "import cvc5; print(cvc5.__version__)"
```

### Test Script (BM_CM_1 Translation)

```python
#!/usr/bin/env python3
"""
BM_CM_1 test with CVC5: \Future A |- \Box A

Manual translation of bimodal theory witness constraints to CVC5 API.
"""

import cvc5
from cvc5 import Kind

def test_bm_cm_1_cvc5():
    # Create solver
    slv = cvc5.Solver()
    slv.setLogic("ALL")  # Use full logic for quantifiers + arithmetic
    slv.setOption("produce-models", "true")
    slv.setOption("smt.mbqi", "true")  # Enable MBQI like Z3

    # Types
    Int = slv.getIntegerSort()
    Bool = slv.getBooleanSort()

    # World and time variables
    eval_world = slv.mkConst(Int, "eval_world")
    eval_time = slv.mkConst(Int, "eval_time")

    # Witness predicate: accessible_world(world, time) -> world
    accessible_world = slv.mkConst(slv.mkFunctionSort([Int, Int], Int), "Box_A_accessible_world")

    # Atomic proposition truth function: truth(world, time, prop) -> bool
    truth = slv.mkConst(slv.mkFunctionSort([Int, Int, Int], Bool), "truth")

    # Proposition A (encoded as integer 0)
    A = slv.mkInteger(0)

    # Frame constraints (simplified)
    # World 0 and 1 exist
    # Times 0 and 1 exist
    # All (world, time) valid

    # Premise: \Future A (A true at some future time in world 0, time 0)
    # Simplified: truth(0, 1, A) = true
    premise = slv.mkTerm(Kind.APPLY_UF, truth, slv.mkInteger(0), slv.mkInteger(1), A)

    # Conclusion: \Box A (A true in all worlds at time 0)
    # We want this FALSE for countermodel
    # FALSE means: exists world where A is false
    # Using witness: truth(accessible_world(0, 0), 0, A) = false

    witness_world = slv.mkTerm(Kind.APPLY_UF, accessible_world, slv.mkInteger(0), slv.mkInteger(0))
    conclusion_false = slv.mkTerm(Kind.NOT,
        slv.mkTerm(Kind.APPLY_UF, truth, witness_world, slv.mkInteger(0), A)
    )

    # Add constraints
    slv.assertFormula(premise)
    slv.assertFormula(conclusion_false)

    # Solve
    import time
    start = time.time()
    result = slv.checkSat()
    elapsed = time.time() - start

    print(f"Result: {result}")
    print(f"Time: {elapsed:.4f}s")

    if result.isSat():
        print("Countermodel found!")
        # Extract model
        print(f"truth(0,1,A) = {slv.getValue(slv.mkTerm(Kind.APPLY_UF, truth, slv.mkInteger(0), slv.mkInteger(1), A))}")
        print(f"accessible_world(0,0) = {slv.getValue(witness_world)}")
        print(f"truth(witness,0,A) = {slv.getValue(slv.mkTerm(Kind.APPLY_UF, truth, witness_world, slv.mkInteger(0), A))}")
        return True
    else:
        print("No countermodel (UNSAT or UNKNOWN)")
        return False

if __name__ == "__main__":
    # Run 5 times to test determinism
    print("Testing BM_CM_1 with CVC5 (determinism check):")
    results = []
    for i in range(5):
        print(f"\n=== Run {i+1} ===")
        success = test_bm_cm_1_cvc5()
        results.append(success)

    if all(results):
        print("\n✅ DETERMINISTIC: All runs found countermodel")
    elif not any(results):
        print("\n❌ CONSISTENT FAILURE: No runs found countermodel")
    else:
        print(f"\n⚠️ NON-DETERMINISTIC: {sum(results)}/5 runs found countermodel")
```

### Evaluation Criteria

**Success**: All 5 runs find countermodel in <2s each
**Partial**: Some runs succeed, but not all (still non-deterministic)
**Failure**: No runs find countermodel, or crashes/errors

### Next Steps Based on Results

- **Success** → Proceed with Phase 2 (compatibility test)
- **Partial** → CVC5 has same non-determinism as Z3, not helpful
- **Failure** → CVC5 can't handle quantifier pattern, abandon migration
