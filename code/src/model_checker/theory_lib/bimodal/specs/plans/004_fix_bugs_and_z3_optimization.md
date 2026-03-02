# Fix Bugs and Optimize Z3 Solver Configuration

## Metadata
- **Date**: 2025-10-01
- **Feature**: Fix witness predicate bugs and optimize Z3 solver for Future operator
- **Scope**: Bug fixes in semantic.false_at() and NecessityOperator.false_at(), Z3 tactic exploration
- **Estimated Phases**: 4
- **Related Reports**:
  - `003_future_past_asymmetry_investigation.md` (Z3 heuristic issue)
  - `002_witness_timeout_investigation.md` (timeout analysis)
  - `001_box_true_at_approaches.md` (implementation strategies)
- **Complexity**: Medium

## Overview

This plan addresses critical bugs discovered during the Future/Past asymmetry investigation and explores Z3 solver optimizations to improve performance for temporal+modal operators.

### Problems Identified

1. **Bug: semantic.false_at() doesn't delegate to operators**
   - Current: Returns `z3.Not(self.true_at(sentence, eval_point))`
   - Should: Delegate to `operator.false_at(*arguments, eval_point)` like `true_at()` does
   - Impact: Witness predicates in NecessityOperator.false_at() never get called

2. **Bug: NecessityOperator.false_at() uses wrong formula string**
   - Current: `formula_str = semantics._get_formula_string(argument)` gets "A"
   - Should: Construct `formula_str = f"Box_{argument_str}"` to get "Box_A"
   - Impact: Witness lookup fails because registry has "Box_A" not "A"

3. **Performance: Z3 struggles with Future operator**
   - Future operator (`time > 0`) returns `unknown`
   - Past operator (`time < 0`) returns `sat` correctly
   - Root cause: Z3 quantifier instantiation heuristics
   - Operators are logically symmetric, implementation is correct

### Goals

1. Apply bug fixes to enable witness predicates
2. Test that witness predicates work correctly for Box formulas
3. Implement Approach 3 (Modal Duality) from Report 001 as new `\Necessity` operator
4. Create experimental examples comparing `\Box` (ForAll) vs `\Necessity` (Modal Duality)
5. Document performance comparison and Z3 configuration best practices

## Success Criteria

- [ ] semantic.false_at() correctly delegates to operator methods
- [ ] NecessityOperator.false_at() finds witnesses with correct formula string
- [ ] At least one simple Box example works with witnesses (e.g., `A |- \Box A`)
- [ ] New `\Necessity` operator implemented using modal duality (Approach 3)
- [ ] Experimental examples created comparing `\Box` vs `\Necessity`
- [ ] Performance comparison documented with timing data
- [ ] Code includes comments explaining both approaches

## Technical Design

### Architecture

The fixes maintain the existing witness predicate architecture from Plan 003:
1. **WitnessRegistry**: Stores accessible_world predicates (unchanged)
2. **WitnessConstraintGenerator**: Generates modal accessibility constraints (unchanged)
3. **BimodalSemantics**: Orchestrates witness registration (unchanged)
4. **NecessityOperator**: Uses witnesses in false_at() (fix bug here)
5. **BimodalSemantics.false_at()**: Delegates to operators (fix bug here)

### Bug Fix Strategy

Both bugs prevent the witness predicate system from working:
- **Bug 1** prevents NecessityOperator.false_at() from being called at all
- **Bug 2** causes failure when it IS called (after fixing Bug 1)

Fix order: Bug 1 → Bug 2 (must fix in sequence)

### Z3 Optimization Strategy

Per Report 003, the Future/Past asymmetry is a Z3 solver heuristic issue, not a code bug. We'll experiment with:
1. **Quantifier instantiation strategies**: `smt.mbqi`, `smt.qi.eager_threshold`
2. **Solver tactics**: `simplify`, `solve-eqs`, `qe` (quantifier elimination)
3. **Pattern hints**: Guide Z3's E-matching triggers
4. **Timeout adjustments**: Increase for complex examples

## Implementation Phases

### Phase 1: Fix semantic.false_at() Delegation Bug

**Objective**: Make semantic.false_at() delegate to operator methods like true_at() does

**Complexity**: Low

**Files Modified**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py`

**Tasks**:
- [ ] Read current semantic.false_at() implementation (line 1030-1043)
- [ ] Compare with semantic.true_at() delegation pattern (line 999-1028)
- [ ] Rewrite false_at() to match true_at() structure:
  ```python
  def false_at(self, sentence, eval_point):
      """Returns a Z3 formula satisfied when sentence is false at eval_point."""
      # Extract world and time from eval_point
      eval_world = eval_point["world"]
      eval_time = eval_point["time"]

      # Get the world array from the world ID
      world_array = self.world_function(eval_world)

      sentence_letter = sentence.sentence_letter

      # base case: sentence letter
      if sentence_letter is not None:
          eval_world_state = z3.Select(world_array, eval_time)
          return z3.Not(self.truth_condition(eval_world_state, sentence_letter))

      # recursive case: delegate to operator's false_at method
      operator = sentence.operator
      arguments = sentence.arguments or ()
      return operator.false_at(*arguments, eval_point)
  ```
- [ ] Add comment explaining delegation pattern matches true_at()

**Testing**:
```bash
# Test that false_at delegation works for simple operators
PYTHONPATH=code/src python3 -c "
from model_checker.syntactic import Syntax
from model_checker.theory_lib.bimodal import BimodalSemantics, bimodal_operators
semantics = BimodalSemantics({'N': 2, 'M': 1})
syntax = Syntax([], [r'\neg A'], bimodal_operators)
# Should delegate to NegationOperator.false_at() which returns true_at()
print('Delegation test passed if no error')
"
```

**Validation**:
- No errors during formula evaluation
- Operators receive false_at() calls correctly
- Ready for Phase 2 (witness predicates will now be reached)

---

### Phase 2: Fix NecessityOperator.false_at() Formula String Bug

**Objective**: Construct correct formula string for witness lookup in NecessityOperator.false_at()

**Complexity**: Low

**Files Modified**:
- `code/src/model_checker/theory_lib/bimodal/operators.py`

**Tasks**:
- [ ] Read current NecessityOperator.false_at() implementation (line 408-463)
- [ ] Locate formula string construction (line 432)
- [ ] Replace `formula_str = semantics._get_formula_string(argument)` with:
  ```python
  # Get formula string for witness lookup
  # Need to construct the full Box formula string from the argument
  argument_str = semantics._get_formula_string(argument)
  formula_str = f"Box_{argument_str}"  # Constructs "Box_A" from "A"
  ```
- [ ] Update comment explaining why we construct "Box_A" not just "A"

**Rationale**:
- Witness registry stores predicates by full formula string (e.g., "Box_A")
- NecessityOperator.false_at() only receives the argument (e.g., "A")
- Must reconstruct the full formula string to match registry key

**Testing**:
```bash
# Test that witness lookup finds correct predicate
PYTHONPATH=code/src python3 -c "
from model_checker.syntactic import Syntax
from model_checker.theory_lib.bimodal import BimodalSemantics, BimodalProposition, bimodal_operators
from model_checker.models.constraints import ModelConstraints

settings = {'N': 2, 'M': 1, 'contingent': True, 'max_time': 5, 'expectation': True, 'iterate': 1}
syntax = Syntax(['A'], [r'\Box A'], bimodal_operators)
semantics = BimodalSemantics(settings)
mc = ModelConstraints(settings, syntax, semantics, BimodalProposition)

print(f'Witnesses registered: {list(semantics.witness_registry.predicates.keys())}')
assert 'Box_A_accessible_world' in semantics.witness_registry.predicates
print('Witness lookup test passed')
"
```

**Validation**:
- Witness predicate lookup succeeds with "Box_A"
- No WitnessPredicateError exceptions
- Ready for Phase 3 (end-to-end tests)

---

### Phase 3: Implement Modal Duality Approach (Approach 3)

**Objective**: Implement `\Necessity` operator using modal duality and create experimental examples comparing approaches

**Complexity**: Medium

**Files Modified**:
- `code/src/model_checker/theory_lib/bimodal/operators.py` (new NecessityDualityOperator)
- `code/src/model_checker/theory_lib/bimodal/examples.py` (new experimental examples)

**Background**:

Per Report 001, Approach 3 (Modal Duality) defines `true_at()` as `Not(false_at())`, leveraging the modal duality theorem: □φ ≡ ¬◇¬φ. This approach:
- Fully leverages witness predicates (all quantification in `false_at()`)
- Is theoretically elegant and standard in modal logic
- May perform better for large models than ForAll approach
- Enables direct comparison with current `\Box` implementation

**Part A: Implement NecessityDualityOperator**

Tasks:
- [ ] Create new operator class in operators.py:
  ```python
  class NecessityDualityOperator(syntactic.Operator):
      """Modal necessity operator using modal duality approach.

      This is an experimental operator implementing Approach 3 from
      specs/reports/001_box_true_at_approaches.md for performance comparison.

      Key difference from NecessityOperator:
      - NecessityOperator.true_at() uses ForAll quantification (Approach 1)
      - NecessityDualityOperator.true_at() uses z3.Not(false_at()) (Approach 3)

      Both operators:
      - Use identical false_at() implementation with witness predicates
      - Should be semantically equivalent
      - Differ only in true_at() encoding strategy

      Modal Duality Foundation:
      - Theorem: □φ ≡ ¬◇¬φ
      - Equivalence: □φ@w ⟺ ∀w'. φ@w' ⟺ ¬∃w'. ¬φ@w' ⟺ ¬(□φ is false)@w
      """

      def __init__(self, semantics):
          super().__init__(
              r'\Necessity',  # LaTeX syntax
              1,              # arity
              semantics=semantics
          )

      def true_at(self, argument, eval_point):
          """Returns true if argument is true in ALL possible worlds.

          Uses modal duality: Box is true iff it's NOT false.
          This leverages witness predicates in false_at() for all quantification.
          """
          return z3.Not(self.false_at(argument, eval_point))

      def false_at(self, argument, eval_point):
          """Returns true if argument is false in SOME possible world.

          Uses witness predicate - IDENTICAL to NecessityOperator.false_at().
          Witness must be registered during model constraint generation.
          """
          semantics = self.semantics
          eval_world = eval_point["world"]
          eval_time = eval_point["time"]

          # Get formula string for witness lookup
          # Construct full Necessity formula string from argument
          argument_str = semantics._get_formula_string(argument)
          formula_str = f"Necessity_{argument_str}"

          # Witness predicate MUST be registered (fail-fast)
          if not semantics.witness_registry.has_witness_predicate(formula_str):
              raise WitnessPredicateError(
                  f"Witness predicate '{formula_str}' evaluation failed: "
                  f"predicate was not registered. This indicates the witness "
                  f"constraint generator did not process this formula during "
                  f"model constraint generation."
              )

          accessible_world_pred = semantics.witness_registry.get_witness_predicate(formula_str)
          witness_world = accessible_world_pred(eval_world, eval_time)

          return z3.And(
              semantics.is_world(witness_world),
              semantics.is_valid_time_for_world(witness_world, eval_time),
              semantics.false_at(argument, {"world": witness_world, "time": eval_time})
          )
  ```

- [ ] Register operator in bimodal_operators list:
  ```python
  # In operators.py, update bimodal_operators_factory
  def bimodal_operators_factory(semantics):
      """Create operators for bimodal theory."""
      return [
          # ... existing operators ...
          NecessityOperator(semantics),
          NecessityDualityOperator(semantics),  # NEW: experimental modal duality
          # ... rest of operators ...
      ]
  ```

- [ ] Update WitnessConstraintGenerator to handle \Necessity formulas:
  ```python
  # In semantic/witness_constraint_generator.py
  # Add to _register_modal_witnesses() or equivalent:

  if formula_str.startswith('Necessity_'):
      # Same witness structure as Box
      accessible_world_pred = z3.Function(
          f"{formula_str}_accessible_world",
          z3.IntSort(), z3.IntSort(), z3.IntSort()
      )
      self.registry.register_witness_predicate(formula_str, accessible_world_pred)
  ```

**Part B: Create Experimental Examples**

Tasks:
- [ ] Add modal examples comparing `\Box` vs `\Necessity` in examples.py:
  ```python
  # Modal Duality Comparison Examples
  # These compare NecessityOperator (ForAll) vs NecessityDualityOperator (Modal Duality)

  MD_CM_1 = BimodalArgument(
      ['A'],
      [r'\Necessity A'],
      'MD_CM_1',
      settings={'N': 2, 'M': 1, 'contingent': True, 'max_time': 5, 'expectation': True, 'iterate': 1},
      description=r'Modal countermodel: A |- \Necessity A (should match Box behavior)'
  )

  MD_CM_2 = BimodalArgument(
      [r'\neg A'],
      [r'\Necessity A'],
      'MD_CM_2',
      settings={'N': 2, 'M': 1, 'contingent': True, 'max_time': 5, 'expectation': True, 'iterate': 1},
      description=r'Modal countermodel: \neg A |- \Necessity A (should match Diamond behavior)'
  )

  MD_V_1 = BimodalArgument(
      [r'\Necessity (A \implies B)', 'A'],
      ['B'],
      'MD_V_1',
      settings={'N': 2, 'M': 1, 'contingent': True, 'max_time': 5, 'expectation': False, 'iterate': 1},
      description=r'Modal validity: \Necessity (A \implies B), A |- B (K axiom with Necessity)'
  )
  ```

- [ ] Add bimodal examples combining `\Necessity` with temporal operators:
  ```python
  # Bimodal examples with Necessity (analogs of BM_CM_* using \Necessity)

  BM_NEC_CM_1 = BimodalArgument(
      [r'\Future A'],
      [r'\Necessity A'],
      'BM_NEC_CM_1',
      settings={'N': 2, 'M': 2, 'contingent': True, 'max_time': 10, 'expectation': True, 'iterate': 1},
      description=r'Bimodal countermodel with Necessity: \Future A |- \Necessity A (compare BM_CM_1)'
  )

  BM_NEC_CM_2 = BimodalArgument(
      [r'\Past A'],
      [r'\Necessity A'],
      'BM_NEC_CM_2',
      settings={'N': 2, 'M': 2, 'contingent': True, 'max_time': 10, 'expectation': True, 'iterate': 1},
      description=r'Bimodal countermodel with Necessity: \Past A |- \Necessity A (compare BM_CM_2)'
  )
  ```

- [ ] Add comparison examples testing nested modals:
  ```python
  MD_NEST_1 = BimodalArgument(
      ['A'],
      [r'\Necessity \Necessity A'],
      'MD_NEST_1',
      settings={'N': 2, 'M': 1, 'contingent': True, 'max_time': 10, 'expectation': True, 'iterate': 1},
      description=r'Nested Necessity: A |- \Necessity \Necessity A'
  )
  ```

**Part C: Create Performance Benchmark Script**

Tasks:
- [ ] Create benchmark comparing `\Box` vs `\Necessity`:
  ```python
  # File: /tmp/modal_duality_benchmark.py
  import z3
  import time
  from model_checker.syntactic import Syntax
  from model_checker.theory_lib.bimodal import BimodalSemantics, BimodalProposition, bimodal_operators
  from model_checker.models.constraints import ModelConstraints

  def benchmark_operator(operator, premises, conclusions, settings):
      """Benchmark a specific operator on a formula."""
      syntax = Syntax(premises, conclusions, bimodal_operators)
      semantics = BimodalSemantics(settings)
      mc = ModelConstraints(settings, syntax, semantics, BimodalProposition)

      solver = z3.Solver()
      solver.set("timeout", settings.get('max_time', 10) * 1000)

      for c in mc.all_constraints:
          solver.add(c)

      start = time.time()
      result = solver.check()
      elapsed = time.time() - start

      return {
          'operator': operator,
          'result': str(result),
          'time': elapsed,
          'constraints': len(mc.all_constraints)
      }

  # Test configurations
  test_cases = [
      ('Simple', ['A'], [r'\Box A'], r'\Necessity A'),
      ('Negation', [r'\neg A'], [r'\Box A'], r'\Necessity A'),
      ('Bimodal Future', [r'\Future A'], [r'\Box A'], r'\Necessity A'),
      ('Bimodal Past', [r'\Past A'], [r'\Box A'], r'\Necessity A'),
  ]

  settings = {'N': 2, 'M': 2, 'contingent': True, 'max_time': 10, 'expectation': True, 'iterate': 1}

  print("Performance Comparison: \\Box (ForAll) vs \\Necessity (Modal Duality)")
  print("="*70)

  for name, premises, box_concl, nec_concl in test_cases:
      print(f"\n{name}:")
      box_result = benchmark_operator('Box', premises, [box_concl], settings)
      nec_result = benchmark_operator('Necessity', premises, [nec_concl], settings)

      print(f"  \\Box:       {box_result['result']:10s} in {box_result['time']:.3f}s ({box_result['constraints']} constraints)")
      print(f"  \\Necessity: {nec_result['result']:10s} in {nec_result['time']:.3f}s ({nec_result['constraints']} constraints)")

      if box_result['result'] == nec_result['result']:
          speedup = box_result['time'] / nec_result['time'] if nec_result['time'] > 0 else float('inf')
          print(f"  Speedup: {speedup:.2f}x ({'Necessity faster' if speedup > 1 else 'Box faster'})")
  ```

- [ ] Run benchmark and analyze:
  ```bash
  PYTHONPATH=code/src python3 /tmp/modal_duality_benchmark.py > /tmp/modal_duality_results.txt
  cat /tmp/modal_duality_results.txt
  ```

**Part D: Verify Bug Fixes with Simple Tests**

Tasks:
- [ ] Test simple `\Box` example works after bug fixes:
  ```bash
  PYTHONPATH=code/src python3 <<'EOF'
  from model_checker.syntactic import Syntax
  from model_checker.theory_lib.bimodal import BimodalSemantics, BimodalProposition, bimodal_operators
  from model_checker.models.constraints import ModelConstraints
  import z3

  settings = {'N': 2, 'M': 1, 'contingent': True, 'max_time': 5, 'expectation': True, 'iterate': 1}
  syntax = Syntax(['A'], [r'\Box A'], bimodal_operators)
  semantics = BimodalSemantics(settings)
  mc = ModelConstraints(settings, syntax, semantics, BimodalProposition)

  solver = z3.Solver()
  solver.set("timeout", 3000)
  for c in mc.all_constraints:
      solver.add(c)

  result = solver.check()
  print(f"A |- \\Box A: {result}")
  assert result == z3.sat, "Should find countermodel"
  print("✓ Box operator bug fixes verified")
  EOF
  ```

- [ ] Test simple `\Necessity` example works:
  ```bash
  PYTHONPATH=code/src python3 <<'EOF'
  from model_checker.syntactic import Syntax
  from model_checker.theory_lib.bimodal import BimodalSemantics, BimodalProposition, bimodal_operators
  from model_checker.models.constraints import ModelConstraints
  import z3

  settings = {'N': 2, 'M': 1, 'contingent': True, 'max_time': 5, 'expectation': True, 'iterate': 1}
  syntax = Syntax(['A'], [r'\Necessity A'], bimodal_operators)
  semantics = BimodalSemantics(settings)
  mc = ModelConstraints(settings, syntax, semantics, BimodalProposition)

  solver = z3.Solver()
  solver.set("timeout", 3000)
  for c in mc.all_constraints:
      solver.add(c)

  result = solver.check()
  print(f"A |- \\Necessity A: {result}")
  assert result == z3.sat, "Should find countermodel"
  print("✓ Necessity operator works")
  EOF
  ```

**Testing**:
```bash
# Run experimental examples
PYTHONPATH=code/src code/dev_cli.py code/src/model_checker/theory_lib/bimodal/examples.py --filter MD_
PYTHONPATH=code/src code/dev_cli.py code/src/model_checker/theory_lib/bimodal/examples.py --filter BM_NEC_
```

**Validation**:
- [ ] NecessityDualityOperator class compiles without errors
- [ ] Witness registration handles `\Necessity` formulas
- [ ] MD_CM_1 returns same result as equivalent Box example
- [ ] MD_CM_2 returns same result as equivalent Diamond example
- [ ] BM_NEC_CM_1 and BM_NEC_CM_2 comparable to BM_CM_1/BM_CM_2
- [ ] Performance benchmark completes and shows timing comparison
- [ ] Both operators semantically equivalent (same sat/unsat results)
- [ ] Documentation explains modal duality approach

---

### Phase 4: Z3 Configuration Optimization and Documentation

**Objective**: Experiment with Z3 tactics to improve Future operator performance, document findings

**Complexity**: Medium

**Files Modified**:
- `code/src/model_checker/theory_lib/bimodal/semantic.py` (add Z3 configuration if beneficial)
- `code/src/model_checker/theory_lib/bimodal/operators.py` (document Z3 limitations)

**Part A: Z3 Tactic Experiments**

Tasks:
- [ ] Create benchmark script testing Z3 configurations:
  ```python
  # File: /tmp/z3_tactic_benchmark.py
  import z3
  import time
  from model_checker.syntactic import Syntax
  from model_checker.theory_lib.bimodal import BimodalSemantics, BimodalProposition, bimodal_operators
  from model_checker.models.constraints import ModelConstraints

  def test_config(name, premises, conclusions, solver_config):
      """Test a specific Z3 configuration."""
      settings = {'N': 2, 'M': 2, 'contingent': True, 'max_time': 10, 'expectation': True, 'iterate': 1}

      syntax = Syntax(premises, conclusions, bimodal_operators)
      semantics = BimodalSemantics(settings)
      mc = ModelConstraints(settings, syntax, semantics, BimodalProposition)

      solver = z3.Solver()
      solver.set("timeout", 10000)  # 10 second timeout

      # Apply configuration
      for key, value in solver_config.items():
          solver.set(key, value)

      for c in mc.all_constraints:
          solver.add(c)

      start = time.time()
      result = solver.check()
      elapsed = time.time() - start

      return {
          'name': name,
          'result': str(result),
          'time': f"{elapsed:.3f}s",
          'config': solver_config
      }

  # Test configurations
  configs = {
      'default': {},
      'mbqi': {'smt.mbqi': True},
      'eager_qi': {'smt.qi.eager_threshold': 100},
      'max_instances': {'smt.qi.max_instances': 1000},
      'combined': {'smt.mbqi': True, 'smt.qi.eager_threshold': 100, 'smt.qi.max_instances': 1000}
  }

  # Test Future operator (problematic)
  print("Testing Future operator with different Z3 configs:")
  print("="*60)
  for config_name, config in configs.items():
      result = test_config("Future", [r'\Future A'], ['A'], config)
      print(f"{config_name:15s}: {result['result']:10s} in {result['time']}")

  print("\n" + "="*60)
  print("Testing Past operator (baseline):")
  print("="*60)
  for config_name, config in configs.items():
      result = test_config("Past", [r'\Past A'], ['A'], config)
      print(f"{config_name:15s}: {result['result']:10s} in {result['time']}")
  ```

- [ ] Run benchmark and record results:
  ```bash
  PYTHONPATH=code/src python3 /tmp/z3_tactic_benchmark.py > /tmp/z3_benchmark_results.txt
  cat /tmp/z3_benchmark_results.txt
  ```

- [ ] Analyze which configurations (if any) help Future operator

**Part B: Add Z3 Configuration (if beneficial)**

Tasks:
- [ ] If a Z3 configuration improves Future operator, add it to BimodalSemantics:
  ```python
  # In semantic.py, __init__ method
  def __init__(self, settings):
      super().__init__(settings)

      # ... existing initialization ...

      # Z3 configuration for bimodal logic
      # Per specs/reports/003_future_past_asymmetry_investigation.md,
      # Future operator struggles with default quantifier heuristics
      # Testing showed [config_name] improves Future operator performance
      # Trade-off: [note any downsides]
      self._z3_config = {
          'smt.mbqi': True,  # Example - adjust based on benchmark results
          # Add more settings as needed
      }
  ```

**Part C: Document Z3 Limitations**

Tasks:
- [ ] Add Z3 performance notes to FutureOperator:
  ```python
  class FutureOperator(syntactic.Operator):
      """Temporal operator evaluating formulas at all future times.

      **Z3 Solver Performance Note**:
      Z3's quantifier instantiation heuristics struggle with 'time > 0' (future)
      compared to 'time < 0' (past) in complex bimodal constraints, despite
      logical symmetry. This can cause 'unknown' results or timeouts.
      See specs/reports/003_future_past_asymmetry_investigation.md for analysis.
      """
  ```

- [ ] Add similar note to PastOperator for comparison

- [ ] Document findings in implementation summary

**Testing**:
```bash
# Run full example suite
PYTHONPATH=code/src timeout 60 code/dev_cli.py code/src/model_checker/theory_lib/bimodal/examples.py
```

**Validation**:
- [ ] Z3 benchmark results documented
- [ ] Code comments explain Z3 limitations
- [ ] Future/Past operator performance asymmetry documented
- [ ] Decision on Z3 configuration documented (use or not use)

---

## Post-Implementation: Choose Between Box and Necessity

**Context**: After Phase 3, we have TWO modal necessity operators:
- `\Box` (NecessityOperator) - Uses ForAll for true_at() (Approach 1)
- `\Necessity` (NecessityDualityOperator) - Uses modal duality for true_at() (Approach 3)

**Decision Point**: Which operator should be the default/primary implementation?

**Factors to Consider**:
1. **Performance**: Which approach is faster on average? (See Phase 3 benchmark results)
2. **Correctness**: Both should be semantically equivalent (verify in testing)
3. **Maintainability**: Modal duality is simpler (one line), ForAll is more explicit
4. **Z3 Interaction**: Which approach interacts better with Z3 optimizations from Phase 4?
5. **Future Work**: Which generalizes better to other modal theories?

**Options**:

**Option 1: Keep Both**
- Maintain both operators for flexibility
- Users can choose based on use case
- Allows continued benchmarking
- Cons: More maintenance burden

**Option 2: Choose \Box (ForAll) as Primary**
- Keep ForAll approach as standard
- More explicit encoding of modal semantics
- Proven pattern in modal logic implementations
- Keep \Necessity as experimental/alternative

**Option 3: Choose \Necessity (Modal Duality) as Primary**
- Adopt modal duality if benchmarks show benefit
- Simpler implementation (less code)
- Fully leverages witness strategy
- Rename to \Box and deprecate old NecessityOperator

**Recommendation**: Make decision based on Phase 3 benchmark data, documenting:
- Performance comparison results
- Any edge cases where one approach fails/struggles
- Z3 optimization interaction
- Final choice with rationale in implementation summary

---

## Testing Strategy

### Unit Tests
- Test semantic.false_at() delegation for all operator types
- Test NecessityOperator.false_at() witness lookup
- Test witness predicate generation for Box formulas

### Integration Tests
- Test simple modal examples (pure Box, pure Diamond)
- Test simple temporal examples (pure Past, pure Future)
- Test bimodal combinations (Box+Past, Box+Future)

### Regression Tests
- Run existing bimodal test suite
- Verify no examples that previously worked now fail
- Document known limitations (Future operator timeouts)

### Performance Tests
- Benchmark Z3 configurations
- Compare solving times with/without optimizations
- Document performance characteristics

## Dependencies

### Prerequisites
- Witness predicate infrastructure from Plan 003 (complete)
- WitnessRegistry with accessible_world predicates (complete)
- WitnessConstraintGenerator (complete)
- BimodalSemantics witness registration hooks (complete)

### External Dependencies
- Z3 Python bindings (existing)
- Python 3.8+ (existing)

### No New Dependencies
This plan only fixes bugs in existing code and tunes Z3 configuration.

## Risk Assessment

### Low Risk
- **Bug fixes are straightforward**: Clear delegation pattern, simple string construction
- **No architectural changes**: Working within existing witness predicate framework
- **Incremental testing**: Each phase validates before moving forward

### Medium Risk
- **Z3 configuration tuning**: Changes may help Future but hurt other cases
- **Performance unpredictability**: Z3 behavior can be non-intuitive

### Mitigation Strategies
- Test each bug fix independently before combining
- Benchmark Z3 configs on multiple examples before applying globally
- Document all Z3 limitations and workarounds
- Keep default config as fallback option

## Documentation Requirements

### Code Comments
- Explain semantic.false_at() delegation matches true_at()
- Document NecessityOperator formula string construction
- Add Z3 performance notes to FutureOperator and PastOperator
- Comment any Z3 configuration changes

### Implementation Notes
- Document Z3 benchmark results
- Record which configs were tried and results
- Explain decision to use or not use specific Z3 tactics

### Update Reports
- Update 002_witness_timeout_investigation.md with resolution
- Reference 003_future_past_asymmetry_investigation.md for Z3 limitations
- Cross-reference 001_box_true_at_approaches.md for future optimization

## Git Commit Strategy

### Phase 1 Commit
```bash
git add code/src/model_checker/theory_lib/bimodal/semantic.py
git commit -m "$(cat <<'EOF'
fix(bimodal): make semantic.false_at() delegate to operators

Fix bug where semantic.false_at() returned Not(true_at()) instead of
delegating to operator.false_at() methods. This prevented witness predicates
in NecessityOperator.false_at() from being called.

Changes:
- Rewrite semantic.false_at() to match true_at() delegation pattern
- Base case: sentence letters return Not(truth_condition())
- Recursive case: delegate to operator.false_at(*arguments, eval_point)
- Add comment explaining delegation mirrors true_at()

Impact:
- Enables witness predicates for modal operators
- Fixes architectural inconsistency between true_at/false_at
- Required for witness predicate system to function

Testing:
- Verified delegation works for negation operator
- No errors during formula evaluation
- Ready for NecessityOperator witness predicate fix

Related: specs/reports/003_future_past_asymmetry_investigation.md

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude <noreply@anthropic.com>
EOF
)"
```

### Phase 2 Commit
```bash
git add code/src/model_checker/theory_lib/bimodal/operators.py
git commit -m "$(cat <<'EOF'
fix(bimodal): construct correct formula string in NecessityOperator.false_at()

Fix bug where NecessityOperator.false_at() looked for witness predicate "A"
instead of "Box_A". Operator methods receive only arguments, not full formula,
so must reconstruct formula string for witness registry lookup.

Changes:
- Get argument string: argument_str = semantics._get_formula_string(argument)
- Construct Box formula: formula_str = f"Box_{argument_str}"
- Update comment explaining formula string construction

Impact:
- Witness predicate lookup now succeeds
- NecessityOperator.false_at() can find registered witnesses
- Completes witness predicate bug fixes

Testing:
- Verified witness lookup finds "Box_A_accessible_world"
- No WitnessPredicateError exceptions
- Simple modal examples work correctly

Related: specs/reports/003_future_past_asymmetry_investigation.md

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude <noreply@anthropic.com>
EOF
)"
```

### Phase 3 Commit
```bash
git add code/src/model_checker/theory_lib/bimodal/operators.py
git add code/src/model_checker/theory_lib/bimodal/semantic/witness_constraint_generator.py
git add code/src/model_checker/theory_lib/bimodal/examples.py
git commit -m "$(cat <<'EOF'
feat(bimodal): implement NecessityDualityOperator using modal duality (Approach 3)

Implement experimental modal necessity operator using modal duality theorem
(□φ ≡ ¬◇¬φ) for performance comparison with standard ForAll approach.

New Operator:
- \Necessity: true_at() = Not(false_at())
- Uses witness predicates exclusively (no ForAll quantification)
- Semantically equivalent to \Box but different encoding strategy
- Enables empirical comparison of Approach 1 vs Approach 3 from Report 001

Implementation:
- NecessityDualityOperator class with modal duality true_at()
- Identical false_at() to NecessityOperator (witness-based)
- Witness registration for Necessity_ formulas in constraint generator
- Comprehensive docstring explaining modal duality foundation

Experimental Examples:
- MD_CM_1, MD_CM_2: Simple modal countermodels
- MD_V_1: Modal validity (K axiom)
- BM_NEC_CM_1, BM_NEC_CM_2: Bimodal with temporal operators
- MD_NEST_1: Nested Necessity operator
- Performance benchmark script comparing \Box vs \Necessity

Testing:
- All MD_* examples return expected results
- Both operators semantically equivalent on test suite
- Performance benchmark shows timing comparison
- No witness predicate errors

Related: specs/reports/001_box_true_at_approaches.md (Approach 3)
         specs/plans/004_fix_bugs_and_z3_optimization.md (Phase 3)

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude <noreply@anthropic.com>
EOF
)"
```

### Phase 4 Commit (if Z3 config added)
```bash
git add code/src/model_checker/theory_lib/bimodal/semantic.py
git add code/src/model_checker/theory_lib/bimodal/operators.py
git commit -m "$(cat <<'EOF'
perf(bimodal): add Z3 configuration and document limitations

Add Z3 solver configuration to improve temporal operator performance.
Document known limitation where Future operator struggles with Z3
quantifier heuristics despite being logically symmetric to Past.

Changes:
- Add _z3_config to BimodalSemantics with [settings based on benchmark]
- Document Z3 performance asymmetry in FutureOperator docstring
- Document modal duality vs ForAll trade-offs in operators.py
- Add reference to investigation reports

Z3 Benchmark Results:
- [Config name]: Future [result], Past [result]
- Chosen config: [name] based on [rationale]
- Trade-offs: [any downsides noted]

Modal Duality Performance:
- \Box (ForAll) vs \Necessity (Duality): [comparison results]
- Recommendation: [which approach to use when]

Testing:
- Simple modal: A |- \Box A returns sat ✓
- Past temporal: \Past A |- A returns sat ✓
- BM_CM_2: \Past A |- \Box A [result]
- Z3 benchmark: [summary of findings]
- Modal duality benchmark: [summary of findings]

Related: specs/reports/003_future_past_asymmetry_investigation.md
         specs/reports/001_box_true_at_approaches.md
         specs/plans/004_fix_bugs_and_z3_optimization.md

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude <noreply@anthropic.com>
EOF
)"
```

## Notes

### Why This Plan Incorporates Modal Duality

**Report 001** recommends:
- Phase 1: Implement Approach 1 (Keep ForAll) for NecessityOperator.true_at()
- Phase 2: Implement Approach 3 (Modal Duality) as alternative

**This Plan** implements:
- Phase 1-2: Fix critical bugs enabling witness predicates
- Phase 3: Implement Approach 3 (Modal Duality) as `\Necessity` operator
- Phase 4: Z3 optimization experiments

**Rationale for Including Modal Duality**:
1. **User Request**: User specifically interested in Approach 3 for experimentation
2. **Low Complexity**: Modal duality is simple to implement (one line of code)
3. **Direct Comparison**: Enables empirical A/B testing of both approaches
4. **Bug Fixes First**: Phases 1-2 ensure witness infrastructure works before comparison
5. **Data-Driven**: Generate performance data to choose best approach

**Changes from Original Plan**:
- Originally Phase 3 was pure Z3 optimization
- Now Phase 3 implements modal duality operator with experimental examples
- Z3 optimization moved to Phase 4
- Enables comparing both approaches under same Z3 configurations

### Implementation Path

This plan delivers:
1. **Phase 1-2**: Bug fixes → witness predicates work correctly
2. **Phase 3**: Modal duality implementation → both approaches available
3. **Phase 4**: Z3 optimization → improve both approaches
4. **Post-Implementation**: Choose primary approach based on benchmarks

**Comparison Enabled**:
- `\Box` (ForAll) vs `\Necessity` (Modal Duality)
- Same witness infrastructure, different true_at() encoding
- Performance benchmarks on modal and bimodal examples
- Z3 configuration impact on both approaches

---

## Summary

This plan delivers:
1. **Working witness predicates** (fixes critical bugs in Phases 1-2)
2. **Modal duality implementation** (experimental `\Necessity` operator in Phase 3)
3. **Performance comparison** (empirical data comparing ForAll vs Modal Duality)
4. **Experimental examples** (MD_* and BM_NEC_* for testing both approaches)
5. **Z3 optimization** (configuration experiments in Phase 4)
6. **Documented limitations** (Z3 heuristic asymmetry, approach trade-offs)
7. **Decision framework** (choose primary approach based on benchmark data)

Implementation is straightforward, risk is low, and directly addresses user request to experiment with Approach 3 (Modal Duality) from Report 001.
