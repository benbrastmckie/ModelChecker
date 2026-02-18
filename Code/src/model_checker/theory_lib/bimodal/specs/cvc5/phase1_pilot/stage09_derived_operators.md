# Stage 9: Derived Operators

## Metadata
- **Stage**: 9/12 | **Est. Duration**: 30 minutes (very fast, just composition)
- **Complexity**: Low (compose Stage 8 primitives)
- **Dependencies**: Stage 8 (primitive operators)
- **Files**: `operators.py` (derived operator classes)
- **Coverage Target**: >85%

## Objective

Migrate derived operators that are defined in terms of primitive operators. These should require minimal changes since they compose Stage 8 operators.

**Key Insight**: Derived operators call primitive operators. If Stage 8 is correct, Stage 9 should be nearly automatic.

## Actual Operators to Migrate

Based on typical bimodal logic:

1. **ConditionalOperator** (→): `A → B` = `¬A ∨ B` (uses Negation, Or)
2. **BiconditionalOperator** (↔): `A ↔ B` = `(A → B) ∧ (B → A)` (uses Conditional, And)
3. **TopOperator** (⊤): `⊤` = `¬⊥` (uses Negation, Bot)
4. **PossibilityOperator** (◇): `◇A` = `¬□¬A` (uses Negation, Necessity)
5. **EventuallyOperator** (F): Defined operators for temporal logic
6. **OnceOperator** (P): Defined operators for temporal logic

**Note**: Check actual code for exact names. These are typical derived operators.

## Key Pattern: Composition (No Direct Solver Calls)

Derived operators should NOT directly call solver methods. They compose primitive operators.

### Example: ConditionalOperator

```python
class ConditionalOperator(syntactic.Operator):
    def true_at(self, left_arg, right_arg, eval_point):
        """A → B is true iff ¬A ∨ B is true."""
        # Create negation of left argument
        negation_op = NegationOperator(self.semantics)
        neg_left = negation_op.true_at(left_arg, eval_point)

        # Get right argument constraint
        right_constraint = right_arg.true_at(self.semantics, eval_point)

        # Return disjunction (uses CVC5 OR from Stage 8)
        or_op = OrOperator(self.semantics)
        return or_op.true_at(neg_left, right_constraint, eval_point)

        # Alternatively, call solver directly (if primitives are methods, not classes):
        # return self.semantics.solver.mkTerm(Kind.OR, neg_left, right_constraint)
```

**Key Point**: The CVC5 migration happens in primitive operators. Derived just compose them.

## Implementation Tasks

### Task 1: TDD - Write Tests First (RED State)
**Duration**: 10 minutes

```python
def test_conditional_uses_negation_and_or(self):
    """Test ConditionalOperator composes Negation and Or."""
    # Create A → B
    # ...
    result = conditional_op.true_at(left_arg, right_arg, eval_point)

    # Should be CVC5 Term
    self.assertIsInstance(result, cvc5.Term)

    # Should be OR of (NOT left) and right
    self.assertEqual(result.getKind(), Kind.OR)
```

**Note**: Tests may be simple if operators just compose. Focus on structure verification.

### Task 2: Verify No Direct Z3 Calls
**Duration**: 5 minutes

**Check**: Ensure no `z3.*` calls in derived operator classes.

If found:
```python
# BAD (direct Z3 call)
return z3.Or(neg_left, right_constraint)

# GOOD (use primitive operator or solver)
return self.semantics.solver.mkTerm(Kind.OR, neg_left, right_constraint)
```

### Task 3: Update Operator Compositions (if needed)
**Duration**: 10 minutes

**Most likely**: Derived operators already use primitives correctly. May need zero changes.

**If changes needed**: Replace `z3.And/Or/Not` with `solver.mkTerm(Kind.AND/OR/NOT, ...)`

### Task 4: Test All Derived Operators
**Duration**: 5 minutes

- [ ] Test Conditional
- [ ] Test Biconditional
- [ ] Test Top
- [ ] Test Possibility (if exists)
- [ ] All tests pass

### Task 5: Coverage and Commit
**Duration**: 5 minutes

- [ ] Coverage >85%
- [ ] Commit

## Success Criteria Checklist

- [ ] All derived operators work with Stage 8 primitives
- [ ] No Z3 calls remain
- [ ] Tests pass
- [ ] Coverage >85%
- [ ] Ready for Stage 10 (witness constraints)

## Adaptive Scoping

**Expected Reality**: This stage may take <30 minutes if derived operators are already well-structured.

**If operators need refactoring**: Spend time to ensure clean composition pattern.

**Don't Overcomplicate**: If an operator works by composing primitives, leave it alone.

---

**Stage 9 Status**: ☑ Complete

**Completion Summary** (2025-10-03):
- ✅ All 6 derived operators validated as CVC5-compatible
- ✅ No code changes needed - operators are purely compositional
- ✅ All operators compose Stage 8 primitives correctly
- ✅ 13/13 tests passing (GREEN state)
- ✅ No Z3 dependencies in derived operators section
- ✅ Committed (bd0d50cb)

**Key Finding**: Derived operators use `DefinedOperator.derived_definition()` pattern which composes primitive operators. Since Stage 8 migrated all primitives to CVC5, derived operators automatically work with CVC5.

**Operators Validated**:
1. ConditionalOperator (→): `[OrOperator, [NegationOperator, left], right]`
2. BiconditionalOperator (↔): `[AndOperator, [Conditional, ...], [Conditional, ...]]`
3. TopOperator (⊤): `[NegationOperator, [BotOperator]]`
4. DefPossibilityOperator (◇): `[NegationOperator, [NecessityOperator, [NegationOperator, arg]]]`
5. DefFutureOperator: `[NegationOperator, [FutureOperator, [NegationOperator, arg]]]`
6. DefPastOperator: `[NegationOperator, [PastOperator, [NegationOperator, arg]]]`

**Files**:
- `test_operators_cvc5_stage09.py`: 13 validation tests (structure + Z3 absence)

**Duration**: <30 minutes (validation only)
**Tests**: 13/13 passing
**Commit**: bd0d50cb

**Ready for Stage 10 (Witness Constraints)**
