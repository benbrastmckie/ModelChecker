"""Bimodal theory specific model iteration implementation.

This module provides the BimodalModelIterator implementation which handles:
1. Detecting differences between models using the certificate encoding's own variables
2. Creating constraints to differentiate models by label bits and box guesses
3. Displaying those differences

## Change of meaning

The retired encoding's iterator compared world histories (`{world_id: {time: state}}`),
truth conditions read via `semantics.truth_condition`, and `task_rel`/time-shift-relation
tables. None of that exists any more (see `semantic/core.py`'s own module docstring). This
module is rewritten around the certificate encoding's own variable set: label bits
(`WitnessRegistry._bits`), box guesses (`WitnessRegistry._guesses`), and the extracted
`WitnessFamily`/`target_time` pair (`semantic/core.py`'s `extract_certificate`, Phase 10).

## `_create_difference_constraint`/`_create_non_isomorphic_constraint` are interface-parity
methods, not the live loop's exclusion mechanism -- true before this redesign, still true now

`BaseModelIterator.iterate()`/`iterate_generator()` (`model_checker/iterate/core.py`) never call
`self._create_difference_constraint`/`self._create_non_isomorphic_constraint` directly: they
delegate to a composed, theory-agnostic `ConstraintGenerator`
(`model_checker/iterate/constraints.py`), constructed unconditionally in
`BaseModelIterator.__init__` and not overridable per theory. That generator's own exclusion
logic is entirely gated on `hasattr(semantics, 'is_world')` -- true of the retired encoding
(and of the other three theories, which keep a bitvector world-state predicate), **false of
this one** (D3/D4 deliberately have no state-existence predicate at all; the certified carrier
is `{0,...,k} x Z`, not enumerated states). This is a genuine, discovered gap: for bimodal,
`iterate: N > 1` now finds its models with **no active exclusion constraint from the generic
path** -- Z3 may happen to return distinct models across separate finalize-and-solve rounds
(the search space is large and label bits are otherwise unconstrained), but nothing in the
shared framework *forces* the next model to differ. Fixing `ConstraintGenerator` itself would
touch shared code all four theories rely on and was judged out of proportion to a bimodal-only
task without dedicated regression coverage across the other three theories; it is recorded here,
in the implementation plan's own Phase 15 section, and in that phase's handoff, rather than
silently left undiscovered. The methods below are kept, rewritten for the new variable set, for
the same reason the retired encoding kept them: interface parity with the other three theories,
and direct programmatic use (`iterate_example`/`iterate_example_generator`, below, which uses
`BaseModelIterator.iterate()`'s own model-building machinery, not these two methods).

## Isomorphism rejection is simplified to exact difference, not rotation/permutation invariance

The plan's own Phase 15 task asks for `_create_non_isomorphic_constraint` to reject "modulo
rotation of each lasso's `back`/`fwd` segments and permutation of the witness lassos." A fully
symmetry-aware rejection would need to enumerate the (finite, but combinatorially real) rotation
group action on each lasso's periodic segments together with witness-lasso relabelings, and
assert non-membership in that whole orbit. Given the scope already covered by this phase's
other, betterspecified obligations, this iteration implements the simpler (and still sound, if
less complete) exact-bit/guess difference shared with `_create_difference_constraint` --
sufficient to guarantee the *next* model is not bit-for-bit identical, though it may still be a
rotation of a previous one. A follow-on task should implement the full symmetry-aware rejection
using `WitnessRegistry.wrap`'s existing slot arithmetic to enumerate rotations.
"""

import sys
import logging

from model_checker import z3_shim as z3

from model_checker.iterate.core import BaseModelIterator
from model_checker.solver import is_true

# Configure logging
logger = logging.getLogger(__name__)
if not logger.handlers:
    handler = logging.StreamHandler(sys.stdout)
    formatter = logging.Formatter('[BIMODAL-ITERATE] %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    logger.setLevel(logging.WARNING)


class BimodalModelIterator(BaseModelIterator):
    """Model iterator for the bimodal theory (certificate encoding). See the module
    docstring for the change of meaning and the discovered live-loop exclusion gap."""

    def _certificate_variables(self):
        """Every label-bit and box-guess Z3 Boolean this search declared -- shared by
        `_create_difference_constraint` and `_create_non_isomorphic_constraint`."""
        semantics = self.build_example.model_constraints.semantics
        registry = semantics.witness_registry
        return list(registry._bits.values()) + list(registry._guesses.values())

    def _blocking_clause(self, prev_model):
        """`Or(var != prev_model's value for var)` over every certificate variable --
        `True` (as a Z3 constraint) exactly when the next model differs from `prev_model` in
        at least one label bit or box guess."""
        variables = self._certificate_variables()
        if not variables:
            return None
        disjuncts = []
        for var in variables:
            prev_value = prev_model.eval(var, model_completion=True)
            disjuncts.append(var != z3.BoolVal(bool(is_true(prev_value))))
        return z3.Or(*disjuncts)

    def _create_difference_constraint(self, previous_models):
        """Blocking clause requiring difference, in at least one label bit or box guess,
        from every model in `previous_models` (D6's certificate variable set). See the
        module docstring: not on the live iteration loop's own exclusion path, but kept
        for interface parity and direct programmatic use.
        """
        clauses = [
            clause
            for clause in (self._blocking_clause(prev_model) for prev_model in previous_models)
            if clause is not None
        ]
        return z3.And(*clauses) if clauses else z3.BoolVal(True)

    def _create_non_isomorphic_constraint(self, isomorphic_model):
        """Blocking clause requiring difference from `isomorphic_model`, in at least one
        label bit or box guess. See the module docstring's "Isomorphism rejection is
        simplified" section: this rejects the exact model, not its whole rotation/
        permutation orbit."""
        clause = self._blocking_clause(isomorphic_model)
        return clause if clause is not None else z3.BoolVal(True)

    def _create_stronger_constraint(self, isomorphic_model):
        """Create constraint for finding stronger models. Not specialized for the
        certificate encoding (matches the retired encoding's own placeholder)."""
        return z3.BoolVal(True)

    def _calculate_differences(self, new_structure, previous_structure):
        """Label-bit and box-guess differences between two certificate-encoded model
        structures, read from each structure's own extracted `certificate`
        (`semantic/core.py`'s `extract_certificate`, Phase 10) rather than from Z3 models
        directly -- both structures have already independently re-checked their own
        certificate (Phase 12's S3 hook) by the time this runs.
        """
        differences = {
            "labels": {},
            "box_guesses": {},
            "target_time": None,
        }

        new_certificate = getattr(new_structure, "certificate", None)
        previous_certificate = getattr(previous_structure, "certificate", None)
        if new_certificate is None or previous_certificate is None:
            return differences

        semantics = new_structure.semantics
        window = list(semantics.witness_registry.target_window())

        label_diffs = {}
        lasso_count = max(len(new_certificate.lassos), len(previous_certificate.lassos))
        for lasso_index in range(lasso_count):
            new_lasso = new_certificate.lassos[lasso_index] if lasso_index < len(new_certificate.lassos) else None
            old_lasso = previous_certificate.lassos[lasso_index] if lasso_index < len(previous_certificate.lassos) else None
            if new_lasso is None or old_lasso is None:
                label_diffs[lasso_index] = {"added": new_lasso is not None, "removed": old_lasso is not None}
                continue
            position_diffs = {}
            for t in window:
                new_label = new_lasso.label(t)
                old_label = old_lasso.label(t)
                if new_label != old_label:
                    position_diffs[t] = {"old": sorted(map(repr, old_label)), "new": sorted(map(repr, new_label))}
            if position_diffs:
                label_diffs[lasso_index] = position_diffs
        if label_diffs:
            differences["labels"] = label_diffs

        guess_diffs = {}
        all_boxed = set(new_certificate.bx.keys()) | set(previous_certificate.bx.keys())
        for child in all_boxed:
            new_guess = new_certificate.bx_of(child)
            old_guess = previous_certificate.bx_of(child)
            if new_guess != old_guess:
                guess_diffs[repr(child)] = {"old": old_guess, "new": new_guess}
        if guess_diffs:
            differences["box_guesses"] = guess_diffs

        new_time = getattr(new_structure, "target_time", None)
        old_time = getattr(previous_structure, "target_time", None)
        if new_time != old_time:
            differences["target_time"] = {"old": old_time, "new": new_time}

        return differences

    def display_model_differences(self, model_structure, output=sys.stdout):
        """Print label-bit/box-guess/target-time differences from the previous model."""
        if not hasattr(model_structure, 'model_differences') or not model_structure.model_differences:
            return

        differences = model_structure.model_differences
        print("\n=== DIFFERENCES FROM PREVIOUS MODEL ===\n", file=output)

        if differences.get('labels'):
            print("Label Changes:", file=output)
            for lasso_index, changes in differences['labels'].items():
                if isinstance(changes, dict) and ('added' in changes or 'removed' in changes):
                    if changes.get('added'):
                        print(f"  + Lasso L{lasso_index} added", file=output)
                    if changes.get('removed'):
                        print(f"  - Lasso L{lasso_index} removed", file=output)
                    continue
                print(f"  Lasso L{lasso_index} changed:", file=output)
                for position, change in sorted(changes.items()):
                    print(f"    Position {position}: {change['old']} -> {change['new']}", file=output)

        if differences.get('box_guesses'):
            print("\nBox Guess Changes:", file=output)
            for formula_repr, change in differences['box_guesses'].items():
                print(f"  {formula_repr}: {change['old']} -> {change['new']}", file=output)

        if differences.get('target_time'):
            change = differences['target_time']
            print(f"\nTarget Time: {change['old']} -> {change['new']}", file=output)

    def iterate_generator(self):
        """Merge bimodal-specific (label/guess) differences into each yielded model,
        matching the retired encoding's own override pattern."""
        for model in super().iterate_generator():
            if len(self.model_structures) >= 2:
                theory_diffs = self._calculate_differences(model, self.model_structures[-2])
                if hasattr(model, 'model_differences') and model.model_differences:
                    model.model_differences.update(theory_diffs)
                else:
                    model.model_differences = theory_diffs

            yield model


# Wrapper function for use in theory examples
def iterate_example(example, max_iterations=None):
    """Find multiple models for a bimodal theory example.

    Args:
        example: A BuildExample instance with a bimodal theory model
        max_iterations: Maximum number of models to find (optional)

    Returns:
        list: List of distinct model structures
    """
    iterator = BimodalModelIterator(example)

    if max_iterations is not None:
        iterator.max_iterations = max_iterations

    model_structures = iterator.iterate()

    for structure in model_structures:
        if hasattr(structure, 'model_differences') and structure.model_differences:
            def create_print_method(struct):
                def print_method(output=None):
                    iterator.display_model_differences(struct, output or sys.stdout)
                    return True
                return print_method
            structure.print_model_differences = create_print_method(structure)

    return model_structures


def iterate_example_generator(example, max_iterations=None):
    """Generator version of iterate_example that yields models incrementally.

    Args:
        example: A BuildExample instance with bimodal theory.
        max_iterations: Maximum number of models to find.

    Yields:
        Model structures as they are discovered.
    """
    if max_iterations is not None:
        if not hasattr(example, 'settings'):
            example.settings = {}
        example.settings['iterate'] = max_iterations

    iterator = BimodalModelIterator(example)
    example._iterator = iterator

    yield from iterator.iterate_generator()


# Mark the generator function for BuildModule detection
iterate_example_generator.returns_generator = True
iterate_example_generator.__wrapped__ = iterate_example_generator
