"""Bimodal theory specific model iteration implementation.

This module provides the BimodalModelIterator implementation which handles:
1. Detecting differences between models using bimodal theory semantics
2. Creating constraints to differentiate models with bimodal theory primitives
3. Checking model isomorphism for bimodal theory models

Ported to the current iterate_example_generator convention (see
imposition/iterate.py) from the version restored via git history; the
original was removed during an unrelated dependency-cutting pass, not
because the semantics were wrong -- see bimodal/docs/ITERATE.md.
"""

import sys
import logging

from model_checker import z3_shim as z3

from model_checker.iterate.core import BaseModelIterator

# Configure logging
logger = logging.getLogger(__name__)
if not logger.handlers:
    handler = logging.StreamHandler(sys.stdout)
    formatter = logging.Formatter('[BIMODAL-ITERATE] %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    logger.setLevel(logging.WARNING)


class BimodalModelIterator(BaseModelIterator):
    """Model iterator for the bimodal theory.

    This class extends BaseModelIterator with bimodal theory-specific
    implementations of the abstract methods required for model iteration.
    It provides specialized difference detection and visualization for
    bimodal theory models.

    The bimodal theory uses:
    - World histories (arrays mapping time -> world state)
    - World states represented as bit vectors
    - Truth conditions for atomic propositions
    - Task transitions between consecutive world states
    - Modal accessibility across different world histories
    """

    def _calculate_differences(self, new_structure, previous_structure):
        """Calculate differences between two bimodal theory model structures.

        For bimodal theory, this focuses on:
        - Changes in world histories (time-state mappings)
        - Changes in truth conditions for sentence letters
        - Changes in task transitions between world states
        - Changes in time intervals for worlds
        - Changes in time-shift relations between worlds

        Args:
            new_structure: The new model structure
            previous_structure: The previous model structure

        Returns:
            dict: Structured differences between the models
        """
        # BimodalStructure does not currently define detect_model_differences;
        # guard rather than assume, so a future theory-owned implementation is
        # picked up automatically without requiring a change here.
        if hasattr(new_structure, 'detect_model_differences'):
            try:
                differences = new_structure.detect_model_differences(previous_structure)
                if differences:
                    return differences
            except Exception:
                pass

        # Fall back to our own implementation
        return self._calculate_bimodal_differences(new_structure, previous_structure)

    def _calculate_bimodal_differences(self, new_structure, previous_structure):
        """Bimodal theory specific implementation of difference detection.

        This is more sophisticated than the base difference detection since
        it understands bimodal theory semantics like world histories, times,
        and task transitions.

        Args:
            new_structure: The new model structure
            previous_structure: The previous model structure

        Returns:
            dict: Dictionary of differences with bimodal theory semantics
        """
        # Get Z3 models
        new_model = new_structure.z3_model
        previous_model = previous_structure.z3_model

        # Initialize bimodal theory-specific differences structure
        differences = {
            "world_histories": {},
            "truth_conditions": {},
            "task_relations": {},
            "time_intervals": {},
            "time_shifts": {},
        }

        # 1. Compare world histories (time-state mappings)
        old_histories = getattr(previous_structure, "world_histories", {})
        new_histories = getattr(new_structure, "world_histories", {})

        all_world_ids = set(old_histories.keys()).union(set(new_histories.keys()))

        for world_id in all_world_ids:
            # If the world exists in both models
            if world_id in old_histories and world_id in new_histories:
                old_history = old_histories[world_id]
                new_history = new_histories[world_id]

                # Find added/removed/changed time points
                all_times = set(old_history.keys()).union(set(new_history.keys()))

                history_diffs = {}
                for time in all_times:
                    if time in old_history and time in new_history:
                        old_state = old_history[time]
                        new_state = new_history[time]
                        if old_state != new_state:
                            history_diffs[time] = {"old": old_state, "new": new_state}
                    elif time in new_history:
                        history_diffs[time] = {"old": None, "new": new_history[time]}
                    elif time in old_history:
                        history_diffs[time] = {"old": old_history[time], "new": None}

                if history_diffs:
                    differences["world_histories"][world_id] = history_diffs

            elif world_id in new_histories:
                differences["world_histories"][world_id] = {
                    "added": True,
                    "history": new_histories[world_id],
                }

            elif world_id in old_histories:
                differences["world_histories"][world_id] = {
                    "removed": True,
                    "history": old_histories[world_id],
                }

        # 2. Compare truth conditions for sentence letters
        semantics = new_structure.semantics

        # Get all world states (unique across all world histories)
        all_states = set()
        for history in new_histories.values():
            all_states.update(set(history.values()))
        for history in old_histories.values():
            all_states.update(set(history.values()))

        for letter in new_structure.sentence_letters:
            letter_diffs = {}

            for state in all_states:
                try:
                    state_bitvec = state
                    if isinstance(state, str) and not state.startswith("<"):
                        if hasattr(semantics, 'state_str_to_bitvec'):
                            state_bitvec = semantics.state_str_to_bitvec(state)

                    old_value = False
                    new_value = False

                    try:
                        old_value = bool(previous_model.eval(
                            semantics.truth_condition(state_bitvec, letter),
                            model_completion=True
                        ))
                    except Exception:
                        pass

                    try:
                        new_value = bool(new_model.eval(
                            semantics.truth_condition(state_bitvec, letter),
                            model_completion=True
                        ))
                    except Exception:
                        pass

                    if old_value != new_value:
                        letter_diffs[str(state)] = {"old": old_value, "new": new_value}
                except Exception:
                    # Skip problematic states
                    pass

            if letter_diffs:
                differences["truth_conditions"][str(letter)] = letter_diffs

        # 3. Compare task relations between world states with duration parameter
        # (ternary task_rel(state, duration, state))
        if hasattr(semantics, 'task_rel'):
            task_diffs = {}

            M = getattr(semantics, 'M', 2)
            duration_range = range(-M + 1, M)

            for state1 in all_states:
                for duration in duration_range:
                    for state2 in all_states:
                        try:
                            old_value = False
                            new_value = False

                            try:
                                old_value = bool(previous_model.eval(
                                    semantics.task_rel(state1, duration, state2),
                                    model_completion=True
                                ))
                            except Exception:
                                pass

                            try:
                                new_value = bool(new_model.eval(
                                    semantics.task_rel(state1, duration, state2),
                                    model_completion=True
                                ))
                            except Exception:
                                pass

                            if old_value != new_value:
                                key = f"{state1}--[{duration}]-->{state2}"
                                task_diffs[key] = {"old": old_value, "new": new_value}
                        except Exception:
                            pass

            if task_diffs:
                differences["task_relations"] = task_diffs

        # 4. Compare time intervals for worlds
        old_intervals = getattr(previous_structure.semantics, 'world_time_intervals', {})
        new_intervals = getattr(new_structure.semantics, 'world_time_intervals', {})

        interval_diffs = {}

        for world_id in all_world_ids:
            if world_id in old_intervals and world_id in new_intervals:
                old_interval = old_intervals[world_id]
                new_interval = new_intervals[world_id]
                if old_interval != new_interval:
                    interval_diffs[world_id] = {"old": old_interval, "new": new_interval}
            elif world_id in new_intervals:
                interval_diffs[world_id] = {"old": None, "new": new_intervals[world_id]}
            elif world_id in old_intervals:
                interval_diffs[world_id] = {"old": old_intervals[world_id], "new": None}

        if interval_diffs:
            differences["time_intervals"] = interval_diffs

        # 5. Compare time-shift relations between worlds
        old_shifts = getattr(previous_structure, 'time_shift_relations', {})
        new_shifts = getattr(new_structure, 'time_shift_relations', {})

        shift_diffs = {}

        for world_id in all_world_ids:
            if world_id in old_shifts and world_id in new_shifts:
                old_shifts_for_world = old_shifts[world_id]
                new_shifts_for_world = new_shifts[world_id]

                all_shifts = set(old_shifts_for_world.keys()).union(set(new_shifts_for_world.keys()))

                world_shift_diffs = {}
                for shift in all_shifts:
                    if shift in old_shifts_for_world and shift in new_shifts_for_world:
                        old_target = old_shifts_for_world[shift]
                        new_target = new_shifts_for_world[shift]
                        if old_target != new_target:
                            world_shift_diffs[shift] = {"old": old_target, "new": new_target}
                    elif shift in new_shifts_for_world:
                        world_shift_diffs[shift] = {"old": None, "new": new_shifts_for_world[shift]}
                    elif shift in old_shifts_for_world:
                        world_shift_diffs[shift] = {"old": old_shifts_for_world[shift], "new": None}

                if world_shift_diffs:
                    shift_diffs[world_id] = world_shift_diffs

            elif world_id in new_shifts:
                shift_diffs[world_id] = {"added": True, "shifts": new_shifts[world_id]}

            elif world_id in old_shifts:
                shift_diffs[world_id] = {"removed": True, "shifts": old_shifts[world_id]}

        if shift_diffs:
            differences["time_shifts"] = shift_diffs

        return differences

    def display_model_differences(self, model_structure, output=sys.stdout):
        """Format differences for display using bimodal theory semantics.

        Args:
            model_structure: The model structure with differences
            output: Output stream for writing output
        """
        if not hasattr(model_structure, 'model_differences') or not model_structure.model_differences:
            return

        differences = model_structure.model_differences

        print("\n=== DIFFERENCES FROM PREVIOUS MODEL ===\n", file=output)

        # 1. World history changes
        if differences.get('world_histories'):
            print("World History Changes:", file=output)

            for world_id, changes in differences['world_histories'].items():
                if isinstance(changes, dict) and changes.get('added', False):
                    print(f"  + World W_{world_id} added", file=output)
                    history = changes.get('history', {})
                    time_states = [f"({time}:{state})" for time, state in sorted(history.items())]
                    if time_states:
                        print(f"    History: {' -> '.join(time_states)}", file=output)

                elif isinstance(changes, dict) and changes.get('removed', False):
                    print(f"  - World W_{world_id} removed", file=output)

                else:
                    print(f"  World W_{world_id} changed:", file=output)
                    for time, change in sorted(changes.items()):
                        old_state = change.get('old')
                        new_state = change.get('new')
                        if old_state is None:
                            print(f"    + Time {time}: {new_state}", file=output)
                        elif new_state is None:
                            print(f"    - Time {time}: {old_state}", file=output)
                        else:
                            print(f"    Time {time}: {old_state} -> {new_state}", file=output)

        # 2. Truth condition changes
        if differences.get('truth_conditions'):
            print("\nTruth Condition Changes:", file=output)

            for letter, changes in differences['truth_conditions'].items():
                letter_name = letter
                if hasattr(model_structure, '_get_friendly_letter_name'):
                    try:
                        letter_name = model_structure._get_friendly_letter_name(letter)
                    except Exception:
                        pass

                print(f"  Letter {letter_name}:", file=output)
                for state, change in changes.items():
                    old_value = change.get('old', False)
                    new_value = change.get('new', False)
                    print(f"    State {state}: {old_value} -> {new_value}", file=output)

        # 3. Task relation changes (format: "state1--[duration]-->state2")
        if differences.get('task_relations'):
            print("\nTask Relation Changes:", file=output)

            for transition, change in differences['task_relations'].items():
                old_value = change.get('old', False)
                new_value = change.get('new', False)
                status = "added" if new_value and not old_value else "removed" if old_value and not new_value else "changed"
                print(f"  TaskRel {transition}: {status}", file=output)

        # 4. Time interval changes
        if differences.get('time_intervals'):
            print("\nTime Interval Changes:", file=output)

            for world_id, change in differences['time_intervals'].items():
                old_interval = change.get('old')
                new_interval = change.get('new')
                if old_interval is None:
                    print(f"  + World W_{world_id} interval: {new_interval}", file=output)
                elif new_interval is None:
                    print(f"  - World W_{world_id} interval: {old_interval}", file=output)
                else:
                    print(f"  World W_{world_id} interval: {old_interval} -> {new_interval}", file=output)

        # 5. Time shift relation changes
        if differences.get('time_shifts'):
            print("\nTime Shift Relation Changes:", file=output)

            for world_id, changes in differences['time_shifts'].items():
                if isinstance(changes, dict) and changes.get('added', False):
                    print(f"  + Time shifts for World W_{world_id} added", file=output)
                    shifts = changes.get('shifts', {})
                    for shift, target in sorted(shifts.items()):
                        print(f"    Shift {shift}: -> W_{target}", file=output)

                elif isinstance(changes, dict) and changes.get('removed', False):
                    print(f"  - Time shifts for World W_{world_id} removed", file=output)

                else:
                    print(f"  Time shifts for World W_{world_id} changed:", file=output)
                    for shift, change in sorted(changes.items()):
                        old_target = change.get('old')
                        new_target = change.get('new')
                        if old_target is None:
                            print(f"    + Shift {shift}: -> W_{new_target}", file=output)
                        elif new_target is None:
                            print(f"    - Shift {shift}: -> W_{old_target}", file=output)
                        else:
                            print(f"    Shift {shift}: W_{old_target} -> W_{new_target}", file=output)

    def _create_difference_constraint(self, previous_models):
        """Create constraints requiring difference from previous models.

        For bimodal theory, this varies world-history state assignments and
        atomic truth conditions across the theory's world-id/time domain.

        Note: the active iteration loop (iterate/iterator.py) always excludes
        previous models via the theory-agnostic ConstraintGenerator in
        iterate/constraints.py (keyed off `semantics.is_world`), not via this
        method. This override exists for interface parity with the other
        three theories (exclusion, imposition, logos) and for direct
        programmatic use.

        Args:
            previous_models: List of Z3 models found so far

        Returns:
            Z3 constraint requiring structural difference
        """
        constraints = []
        semantics = self.build_example.model_constraints.semantics
        times = range(-semantics.M + 1, semantics.M)
        # Bound the world-id domain: max_world_id = M * 2**(M*N) can be large,
        # while only a handful of ids are ever actually assigned as worlds.
        world_ids = range(min(getattr(semantics, 'max_world_id', 0), 16))

        for prev_model in previous_models:
            model_constraints = []

            # World-history constraints: different time-indexed state assignments
            for w in world_ids:
                for t in times:
                    prev_state = prev_model.eval(
                        z3.Select(semantics.world_function(w), t),
                        model_completion=True
                    )
                    model_constraints.append(
                        z3.Select(semantics.world_function(w), t) != prev_state
                    )

            # Truth value constraints
            syntax = self.build_example.example_syntax
            if hasattr(syntax, 'sentence_letters'):
                for letter_obj in syntax.sentence_letters:
                    if hasattr(letter_obj, 'sentence_letter'):
                        atom = letter_obj.sentence_letter
                        for w in world_ids:
                            prev_truth = prev_model.eval(
                                semantics.truth_condition(w, atom),
                                model_completion=True
                            )
                            model_constraints.append(
                                semantics.truth_condition(w, atom) != prev_truth
                            )

            if model_constraints:
                constraints.append(z3.Or(*model_constraints[:20]))  # Limit constraints

        return z3.And(*constraints) if constraints else z3.BoolVal(True)

    def _create_non_isomorphic_constraint(self, z3_model):
        """Create constraint preventing isomorphic models."""
        # For now, simple implementation (matches the other three theories'
        # placeholder; see _create_difference_constraint's note above).
        return z3.BoolVal(True)

    def _create_stronger_constraint(self, isomorphic_model):
        """Create constraint for finding stronger models."""
        # For now, simple implementation
        return z3.BoolVal(True)

    def iterate_generator(self):
        """Override to add theory-specific differences to bimodal theory models.

        This method extends the base iterator's generator to merge
        bimodal-specific differences (world histories, truth conditions,
        task relations, time intervals, time shifts) with the generic
        differences calculated by the base iterator.

        Yields:
            Model structures with both generic and theory-specific differences
        """
        for model in super().iterate_generator():
            if len(self.model_structures) >= 2:
                theory_diffs = self._calculate_bimodal_differences(
                    model, self.model_structures[-2]
                )
                if hasattr(model, 'model_differences') and model.model_differences:
                    model.model_differences.update(theory_diffs)
                else:
                    model.model_differences = theory_diffs

            yield model


# Wrapper function for use in theory examples
def iterate_example(example, max_iterations=None):
    """Find multiple models for a bimodal theory example.

    This function creates a BimodalModelIterator for the given example
    and uses it to find up to max_iterations distinct models.

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

    # Attach the display method to each structure so it can be called by
    # the module printing layer, matching the other three theories.
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

    This function provides a generator interface for finding multiple models,
    yielding each model as it's discovered rather than returning them all at
    once. This enables proper progress tracking and iteration reports, and is
    what builder/runner.py prefers when available (see runner.py's
    `hasattr(theory_module, 'iterate_example_generator')` check).

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

    # Store the iterator on the example for access to debug messages
    example._iterator = iterator

    yield from iterator.iterate_generator()


# Mark the generator function for BuildModule detection
iterate_example_generator.returns_generator = True
iterate_example_generator.__wrapped__ = iterate_example_generator
