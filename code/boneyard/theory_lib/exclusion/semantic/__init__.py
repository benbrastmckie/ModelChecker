"""
Witness semantics module.

This package implements witness-based negation semantics by breaking up
the original monolithic semantic.py file into focused modules while
preserving all functionality and backward compatibility.
"""

# Import all classes from their respective modules
from .core import WitnessSemantics
from .constraints import WitnessConstraintGenerator
from .model import WitnessAwareModel
from .registry import WitnessRegistry

# For now, import the remaining large classes directly from the original semantic.py
# These can be extracted to separate modules in a future refactoring phase
import sys
import time
from typing import Dict, List, Optional, Set, Tuple

import z3

from model_checker import syntactic
from model_checker.models.constraints import ModelConstraints
from model_checker.models.proposition import PropositionDefaults
from model_checker.models.structure import ModelDefaults
from model_checker.utils import (
    Exists,
    ForAll,
    bitvec_to_substates,
    int_to_binary,
    pretty_set_print,
)

from ...logos.semantic import LogosSemantics


# Import remaining classes from original semantic.py temporarily
# TODO: These should be extracted to separate modules in Phase 2
class WitnessModelAdapter(ModelDefaults):
    """
    Adapter to make witness semantics compatible with ModelChecker.
    """

    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 3,
        'possible': False,
        'contingent': False,
        'non_empty': False,
        'non_null': False,
        'disjoint': False,
        'fusion_closure': False,
        'iterate': 1,
        'max_time': 1,
        'expectation': None,
    }

    # No additional general settings needed - uses base class defaults

    def __init__(self, settings):
        super().__init__(settings)
        self.semantics = WitnessSemantics(settings)
        self.settings = settings

    def build_model(self, eval_point):
        """Build model using witness predicate approach."""
        return self.semantics.build_model(eval_point)

    def extended_verify(self, state, sentence, eval_point):
        """Delegate to semantics."""
        return self.semantics.extended_verify(state, sentence, eval_point)

    def extended_compute_verifiers(self, sentence, model, eval_point):
        """Delegate to semantics."""
        return self.semantics.extended_compute_verifiers(sentence, model, eval_point)


class WitnessStructure(ModelDefaults):
    """Extended model structure for witness predicate semantics with full printing."""

    def __init__(self, model_constraints, combined_settings):
        """Initialize with proper constraint checking."""
        if not isinstance(model_constraints, ModelConstraints):
            raise TypeError(
                f"Expected model_constraints to be a ModelConstraints object, "
                f"got {type(model_constraints)}."
            )

        super().__init__(model_constraints, combined_settings)

        # Only evaluate if we have a valid model
        if self.z3_model_status and self.z3_model is not None:
            self._update_model_structure(self.z3_model)

            # Create propositions for sentences
            self.interpret(self.premises)
            self.interpret(self.conclusions)

    def _update_model_structure(self, z3_model):
        """Update model structure from Z3 model, including semantic relations."""
        evaluate = z3_model.evaluate

        # Don't try to re-evaluate main_world if it's already been evaluated by iterator
        if not hasattr(self, 'z3_main_world') or self.z3_main_world is None:
            self.main_world = self.main_point["world"]
            self.main_point["world"] = z3_model.eval(self.main_world, model_completion=True)

        # Update possible states with proper Z3 boolean handling
        possible_states = []
        for state in self.all_states:
            result = evaluate(self.semantics.possible(state))
            is_possible = z3.is_true(result)
            if is_possible:
                possible_states.append(state)

        # Store the possible states
        self.z3_possible_states = possible_states

        # The null state should always be possible
        if 0 not in self.z3_possible_states:
            self.z3_possible_states.append(0)

        # Update world states with proper Z3 boolean handling
        self.z3_world_states = [
            state for state in self.z3_possible_states
            if z3.is_true(evaluate(self.semantics.is_world(state)))
        ]

        # Update impossible states
        self.z3_impossible_states = [
            i for i in range(len(self.all_states))
            if i not in self.z3_possible_states
        ]

        # Update negation data
        self.z3_excludes = [
            (bit_x, bit_y)
            for bit_x in self.all_states
            for bit_y in self.all_states
            if z3.is_true(evaluate(self.semantics.excludes(bit_x, bit_y)))
        ]

        # Update conflicts data
        self.z3_conflicts = [
            (bit_x, bit_y)
            for bit_x in self.all_states
            for bit_y in self.all_states
            if z3.is_true(evaluate(self.semantics.conflicts(bit_x, bit_y)))
        ]

        # Update coherence data
        self.z3_coheres = [
            (bit_x, bit_y)
            for bit_x in self.all_states
            for bit_y in self.all_states
            if z3.is_true(evaluate(self.semantics.coheres(bit_x, bit_y)))
        ]

    def true_at(self, sentence, eval_point):
        """Delegate to semantics for truth evaluation."""
        return self.semantics.true_at(sentence, eval_point)

    def extended_verify(self, state, sentence, eval_point):
        """Delegate to semantics for extended verification."""
        return self.semantics.extended_verify(state, sentence, eval_point)

    def _evaluate_z3_boolean(self, z3_model, expression):
        """Safely evaluate a Z3 boolean expression to a Python boolean.

        This method handles the case where Z3 returns symbolic expressions
        instead of concrete boolean values, which can cause
        "Symbolic expressions cannot be cast to concrete Boolean values" errors.
        """
        try:
            result = z3_model.evaluate(expression, model_completion=True)

            if z3.is_bool(result):
                if z3.is_true(result):
                    return True
                elif z3.is_false(result):
                    return False

            simplified = z3.simplify(result)

            if z3.is_true(simplified):
                return True
            elif z3.is_false(simplified):
                return False

            if str(simplified) == "True":
                return True
            elif str(simplified) == "False":
                return False

            try:
                return z3.simplify(simplified == z3.BoolVal(True)) == z3.BoolVal(True)
            except Exception:
                # logger.warning(f"Could not evaluate Z3 boolean expression: {expression}, assuming False")
                return False

        except Exception as e:
            # logger.warning(f"Error evaluating Z3 boolean expression {expression}: {e}, assuming False")
            return False

    def find_verifying_states(self, sentence, eval_point):
        """Find states that verify the sentence at evaluation point."""
        result = set()
        for state in self.all_states:
            constraint = self.extended_verify(state, sentence, eval_point)
            if self._evaluate_z3_boolean(self.z3_model, constraint):
                result.add(state)
        return result

    def interpret_verify(self, atom):
        """Interpret the verify relation for an atom."""
        result = set()
        for state in self.all_states:
            constraint = self.semantics.verify(state, atom)
            if self._evaluate_z3_boolean(self.z3_model, constraint):
                result.add(state)
        return result

    def interpret_excludes(self):
        """Interpret the excludes relation."""
        result = {}
        for state_x in self.all_states:
            result[state_x] = set()
            for state_y in self.all_states:
                constraint = self.semantics.excludes(state_x, state_y)
                if self._evaluate_z3_boolean(self.z3_model, constraint):
                    result[state_x].add(state_y)
        return result

    def initialize_from_z3_model(self, z3_model):
        """Initialize exclusion-specific attributes from Z3 model.

        This method is called by the iterator when creating new model structures.
        """
        # Store the Z3 model first
        self.z3_model = z3_model

        # Call the update method that sets z3_excludes and other attributes
        self._update_model_structure(z3_model)

    def print_to(self, default_settings, example_name, theory_name, print_constraints=None, output=sys.__stdout__):
        """Print the model details to the specified output stream."""
        if print_constraints is None:
            print_constraints = self.settings.get("print_constraints", False)

        # Check if we actually timed out
        actual_timeout = hasattr(self, 'z3_model_runtime') and self.z3_model_runtime is not None and self.z3_model_runtime >= self.max_time

        # Only show timeout if we really timed out and didn't find a model
        if actual_timeout and (not hasattr(self, 'z3_model') or self.z3_model is None):
            print(f"\nTIMEOUT: Model search exceeded maximum time of {self.max_time} seconds", file=output)
            print(f"No model for example {example_name} found before timeout.", file=output)
            print(f"Try increasing max_time > {self.max_time}.\n", file=output)

        # Print model information
        self.print_all(self.settings, example_name, theory_name, output)

        # Print constraints if requested
        if print_constraints and self.unsat_core is not None:
            self.print_grouped_constraints(output)

    def print_all(self, default_settings, example_name, theory_name, output=sys.__stdout__):
        """Print comprehensive model information including states and evaluation."""
        model_status = self.z3_model_status
        self.print_info(model_status, self.settings, example_name, theory_name, output)
        if model_status:
            self.print_states(output)
            self.print_negation(output)
            self.print_evaluation(output)
            self.print_input_sentences(output)
            self.print_model(output)
            if output is sys.__stdout__:
                total_time = round(time.time() - self.start_time, 4)
                print(f"Total Run Time: {total_time} seconds\n", file=output)
            # Always print closing separator for countermodels
            print(f"\n{'='*40}", file=output)
            return

    def print_states(self, output=sys.__stdout__):
        """Print all fusions of atomic states in the model."""

        def binary_bitvector(bit):
            return (
                bit.sexpr()
                if self.N % 4 != 0
                else int_to_binary(int(bit.sexpr()[2:], 16), self.N)
            )

        def format_state(bin_rep, state, color, label=""):
            """Helper function to format and print a state."""
            label_str = f" ({label})" if label else ""
            use_colors = output is sys.__stdout__
            if use_colors:
                print(f"  {self.WHITE}{bin_rep} = {color}{state}{label_str}{self.RESET}", file=output)
            else:
                print(f"  {bin_rep} = {state}{label_str}", file=output)

        # Define colors (if not already defined)
        if not hasattr(self, 'COLORS'):
            self.COLORS = {
                "default": "\033[37m",  # WHITE
                "world": "\033[34m",    # BLUE
                "possible": "\033[36m", # CYAN
                "impossible": "\033[35m", # MAGENTA
                "initial": "\033[33m",  # YELLOW
            }
        self.WHITE = self.COLORS["default"]
        self.RESET = "\033[0m"

        # Print formatted state space
        print("State Space", file=output)
        for bit in self.all_states:
            state = bitvec_to_substates(bit, self.N)
            bin_rep = binary_bitvector(bit)
            if bit == 0:
                format_state(bin_rep, state, self.COLORS["initial"])
            elif bit in self.z3_world_states:
                format_state(bin_rep, state, self.COLORS["world"], "world")
            elif bit in self.z3_possible_states:
                format_state(bin_rep, state, self.COLORS["possible"])
            elif self.settings['print_impossible']:
                format_state(bin_rep, state, self.COLORS["impossible"], "impossible")

    def print_negation(self, output=sys.__stdout__):
        """Print conflicts, coherence, negation relationships, and witness functions."""

        # Set up colors
        use_colors = output is sys.__stdout__
        WHITE = self.COLORS["default"] if use_colors else ""
        RESET = self.RESET if use_colors else ""
        WORLD_COLOR = self.COLORS["world"] if use_colors else ""
        POSSIBLE_COLOR = self.COLORS["possible"] if use_colors else ""
        IMPOSSIBLE_COLOR = self.COLORS["impossible"] if use_colors else ""

        def get_state_color(bit):
            if bit in self.z3_world_states:
                return WORLD_COLOR
            elif bit in self.z3_possible_states:
                return POSSIBLE_COLOR
            else:
                return IMPOSSIBLE_COLOR

        def should_include_state(bit):
            # Check if we should include this state based on print_impossible setting
            # Always include the null state (bit 0)
            return (bit == 0 or
                   bit in self.z3_possible_states or
                   bit in self.z3_world_states or
                   self.settings['print_impossible'])

        # Filter and print conflicts
        z3_conflicts = getattr(self, 'z3_conflicts', [])
        filtered_conflicts = [(x, y) for x, y in z3_conflicts if should_include_state(x) and should_include_state(y)]
        if filtered_conflicts:
            print("\nConflicts", file=output)
            for bit_x, bit_y in filtered_conflicts:
                color_x = get_state_color(bit_x)
                color_y = get_state_color(bit_y)
                x_state = bitvec_to_substates(bit_x, self.N)
                y_state = bitvec_to_substates(bit_y, self.N)
                print(f"  {color_x}{x_state}{RESET} conflicts with {color_y}{y_state}{RESET}", file=output)

        # Filter and print coherence
        z3_coheres = getattr(self, 'z3_coheres', [])
        filtered_coheres = [(x, y) for x, y in z3_coheres if should_include_state(x) and should_include_state(y)]
        if filtered_coheres:
            print("\nCoherence", file=output)
            for bit_x, bit_y in filtered_coheres:
                color_x = get_state_color(bit_x)
                color_y = get_state_color(bit_y)
                x_state = bitvec_to_substates(bit_x, self.N)
                y_state = bitvec_to_substates(bit_y, self.N)
                print(f"  {color_x}{x_state}{RESET} coheres with {color_y}{y_state}{RESET}", file=output)

        # Filter and print negations
        filtered_excludes = [(x, y) for x, y in self.z3_excludes if should_include_state(x) and should_include_state(y)]
        if filtered_excludes:
            print("\nUnilateral Exclusion", file=output)
            for bit_x, bit_y in filtered_excludes:
                state_x = bitvec_to_substates(bit_x, self.N)
                state_y = bitvec_to_substates(bit_y, self.N)
                color_x = get_state_color(bit_x)
                color_y = get_state_color(bit_y)
                print(f"  {color_x}{state_x}{RESET} excludes {color_y}{state_y}{RESET}", file=output)

        # Print witness predicate functions
        self.print_witness_functions(output)

    def print_witness_functions(self, output=sys.__stdout__):
        """Print witness predicate and other functions from the model."""

        if not self.z3_model:
            return

        # Set up colors
        use_colors = output is sys.__stdout__
        WHITE = self.WHITE if use_colors else ""
        RESET = self.RESET if use_colors else ""
        WORLD_COLOR = self.COLORS["world"] if use_colors else ""
        POSSIBLE_COLOR = self.COLORS["possible"] if use_colors else ""
        IMPOSSIBLE_COLOR = self.COLORS["impossible"] if use_colors else ""

        def get_state_color(bit):
            if bit in self.z3_world_states:
                return WORLD_COLOR
            elif bit in self.z3_possible_states:
                return POSSIBLE_COLOR
            else:
                return IMPOSSIBLE_COLOR

        def should_include_state(bit):
            # Check if we should include this state based on print_impossible setting
            return bit in self.z3_possible_states or bit in self.z3_world_states or self.settings['print_impossible']

        # Find all witness predicate and Skolem functions in the model
        witness_funcs = []
        h_funcs = []
        y_funcs = []
        sk_funcs = []

        for decl in self.z3_model.decls():
            name = decl.name()
            if '_h' in name or '_y' in name:
                witness_funcs.append(decl)
            elif name.startswith('h_sk_'):
                h_funcs.append(decl)
            elif name.startswith('y_sk_'):
                sk_funcs.append(decl)

        # Combine all function types for display
        all_funcs = witness_funcs + h_funcs + sk_funcs

        if not all_funcs:
            # Don't print anything if no functions found
            return

        print("\nFunctions", file=output)

        # For each function, evaluate it for all states
        for func in all_funcs:
            # Create argument for the function
            arg = z3.BitVec("func_arg", self.N)
            func_app = func(arg)

            # Try to evaluate for each state
            for state in self.all_states:
                # Skip impossible states if print_impossible is False
                if not should_include_state(state):
                    continue

                try:
                    # Get the corresponding output value
                    result = self.z3_model.evaluate(z3.substitute(func_app, (arg, state)))

                    # Skip if result is not a possible state and print_impossible is False
                    if z3.is_bv_value(result) and not should_include_state(result.as_long()):
                        continue

                    # Format the output
                    input_state = bitvec_to_substates(state, self.N)
                    if z3.is_bv_value(result):
                        output_state = bitvec_to_substates(result.as_long(), self.N)
                        out_color = get_state_color(result.as_long())
                    else:
                        output_state = str(result)
                        out_color = WHITE

                    # Apply colors based on state type
                    in_color = get_state_color(state)

                    # Print in the required format with colors
                    print(f"  {func.name()}: {in_color}{input_state}{RESET} → {out_color}{output_state}{RESET}", file=output)
                except Exception:
                    # Skip if we can't evaluate this input
                    pass

    def print_evaluation(self, output=sys.__stdout__):
        """Print the evaluation world and all sentence letters that are true/false in that world."""

        BLUE = ""
        RESET = ""
        main_world = self.main_point["world"]
        if output is sys.__stdout__:
            BLUE = "\033[34m"
            RESET = "\033[0m"
        print(
            f"\nThe evaluation world is: {BLUE}{bitvec_to_substates(main_world, self.N)}{RESET}\n",
            file=output,
        )

    # Additional methods would be added here for full compatibility
    # For now, this subset covers the essential functionality


class WitnessProposition(PropositionDefaults):
    """Proposition class for witness predicate semantics."""

    def __init__(self, sentence, model_structure):
        super().__init__(sentence, model_structure)
        self.z3_model = model_structure.z3_model
        self.verifiers = self.find_proposition()

    def proposition_constraints(model_constraints, sentence_letter):
        """Generate constraints for atomic propositions.

        This is called as a class method (without an instance) from ModelConstraints.
        The first argument is the ModelConstraints instance, not self.

        Args:
            model_constraints: The ModelConstraints instance containing semantics and settings
            sentence_letter: The atomic sentence letter to generate constraints for

        Returns:
            list: List of Z3 constraints for the sentence letter
        """
        return model_constraints.semantics.atom_constraints(
            sentence_letter,
            model_constraints.sentence_letters,
            model_constraints.settings
        )

    def find_proposition(self):
        """Find the set of verifiers for this sentence."""
        result = set()
        semantics = self.model_structure.semantics
        eval_point = semantics.main_point

        # Check each state to see if it verifies the sentence
        for state in range(2**semantics.N):
            constraint = semantics.extended_verify(state, self.sentence, eval_point)
            # Use the model structure's _evaluate_z3_boolean method if available
            if hasattr(self.model_structure, '_evaluate_z3_boolean'):
                if self.model_structure._evaluate_z3_boolean(self.z3_model, constraint):
                    result.add(state)
            else:
                if z3.is_true(self.z3_model.evaluate(constraint)):
                    result.add(state)
        return result

    def truth_value_at(self, eval_point):
        """Evaluate truth value at a point."""
        return self.model_structure.semantics.true_at(self.sentence, eval_point)

    def print_method(self, eval_point, indent_num, use_colors):
        """Print the proposition."""
        self.print_proposition(eval_point, indent_num, use_colors)

    def __repr__(self):
        """Return pretty-printed representation of verifiers."""

        N = self.model_structure.semantics.N
        possible = self.model_structure.semantics.possible
        z3_model = self.model_structure.z3_model
        # Use the model structure's _evaluate_z3_boolean method if available
        if hasattr(self.model_structure, '_evaluate_z3_boolean'):
            ver_states = {
                bitvec_to_substates(bit, N)
                for bit in self.verifiers
                if self.model_structure._evaluate_z3_boolean(z3_model, possible(bit)) or self.settings.get('print_impossible', False)
            }
        else:
            ver_states = {
                bitvec_to_substates(bit, N)
                for bit in self.verifiers
                if z3.is_true(z3_model.evaluate(possible(bit))) or self.settings.get('print_impossible', False)
            }
        return pretty_set_print(ver_states)

    def print_proposition(self, eval_point, indent_num, use_colors):
        """Print the proposition with its truth value at the evaluation point."""

        N = self.model_structure.semantics.N
        z3_formula = self.truth_value_at(eval_point)
        # Use the model structure's _evaluate_z3_boolean method if available
        if hasattr(self.model_structure, '_evaluate_z3_boolean'):
            truth_value = self.model_structure._evaluate_z3_boolean(self.model_structure.z3_model, z3_formula)
        else:
            truth_value = z3.is_true(self.model_structure.z3_model.evaluate(z3_formula))
        world_state = bitvec_to_substates(eval_point["world"], N)
        RESET, FULL, PART = self.set_colors(self.name, indent_num, truth_value, world_state, use_colors)
        print(
            f"{'  ' * indent_num}{FULL}|{self.name}| = {self}{RESET}"
            f"  {PART}({truth_value} in {world_state}){RESET}"
        )


# Re-export all classes for backward compatibility
__all__ = [
    'WitnessSemantics',
    'WitnessAwareModel',
    'WitnessRegistry',
    'WitnessConstraintGenerator',
    'WitnessModelAdapter',
    'WitnessStructure',
    'WitnessProposition',
]