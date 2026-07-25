"""
Witness-aware model implementation.

This module contains the WitnessAwareModel class that treats witness functions
as first-class predicates in the model, plus the theory's ModelDefaults-based model
classes (WitnessModelAdapter, WitnessStructure) -- moved here from semantic/__init__.py so
that __init__.py can be re-export-only per docs/THEORY_ARCHITECTURE.md's Theory Contract.
"""

# Standard library imports
import sys
import time
from typing import Any, Dict, Optional, Tuple, Union

# Third-party imports
from model_checker import z3_shim as z3

# Core imports
from model_checker.solver import is_true, is_false
from model_checker.models.constraints import ModelConstraints
from model_checker.models.structure import ModelDefaults
from model_checker.utils import bitvec_to_substates, int_to_binary

# Local imports
# Absolute import: see core.py's comment on the identical scaffolded-project depth defect.
from model_checker.theory_lib.types import StateId
# NOTE: WitnessSemantics is intentionally NOT imported at module level here -- core.py imports
# WitnessAwareModel from this module, so a top-level "from .core import WitnessSemantics"
# would create a circular import (core -> model -> core). WitnessModelAdapter.__init__ below
# imports it locally instead, which is safe since it only needs it once construction actually
# happens, well after both modules have finished their own top-level execution.


class WitnessAwareModel:
    """
    Model that treats witness functions as first-class predicates.

    In addition to standard predicates (verify, exclude, fusion, etc.),
    this model includes witness predicates for negation formulas.
    """

    def __init__(self, z3_model: z3.ModelRef, semantics: Any, witness_predicates: Dict[str, z3.FuncDeclRef]) -> None:
        self.z3_model: z3.ModelRef = z3_model
        self.semantics: Any = semantics
        self.witness_predicates: Dict[str, z3.FuncDeclRef] = witness_predicates
        # Cache for evaluated predicates
        self._cache: Dict[str, Any] = {}

    def eval(self, expr: z3.ExprRef) -> z3.ExprRef:
        """Standard Z3 model evaluation."""
        return self.z3_model.eval(expr)

    def has_witness_for(self, formula_str: str) -> bool:
        """Check if model has witness predicates for given formula."""
        return f"{formula_str}_h" in self.witness_predicates

    def get_h_witness(self, formula_str: str, state: Union[int, StateId]) -> Optional[int]:
        """
        Get h(state) for the given formula.
        This is the key method that makes witnesses accessible.
        """
        h_pred = self.witness_predicates.get(f"{formula_str}_h")
        if h_pred is None:
            return None

        # Query the witness predicate
        state_bv = z3.BitVecVal(state, self.semantics.N)
        result = self.eval(h_pred(state_bv))
        if z3.is_bv_value(result):
            return result.as_long()
        return None

    def get_y_witness(self, formula_str: str, state: int) -> Optional[int]:
        """Get y(state) for the given formula."""
        y_pred = self.witness_predicates.get(f"{formula_str}_y")
        if y_pred is None:
            return None

        state_bv = z3.BitVecVal(state, self.semantics.N)
        result = self.eval(y_pred(state_bv))
        if z3.is_bv_value(result):
            return result.as_long()
        return None

    def get_all_witness_values(self, formula_str: str) -> Dict[int, Tuple[int, int]]:
        """Get all witness values for a formula."""
        witness_map = {}

        for state in range(2**self.semantics.N):
            h_val = self.get_h_witness(formula_str, state)
            y_val = self.get_y_witness(formula_str, state)
            if h_val is not None and y_val is not None:
                witness_map[state] = (h_val, y_val)

        return witness_map


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
        from .core import WitnessSemantics  # local import: see module-level note above

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
            is_possible = is_true(result)
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
            if is_true(evaluate(self.semantics.is_world(state)))
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
            if is_true(evaluate(self.semantics.excludes(bit_x, bit_y)))
        ]

        # Update conflicts data
        self.z3_conflicts = [
            (bit_x, bit_y)
            for bit_x in self.all_states
            for bit_y in self.all_states
            if is_true(evaluate(self.semantics.conflicts(bit_x, bit_y)))
        ]

        # Update coherence data
        self.z3_coheres = [
            (bit_x, bit_y)
            for bit_x in self.all_states
            for bit_y in self.all_states
            if is_true(evaluate(self.semantics.coheres(bit_x, bit_y)))
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
                if is_true(result):
                    return True
                elif is_false(result):
                    return False

            simplified = z3.simplify(result)

            if is_true(simplified):
                return True
            elif is_false(simplified):
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
