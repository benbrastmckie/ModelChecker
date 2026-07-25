"""
Model structure implementation for the logos theory.

This module contains LogosModelStructure, which manages the overall semantic
model structure for the logos theory with support for all subtheories and
modular operator loading.
"""

import sys
import time
from typing import Any, Dict, List, Optional, TYPE_CHECKING

from model_checker import z3_shim as z3

from model_checker.solver import is_true, is_false
from model_checker.models.structure import ModelDefaults
from model_checker.utils import bitvec_to_substates, int_to_binary

if TYPE_CHECKING:
    from model_checker.models.model_constraints import ModelConstraints


class LogosModelStructure(ModelDefaults):
    """
    Model structure with modular operator support.

    Manages the overall semantic model structure for the logos theory
    with support for all subtheories and modular operator loading.
    """

    def __init__(self, model_constraints: 'ModelConstraints', settings: Dict[str, Any]) -> None:
        super().__init__(model_constraints, settings)
        self.loaded_subtheories = []

        # Get main point
        self.main_world = self.main_point["world"]

        # Initialize Z3 model values
        self.z3_main_world = None
        self.z3_possible_states = None
        self.z3_world_states = None

        # Initialize attributes for difference tracking
        self.model_differences = None  # Will store differences with previous model
        self.previous_model = None     # Reference to previous model for comparison

        # Only evaluate if we have a valid model
        if self.z3_model_status and self.z3_model is not None:
            self.z3_main_world = self.z3_model[self.main_world]
            self.main_point["world"] = self.z3_main_world
            self.z3_possible_states = [
                bit
                for bit in self.all_states
                if bool(self.z3_model.evaluate(self.semantics.possible(bit)))
            ]
            self.z3_world_states = [
                bit
                for bit in self.z3_possible_states
                if bool(self.z3_model.evaluate(self.semantics.is_world(bit)))
            ]

    def load_subtheories(self, subtheories: List[str]) -> None:
        """Load specified subtheories into the model."""
        self.loaded_subtheories.extend(subtheories)
        if hasattr(self.semantics, 'load_subtheories'):
            self.semantics.load_subtheories(subtheories)

    def get_available_operators(self) -> Dict[str, Any]:
        """Get all operators from loaded subtheories."""
        if hasattr(self.semantics, 'operator_registry'):
            return self.semantics.operator_registry.get_operators()
        return {}

    def print_model_info(self) -> None:
        """Print information about the loaded model."""
        print(f"Logos Theory Model")
        print(f"Loaded subtheories: {', '.join(self.loaded_subtheories)}")

        operators = self.get_available_operators()
        if operators:
            print(f"Available operators: {len(operators)}")
            for name, op in operators.items():
                print(f"  - {name}: {op.__class__.__name__}")
        else:
            print("No operators loaded")

    def _evaluate_z3_boolean_for_model(self, expression: z3.BoolRef) -> bool:
        """Safely evaluate a Z3 boolean expression using the model.

        This method handles the case where Z3 returns symbolic expressions
        instead of concrete boolean values.

        Args:
            expression: The Z3 boolean expression to evaluate

        Returns:
            bool: True if the expression evaluates to true, False otherwise
        """
        try:
            result = self.z3_model.evaluate(expression, model_completion=True)
            if is_true(result):
                return True
            elif is_false(result):
                return False

            # Try to simplify
            simplified = z3.simplify(result)
            if is_true(simplified):
                return True
            elif is_false(simplified):
                return False

            # Conservative default
            return False
        except Exception:
            return False

    def print_all(self, default_settings, example_name, theory_name, output=sys.__stdout__):
        """Print a complete overview of the model structure and evaluation results.

        This method provides a comprehensive display of the model, including:
        - Model states and their properties
        - Evaluation results at the designated world
        - Truth values of atomic sentence letters
        - Recursive evaluation of complex sentences and their subformulas

        Args:
            default_settings (dict): Default configuration settings for the model
            example_name (str): Name of the example being evaluated
            theory_name (str): Name of the logical theory being used
            output (file, optional): Output stream to write to. Defaults to sys.stdout
        """
        model_status = self.z3_model_status
        self.print_info(model_status, self.settings, example_name, theory_name, output)
        if model_status:
            self.print_states(output)
            self.print_evaluation(output)
            self.print_input_sentences(output)
            self.print_model(output)
            if output is sys.__stdout__:
                total_time = round(time.time() - self.start_time, 4)
                print(f"Total Run Time: {total_time} seconds", file=output)
            # Always print closing separator for countermodels
            print(f"\n{'='*40}", file=output)
            return

    def print_to(self, default_settings, example_name, theory_name, print_constraints=None, output=sys.__stdout__):
        """Print the model details to the specified output stream.

        This method prints all elements of the model including states, evaluation results,
        and optionally constraints to the provided output stream.

        Args:
            default_settings (dict): Default configuration settings for the model
            example_name (str): Name of the example being evaluated
            theory_name (str): Name of the logical theory being used
            print_constraints (bool, optional): Whether to print model constraints.
                Defaults to the value in self.settings.
            output (TextIO, optional): Output stream to write to. Defaults to sys.stdout.
        """
        if print_constraints is None:
            print_constraints = self.settings["print_constraints"]
        # Check if we actually timed out (runtime >= max_time)
        actual_timeout = hasattr(self, 'z3_model_runtime') and self.z3_model_runtime is not None and self.z3_model_runtime >= self.max_time

        # Only show timeout if we really timed out and didn't find a model
        if actual_timeout and (not hasattr(self, 'z3_model') or self.z3_model is None):
            print(f"\nTIMEOUT: Model search exceeded maximum time of {self.max_time} seconds", file=output)
            print(f"No model for example {example_name} found before timeout.", file=output)
            print(f"Try increasing max_time > {self.max_time}.\n", file=output)
        self.print_all(self.settings, example_name, theory_name, output)

        if print_constraints and self.unsat_core is not None:
            self.print_grouped_constraints(output)

    def print_model_differences(self, output=sys.stdout):
        """Print differences between this model and the previous one.

        Logos-specific implementation that understands hyperintensional semantics.

        Args:
            output (file, optional): Output stream to write to. Defaults to sys.stdout.
        """
        if not hasattr(self, 'model_differences') or not self.model_differences:
            return

        diffs = self.model_differences

        # Use colors if outputting to terminal
        if output is sys.stdout:
            GREEN = "\033[32m"
            RED = "\033[31m"
            YELLOW = "\033[33m"
            BLUE = "\033[34m"
            RESET = "\033[0m"
        else:
            GREEN = RED = YELLOW = BLUE = RESET = ""

        print(f"\n{YELLOW}=== DIFFERENCES FROM PREVIOUS MODEL ==={RESET}\n", file=output)

        # Print world changes
        if diffs.get('world_changes', {}).get('added') or diffs.get('world_changes', {}).get('removed'):
            print(f"{BLUE}World Changes:{RESET}", file=output)
            for world in diffs.get('world_changes', {}).get('added', []):
                world_str = bitvec_to_substates(world, self.N)
                print(f"  {GREEN}+ {world_str} (now a world){RESET}", file=output)
            for world in diffs.get('world_changes', {}).get('removed', []):
                world_str = bitvec_to_substates(world, self.N)
                print(f"  {RED}- {world_str} (no longer a world){RESET}", file=output)
            print("", file=output)

        # Print possible state changes
        if diffs.get('possible_changes', {}).get('added') or diffs.get('possible_changes', {}).get('removed'):
            print(f"{BLUE}Possible State Changes:{RESET}", file=output)
            for state in diffs.get('possible_changes', {}).get('added', []):
                state_str = bitvec_to_substates(state, self.N)
                print(f"  {GREEN}+ {state_str} (now possible){RESET}", file=output)
            for state in diffs.get('possible_changes', {}).get('removed', []):
                state_str = bitvec_to_substates(state, self.N)
                print(f"  {RED}- {state_str} (now impossible){RESET}", file=output)
            print("", file=output)

        # Print atomic changes (verify/falsify)
        if diffs.get('atomic_changes'):
            atomic = diffs.get('atomic_changes', {})
            # Print verification changes
            if atomic.get('verify'):
                print(f"{BLUE}Verification Changes:{RESET}", file=output)
                for letter, state_changes in atomic['verify'].items():
                    print(f"  Letter {letter}:", file=output)
                    for state_str, change in state_changes.items():
                        if change['new']:
                            print(f"    {GREEN}+ {state_str} now verifies {letter}{RESET}", file=output)
                        else:
                            print(f"    {RED}- {state_str} no longer verifies {letter}{RESET}", file=output)
                print("", file=output)

            # Print falsification changes
            if atomic.get('falsify'):
                print(f"{BLUE}Falsification Changes:{RESET}", file=output)
                for letter, state_changes in atomic['falsify'].items():
                    print(f"  Letter {letter}:", file=output)
                    for state_str, change in state_changes.items():
                        if change['new']:
                            print(f"    {GREEN}+ {state_str} now falsifies {letter}{RESET}", file=output)
                        else:
                            print(f"    {RED}- {state_str} no longer falsifies {letter}{RESET}", file=output)
                print("", file=output)

        # Print parthood changes
        if diffs.get('parthood'):
            print(f"{BLUE}Part-of Relation Changes:{RESET}", file=output)
            for relation, change in diffs['parthood'].items():
                if change['new']:
                    print(f"  {GREEN}+ {relation}{RESET}", file=output)
                else:
                    print(f"  {RED}- {relation}{RESET}", file=output)
            print("", file=output)

    def print_evaluation(self, output=sys.__stdout__):
        """Print the evaluation world and evaluate all sentence letters at that world."""
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

    def print_states(self, output=sys.__stdout__):
        """Print all states in the model with their binary representations and properties."""
        def binary_bitvector(bit):
            return (
                bit.sexpr()
                if self.N % 4 != 0
                else int_to_binary(int(bit.sexpr()[2:], 16), self.N)
            )

        def format_state(bin_rep, state, color, label=""):
            label_str = f" ({label})" if label else ""
            use_colors = output is sys.__stdout__
            if use_colors:
                print(f"  {self.WHITE}{bin_rep} = {color}{state}{label_str}{self.RESET}", file=output)
            else:
                print(f"  {bin_rep} = {state}{label_str}", file=output)

        # Print formatted state space
        print("\nState Space:", file=output)
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

    def extract_states(self) -> Dict[str, List[str]]:
        """Extract categorized states for output.

        Logos distinguishes between worlds, possible states, and impossible states.

        Returns:
            Dict with keys 'worlds', 'possible', 'impossible'
        """
        states = {"worlds": [], "possible": [], "impossible": []}

        if hasattr(self, 'z3_world_states') and self.z3_world_states:
            for state in self.z3_world_states:
                # Convert bit vector to state number
                if hasattr(state, 'as_long'):
                    states["worlds"].append(f"s{state.as_long()}")
                else:
                    states["worlds"].append(f"s{state}")

        if hasattr(self, 'z3_possible_states') and self.z3_possible_states:
            for state in self.z3_possible_states:
                # Only add if not already a world
                if state not in (self.z3_world_states if hasattr(self, 'z3_world_states') else []):
                    if hasattr(state, 'as_long'):
                        states["possible"].append(f"s{state.as_long()}")
                    else:
                        states["possible"].append(f"s{state}")

        # For impossible states, we need to check all states that aren't possible
        if hasattr(self, 'all_states') and self.all_states:
            # Convert possible states to integers for comparison
            possible_set = set()
            if hasattr(self, 'z3_possible_states') and self.z3_possible_states:
                for ps in self.z3_possible_states:
                    if hasattr(ps, 'as_long'):
                        possible_set.add(ps.as_long())
                    else:
                        possible_set.add(ps)

            for state in self.all_states:
                # Convert state to integer for comparison
                state_val = state.as_long() if hasattr(state, 'as_long') else state

                # Check if not possible and not null state
                if state_val not in possible_set and state_val != 0:
                    states["impossible"].append(f"s{state_val}")

        return states

    def extract_evaluation_world(self) -> Optional[str]:
        """Extract the main evaluation world.

        Returns:
            State name (e.g., 's3') or None if not set
        """
        if hasattr(self, 'z3_main_world') and self.z3_main_world is not None:
            if hasattr(self.z3_main_world, 'as_long'):
                return f"s{self.z3_main_world.as_long()}"
            else:
                return f"s{self.z3_main_world}"
        return None

    def extract_relations(self) -> Dict[str, Any]:
        """Extract relations between states.

        For Logos, this includes fusion/fission relations and compatibility.

        Returns:
            Dict containing various relations
        """
        relations = {}

        # Add any Logos-specific relations here
        # For now, return empty as relations are computed dynamically

        return relations

    def extract_propositions(self) -> Dict[str, Dict[str, bool]]:
        """Extract proposition truth values at worlds.

        Returns:
            Dict mapping propositions to their truth values at each world
        """
        propositions = {}

        if not hasattr(self, 'syntax') or not hasattr(self.syntax, 'propositions'):
            return propositions

        # Get world states
        worlds = []
        if hasattr(self, 'z3_world_states'):
            worlds = self.z3_world_states

        # Extract truth values for each proposition
        for prop_name, prop_obj in self.syntax.propositions.items():
            if hasattr(prop_obj, 'letter'):
                letter = prop_obj.letter
                propositions[letter] = {}

                for world in worlds:
                    # Get world number
                    if hasattr(world, 'as_long'):
                        world_num = world.as_long()
                    else:
                        world_num = world

                    world_name = f"s{world_num}"

                    if hasattr(prop_obj, 'truth_value_at'):
                        try:
                            # Logos propositions use truth_value_at
                            propositions[letter][world_name] = prop_obj.truth_value_at(world_num)
                        except:
                            # If evaluation fails, skip this world
                            pass

        return propositions
