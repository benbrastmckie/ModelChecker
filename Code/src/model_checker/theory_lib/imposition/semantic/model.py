"""
Model structure implementation for imposition theory.

This module contains the ImpositionModelStructure class that extends
LogosModelStructure with imposition relation printing and extraction capabilities.
"""

import sys
import time
from typing import Dict, Any, List, Optional, Set, Tuple

import z3

from model_checker.theory_lib.logos import LogosModelStructure
from model_checker.utils import bitvec_to_substates


class ImpositionModelStructure(LogosModelStructure):
    """
    Model structure for imposition theory that extends LogosModelStructure
    with imposition relation printing capabilities.
    """

    def __init__(self, model_constraints: List[z3.BoolRef], settings: Dict[str, Any]):
        """Initialize the imposition model structure.

        Args:
            model_constraints: Z3 constraints for the model
            settings: Configuration settings
        """
        super().__init__(model_constraints, settings)

        # Initialize imposition relations storage
        self.z3_imposition_relations = []

        # Only evaluate if we have a valid model
        if self.z3_model_status and self.z3_model is not None:
            self._update_imposition_relations()

    def _evaluate_z3_boolean(self, z3_model: z3.ModelRef, expression: z3.BoolRef) -> bool:
        """Safely evaluate a Z3 boolean expression to a Python boolean.

        This method handles the case where Z3 returns symbolic expressions
        instead of concrete boolean values, which can cause
        "Symbolic expressions cannot be cast to concrete Boolean values" errors.

        Args:
            z3_model: The Z3 model to evaluate against
            expression: The Z3 boolean expression to evaluate

        Returns:
            Boolean value of the expression
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
                return False

        except Exception:
            return False

    def _update_imposition_relations(self) -> None:
        """Extract imposition relations from the Z3 model."""
        if not hasattr(self.semantics, 'imposition'):
            return

        # Find all imposition triples (state, world, outcome)
        self.z3_imposition_relations = []

        for state in self.all_states:
            for world in self.z3_world_states:
                for outcome in self.z3_world_states:
                    try:
                        if self._evaluate_z3_boolean(self.z3_model, self.semantics.imposition(state, world, outcome)):
                            self.z3_imposition_relations.append((state, world, outcome))
                    except:
                        pass

    def print_all(self, default_settings: Dict[str, Any], example_name: str, theory_name: str, output=sys.__stdout__) -> None:
        """Print model including imposition relations.

        Args:
            default_settings: Default settings for printing
            example_name: Name of the example being processed
            theory_name: Name of the theory
            output: Output stream for printing
        """
        model_status = self.z3_model_status
        self.print_info(model_status, self.settings, example_name, theory_name, output)
        if model_status:
            self.print_states(output)
            self.print_imposition(output)
            self.print_evaluation(output)
            self.print_input_sentences(output)
            self.print_model(output)
            if output is sys.__stdout__:
                total_time = round(time.time() - self.start_time, 4)
                print(f"Total Run Time: {total_time} seconds\n", file=output)
            # Always print closing separator for countermodels
            print(f"\n{'='*40}", file=output)
            return

    def print_imposition(self, output=sys.__stdout__) -> None:
        """Print imposition relations in the format 'a ->_w u'.

        Args:
            output: Output stream for printing
        """
        if not self.z3_imposition_relations:
            return

        print("\nImposition Relation:", file=output)

        # Set up colors if outputting to stdout
        use_colors = output is sys.__stdout__
        WHITE = "\033[37m" if use_colors else ""
        RESET = "\033[0m" if use_colors else ""
        WORLD_COLOR = "\033[34m" if use_colors else ""
        POSSIBLE_COLOR = "\033[36m" if use_colors else ""

        def get_state_color(bit: z3.BitVecRef) -> str:
            """Get the appropriate color for a state based on its type."""
            if bit in self.z3_world_states:
                return WORLD_COLOR
            elif bit in self.z3_possible_states:
                return POSSIBLE_COLOR
            else:
                return WHITE

        # Group impositions by world being imposed on
        impositions_by_world = {}
        for state, world, outcome in self.z3_imposition_relations:
            if world not in impositions_by_world:
                impositions_by_world[world] = []
            impositions_by_world[world].append((state, outcome))

        # Print impositions grouped by world
        for world in sorted(impositions_by_world.keys(), key=lambda x: x if isinstance(x, int) else x.as_long()):
            world_str = bitvec_to_substates(world, self.N)
            world_color = get_state_color(world)

            for state, outcome in sorted(impositions_by_world[world], key=lambda x: (x[0] if isinstance(x[0], int) else x[0].as_long(), x[1] if isinstance(x[1], int) else x[1].as_long())):
                state_str = bitvec_to_substates(state, self.N)
                outcome_str = bitvec_to_substates(outcome, self.N)

                state_color = get_state_color(state)
                outcome_color = get_state_color(outcome)

                # Print in format: a ->_w u (meaning: u is the outcome of imposing a on w)
                print(f"  {state_color}{state_str}{RESET} →_{world_color}{world_str}{RESET} {outcome_color}{outcome_str}{RESET}", file=output)

    def extract_states(self) -> Dict[str, List[str]]:
        """Extract categorized states for output.

        Returns:
            Dictionary containing categorized state lists
        """
        states = {"worlds": [], "possible": [], "impossible": []}

        # Extract world states
        if hasattr(self, 'z3_world_states') and self.z3_world_states:
            for state in self.z3_world_states:
                state_val = state if isinstance(state, int) else state.as_long()
                states["worlds"].append(f"s{state_val}")

        # Extract possible states (non-world)
        if hasattr(self, 'z3_possible_states') and self.z3_possible_states:
            for state in self.z3_possible_states:
                state_val = state if isinstance(state, int) else state.as_long()
                # Only add if not already in worlds
                state_str = f"s{state_val}"
                if state_str not in states["worlds"]:
                    states["possible"].append(state_str)

        # Extract impossible states
        if hasattr(self, 'all_states') and self.all_states:
            for state in self.all_states:
                state_val = state if isinstance(state, int) else state.as_long()
                state_str = f"s{state_val}"
                # Add if not in worlds or possible
                if state_str not in states["worlds"] and state_str not in states["possible"]:
                    states["impossible"].append(state_str)

        return states

    def extract_evaluation_world(self) -> Optional[str]:
        """Extract the main evaluation world.

        Returns:
            String representation of the evaluation world, or None
        """
        if hasattr(self.semantics, 'main_world') and self.semantics.main_world is not None:
            world_val = self.semantics.main_world
            if hasattr(world_val, 'as_long'):
                world_val = world_val.as_long()
            return f"s{world_val}"
        return None

    def extract_relations(self) -> Dict[str, Any]:
        """Extract imposition relations.

        Returns:
            Dictionary containing imposition relations
        """
        relations = {}

        if hasattr(self, 'z3_imposition_relations') and self.z3_imposition_relations:
            relations['imposition'] = {}

            # Group impositions by world being imposed on
            for state, world, outcome in self.z3_imposition_relations:
                # Convert to integers if needed
                state_val = state if isinstance(state, int) else state.as_long()
                world_val = world if isinstance(world, int) else world.as_long()
                outcome_val = outcome if isinstance(outcome, int) else outcome.as_long()

                world_name = f"s{world_val}"
                state_name = f"s{state_val}"
                outcome_name = f"s{outcome_val}"

                # Structure: relations['imposition'][world][state] = outcome
                if world_name not in relations['imposition']:
                    relations['imposition'][world_name] = {}

                relations['imposition'][world_name][state_name] = outcome_name

        return relations

    def extract_propositions(self) -> Dict[str, Dict[str, bool]]:
        """Extract proposition truth values at states.

        Returns:
            Dictionary mapping proposition names to state truth values
        """
        propositions = {}

        if not hasattr(self.syntax, 'propositions'):
            return propositions

        # For each proposition, evaluate at all worlds
        for prop_name, prop in self.syntax.propositions.items():
            propositions[prop_name] = {}

            # Evaluate at worlds (imposition uses world evaluation like logos)
            if hasattr(self, 'z3_world_states') and self.z3_world_states:
                for world in self.z3_world_states:
                    world_val = world if isinstance(world, int) else world.as_long()
                    world_name = f"s{world_val}"

                    try:
                        # Use evaluate_at method if available
                        if hasattr(prop, 'evaluate_at'):
                            truth_val = prop.evaluate_at(world)
                            if hasattr(truth_val, 'as_bool'):
                                truth_val = truth_val.as_bool()
                            propositions[prop_name][world_name] = bool(truth_val)
                    except:
                        # Skip if evaluation fails
                        pass

        return propositions

    def initialize_from_z3_model(self, z3_model: z3.ModelRef) -> None:
        """Initialize imposition-specific attributes from Z3 model.

        This method is called by the iterator when creating new model structures.

        Args:
            z3_model: The Z3 model to initialize from
        """
        # Store the Z3 model first
        self.z3_model = z3_model

        # Call comprehensive model structure update like exclusion theory does
        # This also handles proposition initialization
        self._update_model_structure(z3_model)

    def _update_model_structure(self, z3_model: z3.ModelRef) -> None:
        """Update model structure from Z3 model, including semantic relations.

        This method ensures all Z3-dependent attributes are correctly set
        based on the provided Z3 model, following the pattern used by
        the exclusion theory.

        Args:
            z3_model: The Z3 model to update from
        """
        evaluate = z3_model.evaluate

        # Don't re-evaluate main_world if already set by iterator
        if not hasattr(self, 'z3_main_world') or self.z3_main_world is None:
            self.main_world = self.main_point["world"]
            self.main_point["world"] = z3_model.eval(self.main_world, model_completion=True)

        # Update possible states
        self.z3_possible_states = [
            state for state in self.all_states
            if self._evaluate_z3_boolean(z3_model, self.semantics.possible(state))
        ]

        # Update world states
        self.z3_world_states = [
            state for state in self.z3_possible_states
            if self._evaluate_z3_boolean(z3_model, self.semantics.is_world(state))
        ]

        # Update impossible states
        self.z3_impossible_states = [
            i for i in self.all_states
            if i not in self.z3_possible_states
        ]

        # Update imposition relations
        self._update_imposition_relations()

    def print_model_differences(self, output=sys.__stdout__) -> bool:
        """Print imposition theory differences.

        Args:
            output: Output stream for printing

        Returns:
            True if differences were printed
        """
        if not hasattr(self, 'model_differences') or not self.model_differences:
            return False

        diffs = self.model_differences

        # Print header with colors
        print(f"\n{self.COLORS['world']}=== DIFFERENCES FROM PREVIOUS MODEL ==={self.RESET}\n", file=output)

        # World changes - use 'world_changes' key from generic calculator
        worlds = diffs.get('world_changes', {})
        if worlds.get('added') or worlds.get('removed'):
            print(f"{self.COLORS['world']}World Changes:{self.RESET}", file=output)
            for world in worlds.get('added', []):
                world_str = bitvec_to_substates(world, self.N)
                print(f"  {self.COLORS['possible']}+ {world_str} (now a world){self.RESET}", file=output)
            for world in worlds.get('removed', []):
                world_str = bitvec_to_substates(world, self.N)
                print(f"  {self.COLORS['impossible']}- {world_str} (no longer a world){self.RESET}", file=output)
            print(file=output)

        # Possible state changes
        possible = diffs.get('possible_changes', {})
        if possible.get('added') or possible.get('removed'):
            print(f"{self.COLORS['world']}Possible State Changes:{self.RESET}", file=output)
            for state in possible.get('added', []):
                state_str = bitvec_to_substates(state, self.N)
                print(f"  {self.COLORS['possible']}+ {state_str} (now possible){self.RESET}", file=output)
            for state in possible.get('removed', []):
                state_str = bitvec_to_substates(state, self.N)
                print(f"  {self.COLORS['impossible']}- {state_str} (now impossible){self.RESET}", file=output)
            print(file=output)

        # Verification changes (theory-specific)
        verification = diffs.get('verification', {})
        if verification:
            print(f"{self.COLORS['world']}Verification Changes:{self.RESET}", file=output)
            for letter_str, changes in verification.items():
                letter_name = letter_str.replace('Proposition_', '').replace('(', '').replace(')', '')
                print(f"  Letter {letter_name}:", file=output)

                if changes.get('added'):
                    for state in changes['added']:
                        try:
                            state_str = bitvec_to_substates(state, self.N)
                            print(f"    {self.COLORS['possible']}+ {state_str} now verifies {letter_name}{self.RESET}", file=output)
                        except:
                            print(f"    {self.COLORS['possible']}+ {state} now verifies {letter_name}{self.RESET}", file=output)

                if changes.get('removed'):
                    for state in changes['removed']:
                        try:
                            state_str = bitvec_to_substates(state, self.N)
                            print(f"    {self.COLORS['impossible']}- {state_str} no longer verifies {letter_name}{self.RESET}", file=output)
                        except:
                            print(f"    {self.COLORS['impossible']}- {state} no longer verifies {letter_name}{self.RESET}", file=output)
            print(file=output)

        # Falsification changes (theory-specific)
        falsification = diffs.get('falsification', {})
        if falsification:
            print(f"{self.COLORS['world']}Falsification Changes:{self.RESET}", file=output)
            for letter_str, changes in falsification.items():
                letter_name = letter_str.replace('Proposition_', '').replace('(', '').replace(')', '')
                print(f"  Letter {letter_name}:", file=output)

                if changes.get('added'):
                    for state in changes['added']:
                        try:
                            state_str = bitvec_to_substates(state, self.N)
                            print(f"    {self.COLORS['possible']}+ {state_str} now falsifies {letter_name}{self.RESET}", file=output)
                        except:
                            print(f"    {self.COLORS['possible']}+ {state} now falsifies {letter_name}{self.RESET}", file=output)

                if changes.get('removed'):
                    for state in changes['removed']:
                        try:
                            state_str = bitvec_to_substates(state, self.N)
                            print(f"    {self.COLORS['impossible']}- {state_str} no longer falsifies {letter_name}{self.RESET}", file=output)
                        except:
                            print(f"    {self.COLORS['impossible']}- {state} no longer falsifies {letter_name}{self.RESET}", file=output)
            print(file=output)

        # Imposition relation changes (theory-specific with improved formatting)
        imp_diffs = diffs.get('imposition_relations', {})
        if imp_diffs:
            print(f"{self.COLORS['world']}Imposition Changes:{self.RESET}", file=output)
            for relation, change in imp_diffs.items():
                # Try to parse the state pair for better formatting
                try:
                    states = relation.split(',')
                    if len(states) == 2:
                        state1_bitvec = int(states[0])
                        state2_bitvec = int(states[1])

                        state1_str = bitvec_to_substates(state1_bitvec, self.N)
                        state2_str = bitvec_to_substates(state2_bitvec, self.N)

                        if change.get('new'):
                            print(f"  {self.COLORS['possible']}+ {state1_str} can now impose on {state2_str}{self.RESET}", file=output)
                        else:
                            print(f"  {self.COLORS['impossible']}- {state1_str} can no longer impose on {state2_str}{self.RESET}", file=output)
                        continue
                except:
                    pass

                # Fall back to simple representation if parsing fails
                if change.get('new'):
                    print(f"  {self.COLORS['possible']}+ {relation}: can now impose{self.RESET}", file=output)
                else:
                    print(f"  {self.COLORS['impossible']}- {relation}: can no longer impose{self.RESET}", file=output)
            print(file=output)

        return True