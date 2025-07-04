"""
Simplified exclusion semantics module.
Removes multi-strategy complexity and focuses on core semantic primitives.
"""

import z3
import sys
import time

from model_checker.utils import (
    ForAll,
    Exists,
    bitvec_to_substates,
    pretty_set_print,
    int_to_binary,
)
from model_checker import model
from model_checker import syntactic


class ExclusionSemantics(model.SemanticDefaults):
    """
    Simplified exclusion semantics with single strategy support.
    
    This implementation removes all multi-strategy code and focuses on
    the core semantic primitives needed for exclusion logic.
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
        'iteration_timeout': 1.0,
        'iteration_attempts': 5,
        'max_time': 1,
        'expectation': None,
    }
    
    # Default general settings for the exclusion theory
    DEFAULT_GENERAL_SETTINGS = {
        "print_impossible": False,
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,
        "maximize": False,
    }

    def __init__(self, combined_settings):
        # Initialize the superclass to set defaults
        super().__init__(combined_settings)
        
        # Override premise and conclusion behavior attributes
        # (parent class sets them to None by default)
        self.premise_behavior = self._premise_behavior_method
        self.conclusion_behavior = self._conclusion_behavior_method

        # Define the Z3 primitives - only what we need
        self.verify = z3.Function(
            "verify",  # name
            z3.BitVecSort(self.N),  # first argument type: bitvector
            syntactic.AtomSort,     # second argument type: sentence letter
            z3.BoolSort(),          # return type: boolean
        )
        
        self.excludes = z3.Function(
            "excludes",  # name
            z3.BitVecSort(self.N),  # first argument type: bitvector
            z3.BitVecSort(self.N),  # second argument type: bitvector
            z3.BoolSort(),          # return type: boolean
        )
        
        self.main_world = z3.BitVec("w", self.N)
        self.main_point = {
            "world": self.main_world
        }

        # Simple counter for unique naming
        self.counter = 0
        
        # Define additional semantic relations
        self._define_semantic_relations()

        # Define frame constraints
        x, y, z, u = z3.BitVecs("frame_x frame_y frame_z frame_u", self.N)
        
        # Actuality constraint
        actuality = self.is_world(self.main_world)
        
        # Basic exclusion properties
        exclusion_symmetry = ForAll(
            [x, y],
            z3.Implies(
                self.excludes(x, y),
                self.excludes(y, x)
            )
        )
        
        # Null state excludes nothing
        null_state = ForAll(x, z3.Not(self.excludes(self.null_state, x)))
        
        # Harmony between worlds and possibility
        harmony = ForAll( 
            [x, y],
            z3.Implies(
                z3.And(
                    self.is_world(x),
                    self.coheres(x, y)
                ),
                self.possible(y)
            ),
        )
        
        # Rashomon principle
        rashomon = ForAll(
            [x, y],
            z3.Implies(
                z3.And(
                    self.possible(x),
                    self.possible(y),
                    self.coheres(x, y)
                ),
                self.compossible(x, y),
            ),
        )

        # Cosmopolitanism principle
        cosmopolitanism = ForAll(
            x,
            z3.Implies(
                self.possible(x),
                Exists(
                    y,
                    z3.And(
                        self.is_world(y),
                        self.is_part_of(x, y)
                    )
                )
            )
        )

        # Cumulativity: if e excludes e' and f excludes f', then e ⊔ f excludes e' ⊔ f'
        cumulativity = ForAll(
            [x, y, z, u], 
            z3.Implies(
                z3.And(self.excludes(x,z), self.excludes(y,u)), 
                self.excludes(self.fusion(x,y), self.fusion(z,u))
            )
        )

        # Plenitude
        plenitude = ForAll(
            x, 
            z3.And(
                z3.Implies(
                    self.possible(x), 
                    Exists(y, z3.And(self.coheres(x,y), self.is_world(y)))
                ), 
                z3.Implies(
                    Exists(y, z3.And(self.coheres(x,y), self.is_world(y))), 
                    self.possible(x)
                )
            )
        )

        # Excluders exist for non-null states
        excluders = ForAll(
            x,
            z3.Implies(
                x != self.null_state,
                Exists(
                    y,
                    self.excludes(y, x)
                )
            )
        )

        # Partial excluders
        partial_excluders = ForAll(
            x,
            z3.Implies(
                x != self.null_state,
                Exists(
                    [y, z],
                    z3.And(
                        self.is_part_of(y, x),
                        self.excludes(z, y)
                    )
                )
            )
        )

        # Possibility downward closure
        possibility_downward_closure = ForAll(
            [x, y],
            z3.Implies(
                z3.And(
                    self.possible(y),
                    self.is_part_of(x, y)
                ),
                self.possible(x)
            ),
        )

        # Define coherence in terms of exclusion
        coherence_def = ForAll(
            [x, y],
            self.coheres(x, y) == z3.Not(self.excludes(x, y))
        )
        
        # Set frame constraints
        self.frame_constraints = [
            # Core constraints
            actuality,
            exclusion_symmetry,
            null_state,
            coherence_def,
            
            # Modal constraints
            harmony,
            rashomon,
            cosmopolitanism,
            
            # Exclusion constraints
            cumulativity,
            plenitude,
            excluders,
            partial_excluders,
            possibility_downward_closure,
        ]

    def _define_semantic_relations(self):
        """Define additional semantic relations needed for exclusion logic."""
        N = self.N
        
        # Possible relation - states that could exist
        self.possible = z3.Function(
            "possible",
            z3.BitVecSort(N),
            z3.BoolSort()
        )
        
        # Coherence relation - states that don't exclude each other
        self.coheres = z3.Function(
            "coheres",
            z3.BitVecSort(N),
            z3.BitVecSort(N),
            z3.BoolSort()
        )
        
        # Compossible relation - states that can coexist
        self.compossible = z3.Function(
            "compossible",
            z3.BitVecSort(N),
            z3.BitVecSort(N),
            z3.BoolSort()
        )
        
        # Necessary relation - states that must exist
        self.necessary = z3.Function(
            "necessary",
            z3.BitVecSort(N),
            z3.BoolSort()
        )
        
        # Coherence definition will be added to frame constraints later

    def is_world(self, bit_s):
        """
        Determines if a state is a world by checking if it is possible and maximal.
        A state is maximal if it has no proper extension that is possible.
        """
        m = z3.BitVec("m", self.N)
        return z3.And(
            self.possible(bit_s),
            z3.Not(
                Exists(
                    [m],
                    z3.And(
                        self.is_proper_part_of(bit_s, m),
                        self.possible(m)
                    )
                )
            )
        )

    def occurs(self, bit_s):
        """Check if a state occurs (is part of the main world)."""
        return self.is_part_of(bit_s, self.main_world)

    def product(self, set_X, set_Y):
        """Compute the product of two sets of states."""
        return {self.fusion(x, y) for x in set_X for y in set_Y}

    def true_at(self, sentence, eval_point):
        """
        Evaluate truth at an evaluation point with proper recursive reduction.
        
        For atomic sentences: reduces to verifier existence
        For complex sentences: delegates to operator's true_at method
        """
        if sentence.sentence_letter is not None:
            # Atomic case: exists v. verify(v, atom) AND is_part_of(v, world)
            v = z3.BitVec(f"v_atom_{id(sentence)}_{self.counter}", self.N)
            self.counter += 1
            return Exists([v], z3.And(
                self.verify(v, sentence.sentence_letter),
                self.is_part_of(v, eval_point["world"])
            ))
        else:
            # Complex case: delegate to operator
            return sentence.operator.true_at(*sentence.arguments, eval_point)

    def extended_verify(self, state, sentence, eval_point):
        """
        Extended verification with proper recursive reduction.
        
        For atomic sentences: direct verification
        For complex sentences: delegates to operator's extended_verify method
        """
        if sentence.sentence_letter is not None:
            # Atomic case: verify(state, atom)
            return self.verify(state, sentence.sentence_letter)
        else:
            # Complex case: delegate to operator
            return sentence.operator.extended_verify(state, *sentence.arguments, eval_point)

    def atom_constraints(self, letter_id, sentence_letters, settings):
        """
        Return constraints for an atomic sentence.
        Simplified version without multi-strategy complexity.
        """
        N = self.N
        verify = self.verify
        
        # Get settings from provided dict
        contingent = settings.get('contingent', False)
        non_empty = settings.get('non_empty', False)
        non_null = settings.get('non_null', False)
        disjoint = settings.get('disjoint', False)
        
        atom_constraints = []
        
        # Non-empty constraint
        if non_empty:
            v = z3.BitVec(f"v_{letter_id}_non_empty", N)
            constraint = Exists([v], verify(v, letter_id))
            atom_constraints.append(constraint)
        
        # Non-null constraint
        if non_null:
            constraint = z3.Not(verify(0, letter_id))
            atom_constraints.append(constraint)
        
        # Contingent constraint
        if contingent:
            x = z3.BitVec(f"v_{letter_id}_contingent", N)
            constraint = z3.And(
                Exists([x], z3.And(self.possible(x), verify(x, letter_id))),
                Exists([x], z3.And(self.possible(x), z3.Not(verify(x, letter_id))))
            )
            atom_constraints.append(constraint)
        
        # Disjoint constraint - atomic sentences have disjoint subject matters
        if disjoint and sentence_letters:
            if letter_id != sentence_letters[0]:
                for other_letter in sentence_letters:
                    if other_letter == letter_id:
                        break
                    else:
                        x = z3.BitVec(f"disjoint_{letter_id}_{other_letter}", N)
                        constraint = ForAll(
                            [x],
                            z3.Implies(
                                verify(x, letter_id), 
                                z3.Not(verify(x, other_letter))
                            )
                        )
                        atom_constraints.append(constraint)
        
        return atom_constraints

    def _premise_behavior_method(self, premise):
        """Premise must be true at main evaluation point."""
        return self.true_at(premise, self.main_point)

    def _conclusion_behavior_method(self, conclusion):
        """Conclusion must be false at main evaluation point."""
        return z3.Not(self.true_at(conclusion, self.main_point))


class UnilateralProposition(model.PropositionDefaults):
    """Proposition class for unilateral semantics."""
    
    def __init__(self, sentence, model_structure):
        super().__init__(sentence, model_structure)
        self.z3_model = model_structure.z3_model
        self.verifiers = self.find_proposition()
    
    @classmethod
    def proposition_constraints(cls, model_constraints, letter_id):
        """Generate constraints for atomic propositions."""
        return model_constraints.semantics.atom_constraints(
            letter_id,
            model_constraints.sentence_letters,
            model_constraints.settings
        )

    def find_proposition(self):
        """Find the set of verifiers for this sentence."""
        return self.model_structure.find_verifying_states(
            self.sentence, 
            self.model_structure.semantics.main_point
        )
    
    def __repr__(self):
        """Return pretty-printed representation of verifiers."""
        N = self.model_structure.semantics.N
        ver_states = {
            bitvec_to_substates(bit, N)
            for bit in self.verifiers
        }
        return pretty_set_print(ver_states)

    def truth_value_at(self, eval_point):
        """Evaluate truth value at a point."""
        return self.model_structure.true_at(
            self.sentence, 
            eval_point
        )

    def evaluate(self):
        """Evaluate at the main world."""
        z3_model = self.model_structure.z3_model
        world = self.model_structure.semantics.main_world
        z3_formula = self.truth_value_at({"world": world})
        return z3.is_true(z3_model.evaluate(z3_formula))

    def print_method(self, eval_point, indent_num, use_colors):
        """Print the proposition."""
        self.print_proposition(eval_point, indent_num, use_colors)
        
    def print_proposition(self, eval_point, indent_num, use_colors):
        """Print the proposition with its truth value at the evaluation point."""
        N = self.model_structure.semantics.N
        z3_formula = self.truth_value_at(eval_point)
        truth_value = z3.is_true(self.model_structure.z3_model.evaluate(z3_formula))
        world_state = bitvec_to_substates(eval_point["world"], N)
        RESET, FULL, PART = self.set_colors(self.name, indent_num, truth_value, world_state, use_colors)
        print(
            f"{'  ' * indent_num}{FULL}|{self.name}| = {self}{RESET}"
            f"  {PART}({truth_value} in {world_state}){RESET}"
        )


class ExclusionStructure(model.ModelDefaults):
    """Model structure for exclusion semantics."""

    def __init__(self, model_constraints, combined_settings):
        """Initialize with proper constraint checking."""
        if not isinstance(model_constraints, model.ModelConstraints):
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
        """Update model structure from Z3 model."""
        evaluate = z3_model.evaluate
        self.main_world = self.main_point["world"]
        self.main_point["world"] = z3_model[self.main_world]
        
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
        
        # Update conflicts/exclusion data
        self.z3_excludes = [
            (bit_x, bit_y)
            for bit_x in self.all_states
            for bit_y in self.all_states
            if z3.is_true(evaluate(self.semantics.excludes(bit_x, bit_y)))
        ]

    def true_at(self, sentence, eval_point):
        """Delegate to semantics for truth evaluation."""
        return self.semantics.true_at(sentence, eval_point)
    
    def extended_verify(self, state, sentence, eval_point):
        """Delegate to semantics for extended verification."""
        return self.semantics.extended_verify(state, sentence, eval_point)

    def find_verifying_states(self, sentence, eval_point):
        """Find states that verify the sentence at evaluation point."""
        result = set()
        for state in self.all_states:
            constraint = self.extended_verify(state, sentence, eval_point)
            if z3.is_true(self.z3_model.evaluate(constraint)):
                result.add(state)
        return result

    def interpret_verify(self, atom):
        """Interpret the verify relation for an atom."""
        result = set()
        for state in self.all_states:
            constraint = self.semantics.verify(state, atom)
            if z3.is_true(self.z3_model.evaluate(constraint)):
                result.add(state)
        return result

    def interpret_excludes(self):
        """Interpret the excludes relation."""
        result = {}
        for state_x in self.all_states:
            result[state_x] = set()
            for state_y in self.all_states:
                constraint = self.semantics.excludes(state_x, state_y)
                if z3.is_true(self.z3_model.evaluate(constraint)):
                    result[state_x].add(state_y)
        return result
    
    def print_to(self, default_settings, example_name, theory_name, print_constraints=None, output=sys.__stdout__):
        """Print the model details to the specified output stream.
        
        This method provides compatibility with the framework's expected interface
        by delegating to the print_all method.
        
        Args:
            default_settings (dict): Default configuration settings for the model
            example_name (str): Name of the example being evaluated
            theory_name (str): Name of the logical theory being used
            print_constraints (bool, optional): Whether to print model constraints.
            output (TextIO, optional): Output stream to write to. Defaults to sys.stdout.
        """
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
            self.print_exclusion(output)
            self.print_evaluation(output)
            self.print_input_sentences(output)
            self.print_model(output)
            if output is sys.__stdout__:
                total_time = round(time.time() - self.start_time, 4) 
                print(f"Total Run Time: {total_time} seconds\n", file=output)
                print(f"{'='*40}", file=output)
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
                
    def print_exclusion(self, output=sys.__stdout__):
        """Print exclusion relationships."""
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
        
        # Filter and print conflicts/exclusions
        filtered_excludes = [(x, y) for x, y in self.z3_excludes if should_include_state(x) and should_include_state(y)]
        if filtered_excludes:
            print("\nExcludes", file=output)
            for bit_x, bit_y in filtered_excludes:
                state_x = bitvec_to_substates(bit_x, self.N)
                state_y = bitvec_to_substates(bit_y, self.N)
                color_x = get_state_color(bit_x)
                color_y = get_state_color(bit_y)
                print(f"  {WHITE}{color_x}{state_x}{WHITE} ✖ {color_y}{state_y}{RESET}", file=output)
        else:
            print("\nExcludes\n  (none)", file=output)
            
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