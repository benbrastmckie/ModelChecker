"""
Witness Array Exclusion Semantics

This implementation attempts to solve the Skolem function accessibility problem
by using Z3 arrays to store witness mappings, making them accessible during 
Phase 2 truth evaluation.

Key Innovation:
- Replace Skolem functions h_sk and y_sk with Z3 arrays h_array and y_array
- Arrays become part of the model and can be queried after solving
- Maintains exact three-condition exclusion semantics
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


class WitnessArraySemantics(model.SemanticDefaults):
    """
    Exclusion semantics using witness arrays for existential witness storage.
    
    This implementation replaces Skolem functions with Z3 arrays to make
    witness mappings accessible during verification phase.
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

        # Counter for unique naming
        self.counter = 0
        
        # Storage for witness arrays
        self.witness_arrays = {}
        self.array_counter = 0
        
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

    def create_witness_arrays(self, array_id):
        """
        Create witness arrays for an exclusion instance.
        
        Returns:
            tuple: (h_array, y_array) where:
                - h_array: Maps verifiers to their exclusion states
                - y_array: Maps verifiers to their witness parts
        """
        N = self.N
        h_array = z3.Array(f"h_array_{array_id}", z3.BitVecSort(N), z3.BitVecSort(N))
        y_array = z3.Array(f"y_array_{array_id}", z3.BitVecSort(N), z3.BitVecSort(N))
        return h_array, y_array

    def store_witness_arrays(self, array_id, h_array, y_array, argument, state):
        """Store witness array information for later retrieval."""
        self.witness_arrays[array_id] = {
            'h_array': h_array,
            'y_array': y_array,
            'argument': argument,
            'state': state,
            'array_id': array_id
        }

    def extract_array_values(self, model, array, domain_size):
        """Extract all values from a Z3 array in the model."""
        values = {}
        for i in range(2**domain_size):
            idx = z3.BitVecVal(i, domain_size)
            try:
                val = model.evaluate(array[idx], model_completion=True)
                if val is not None:
                    values[i] = val.as_long()
                else:
                    values[i] = 0  # Default value for undefined entries
            except:
                values[i] = 0  # Handle any evaluation errors
        return values

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
            v = z3.BitVec(f"v_nonempty_{letter_id}", N)
            atom_constraints.append(
                Exists([v], verify(v, sentence_letters[letter_id]))
            )
        
        # Non-null constraint
        if non_null:
            atom_constraints.append(
                z3.Not(verify(self.null_state, sentence_letters[letter_id]))
            )
        
        # Contingency constraint
        if contingent:
            # Ensure both verifiers and non-verifiers exist
            v = z3.BitVec(f"v_cont_{letter_id}", N)
            nv = z3.BitVec(f"nv_cont_{letter_id}", N)
            atom_constraints.extend([
                Exists([v], verify(v, sentence_letters[letter_id])),
                Exists([nv], z3.Not(verify(nv, sentence_letters[letter_id])))
            ])
        
        # Disjoint constraint
        if disjoint and letter_id > 0:
            # This atom is disjoint from all previous atoms
            for prev_id in range(letter_id):
                v = z3.BitVec(f"v_disj_{letter_id}_{prev_id}", N)
                atom_constraints.append(
                    ForAll([v], z3.Not(z3.And(
                        verify(v, sentence_letters[letter_id]),
                        verify(v, sentence_letters[prev_id])
                    )))
                )
        
        return atom_constraints

    def _premise_behavior_method(self, premise):
        """Premise must be true at main evaluation point."""
        return self.true_at(premise, self.main_point)

    def _conclusion_behavior_method(self, conclusion):
        """Conclusion must be false at main evaluation point."""
        return z3.Not(self.true_at(conclusion, self.main_point))

    # Print methods (simplified versions)
    def print_to(self, output=sys.__stdout__):
        """Print all semantic information."""
        self.print_states(output)
        self.print_exclusion(output)
        self.print_evaluation(output)

    def print_all(self, output=sys.__stdout__):
        """Print all information including constraints."""
        self.print_to(output)

    def print_states(self, output=sys.__stdout__):
        """Print state information."""
        # Set up colors
        use_colors = output is sys.__stdout__
        WHITE = self.COLORS["default"] if use_colors else ""
        RESET = self.RESET if use_colors else ""
        WORLD_COLOR = self.COLORS["world"] if use_colors else ""
        POSSIBLE_COLOR = self.COLORS["possible"] if use_colors else ""
        IMPOSSIBLE_COLOR = self.COLORS["impossible"] if use_colors else ""
        
        def get_state_color(bit):
            if hasattr(self, 'z3_world_states') and bit in self.z3_world_states:
                return WORLD_COLOR
            elif hasattr(self, 'z3_possible_states') and bit in self.z3_possible_states:
                return POSSIBLE_COLOR
            else:
                return IMPOSSIBLE_COLOR
                
        def should_include_state(bit):
            # Check if we should include this state based on print_impossible setting
            return (bit == 0 or 
                   (hasattr(self, 'z3_possible_states') and bit in self.z3_possible_states) or 
                   (hasattr(self, 'z3_world_states') and bit in self.z3_world_states) or 
                   self.settings.get('print_impossible', False))
        
        print(f"\nState Space", file=output)
        for bit in range(2**self.N):
            if should_include_state(bit):
                state = bitvec_to_substates(bit, self.N)
                color = get_state_color(bit)
                binary = int_to_binary(bit, self.N)
                print(f"  {WHITE}{color}{state} #{binary}{RESET}", file=output)
                
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
            if hasattr(self, 'z3_world_states') and bit in self.z3_world_states:
                return WORLD_COLOR
            elif hasattr(self, 'z3_possible_states') and bit in self.z3_possible_states:
                return POSSIBLE_COLOR
            else:
                return IMPOSSIBLE_COLOR
                
        def should_include_state(bit):
            return (bit == 0 or 
                   (hasattr(self, 'z3_possible_states') and bit in self.z3_possible_states) or 
                   (hasattr(self, 'z3_world_states') and bit in self.z3_world_states) or 
                   self.settings.get('print_impossible', False))
        
        # Filter and print conflicts/exclusions
        if hasattr(self, 'z3_excludes'):
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
            file=output
        )