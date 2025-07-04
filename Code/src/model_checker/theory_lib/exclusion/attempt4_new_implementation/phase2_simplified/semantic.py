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
        N = self.model_structure.semantics.N
        truth_value = self.truth_value_at(eval_point)
        world_state = bitvec_to_substates(eval_point["world"], N)
        RESET, FULL, PART = self.set_colors(
            self.name, indent_num, truth_value, world_state, use_colors
        )
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
        
        # Update impossible states
        self.z3_impossible_states = [
            i for i in range(len(self.all_states)) 
            if i not in self.z3_possible_states
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