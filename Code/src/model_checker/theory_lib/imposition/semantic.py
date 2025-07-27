##########################
### DEFINE THE IMPORTS ###
##########################

import z3
import sys
import time

from model_checker.theory_lib.logos import LogosSemantics, LogosModelStructure
from model_checker.utils import (
    ForAll,
    Exists,
    bitvec_to_substates,
)



##############################################################################
######################### SEMANTICS AND PROPOSITIONS #########################
##############################################################################

class ImpositionSemantics(LogosSemantics):
    """
    Kit Fine's imposition semantics as an independent theory.
    
    Inherits logos base functionality for consistency and code reuse,
    while implementing Fine's distinctive counterfactual semantics
    through the imposition operation. Developed as a separate theory
    for comparison with Brast-McKie hyperintensional semantics.
    
    This theory extends LogosSemantics with:
    - The imposition operation for counterfactual reasoning
    - Alternative world calculation based on imposition
    - Fine's specific semantic constraints
    """

    DEFAULT_EXAMPLE_SETTINGS = {
        'N' : 3,
        'contingent' : False,
        'non_empty' : False,
        'non_null' : False,
        'disjoint' : False,
        'max_time' : 1,
        'iterate' : 1,
        'expectation' : None,
    }
    
    # Default general settings for the imposition theory
    DEFAULT_GENERAL_SETTINGS = {
        "print_impossible": False,
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,
        "maximize": False,
    }

    def __init__(self, settings):
        # Merge settings with defaults
        combined_settings = {}
        combined_settings.update(self.DEFAULT_EXAMPLE_SETTINGS)
        combined_settings.update(self.DEFAULT_GENERAL_SETTINGS)
        combined_settings.update(settings)  # User settings override defaults
        
        # Initialize the parent LogosSemantics with combined_settings
        super().__init__(combined_settings=combined_settings)
        
        # Define imposition-specific operations
        self._define_imposition_operation()
    
    def _define_imposition_operation(self):
        """Define the imposition operation as a Z3 function."""
        # Define the imposition function for Fine's semantics
        self.imposition = z3.Function(
            "imposition",
            z3.BitVecSort(self.N),  # state imposed
            z3.BitVecSort(self.N),  # world being imposed on
            z3.BitVecSort(self.N),  # outcome world
            z3.BoolSort()           # boolean result
        )

        # Define the frame constraints
        x, y, z, u = z3.BitVecs("frame_x frame_y, frame_z, frame_u", self.N)
        possibility_downard_closure = ForAll(
            [x, y],
            z3.Implies(z3.And(self.possible(y), self.is_part_of(x, y)), self.possible(x)),
        )
        is_main_world = self.is_world(self.main_world)
        inclusion = ForAll(
            [x, y, z],
            z3.Implies(
                self.imposition(x, y, z),
                self.is_part_of(x, z)
            )
        )
        actuality = ForAll(
            [x, y],
            z3.Implies(
                z3.And(
                    self.is_part_of(x, y),
                    self.is_world(y)
                ),
                Exists(
                    z,
                    z3.And(
                        self.is_part_of(z, y),
                        self.imposition(x, y, z),
                    )
                )
            )
        )
        incorporation = ForAll(
            [x, y, z, u],
            z3.Implies(
                z3.And(
                    self.imposition(x, y, z),
                    self.is_part_of(u, z)
                ),
                self.imposition(self.fusion(x, u), y, z)
            )
        )
        completeness = ForAll(
            [x, y, z],
            z3.Implies(
                self.imposition(x, y, z),
                self.is_world(z)
            )
        )

        # Set frame constraints
        self.frame_constraints = [
            possibility_downard_closure,
            is_main_world,
            inclusion,
            actuality,
            incorporation,
            completeness,
        ]

        # Define invalidity conditions
        self.premise_behavior = lambda premise: self.true_at(premise, self.main_point)
        self.conclusion_behavior = lambda conclusion: self.false_at(conclusion, self.main_point)

    # TODO: can this be removed (its in logos semantics)
    def extended_verify(self, state, sentence, eval_point):
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            return self.verify(state, sentence_letter)
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.extended_verify(state, *arguments, eval_point)
    
    # TODO: can this be removed (its in logos semantics)
    def extended_falsify(self, state, sentence, eval_point):
        sentence_letter = sentence.sentence_letter
        if sentence_letter is not None:
            return self.falsify(state, sentence_letter)
        operator = sentence.operator
        arguments = sentence.arguments or ()
        return operator.extended_falsify(state, *arguments, eval_point)

    def calculate_outcome_worlds(self, verifiers, eval_point, model_structure):
        """Calculate alternative worlds given verifiers and eval_point."""
        eval = model_structure.z3_model.evaluate
        world_states = model_structure.z3_world_states
        eval_world = eval_point["world"]
        return {
            pw for ver in verifiers
            for pw in world_states
            if eval(self.imposition(ver, eval_world, pw))
        }


class ImpositionModelStructure(LogosModelStructure):
    """
    Model structure for imposition theory that extends LogosModelStructure
    with imposition relation printing capabilities.
    """
    
    def __init__(self, model_constraints, settings):
        super().__init__(model_constraints, settings)
        
        # Initialize imposition relations storage
        self.z3_imposition_relations = []
        
        # Only evaluate if we have a valid model
        if self.z3_model_status and self.z3_model is not None:
            self._update_imposition_relations()
    
    def _update_imposition_relations(self):
        """Extract imposition relations from the Z3 model."""
        if not hasattr(self.semantics, 'imposition'):
            return
            
        evaluate = self.z3_model.evaluate
        
        # Find all imposition triples (state, world, outcome)
        self.z3_imposition_relations = []
        
        for state in self.all_states:
            for world in self.z3_world_states:
                for outcome in self.z3_world_states:
                    try:
                        if z3.is_true(evaluate(self.semantics.imposition(state, world, outcome))):
                            self.z3_imposition_relations.append((state, world, outcome))
                    except:
                        pass
    
    def print_all(self, default_settings, example_name, theory_name, output=sys.__stdout__):
        """Print model including imposition relations."""
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
                print(f"{'='*40}", file=output)
            return
    
    def print_imposition(self, output=sys.__stdout__):
        """Print imposition relations in the format 'w ->_a u'."""
        if not self.z3_imposition_relations:
            return
            
        print("\nImposition Relation:", file=output)
        
        # Set up colors if outputting to stdout
        use_colors = output is sys.__stdout__
        WHITE = "\033[37m" if use_colors else ""
        RESET = "\033[0m" if use_colors else ""
        WORLD_COLOR = "\033[34m" if use_colors else ""
        POSSIBLE_COLOR = "\033[36m" if use_colors else ""
        
        def get_state_color(bit):
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
                
                # Print in format: w ->_a u (meaning: u is the outcome of imposing a on w)
                print(f"  {world_color}{world_str}{RESET} →_{state_color}{state_str}{RESET} {outcome_color}{outcome_str}{RESET}", file=output)
    
    def initialize_from_z3_model(self, z3_model):
        """Initialize imposition-specific attributes from Z3 model.
        
        This method is called by the iterator when creating new model structures.
        """
        # First call parent initialization
        super().initialize_from_z3_model(z3_model)
        
        # Then update imposition relations
        self._update_imposition_relations()
    
    def print_model_differences(self, output=sys.__stdout__):
        """Print differences including imposition relation changes."""
        # First call parent implementation
        if not super().print_model_differences(output):
            return False
        
        # Add imposition-specific differences
        if hasattr(self, 'model_differences') and self.model_differences:
            imp_diffs = self.model_differences.get('imposition_relations', {})
            
            if imp_diffs:
                print(f"\n{self.COLORS['world']}Imposition Changes:{self.RESET}", file=output)
                for relation, change in imp_diffs.items():
                    if change.get('new'):
                        print(f"  {self.COLORS['possible']}+ {relation}{self.RESET}", file=output)
                    else:
                        print(f"  {self.COLORS['impossible']}- {relation}{self.RESET}", file=output)
        
        return True
