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
        "derive_imposition": False,  # Theory-specific setting
    }

    def __init__(self, settings):
        # Merge settings with defaults
        combined_settings = {}
        combined_settings.update(self.DEFAULT_EXAMPLE_SETTINGS)
        combined_settings.update(self.DEFAULT_GENERAL_SETTINGS)
        combined_settings.update(settings)  # User settings override defaults
        
        # Initialize the parent LogosSemantics with combined_settings
        super().__init__(combined_settings=combined_settings)
        
        # Store derive_imposition setting
        self.derive_imposition = combined_settings.get('derive_imposition', False)
        
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
            z3.BoolSort()           # truth-value
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

        self.imposition_constraints = [
            inclusion,
            actuality,
            incorporation,
            completeness,
        ]

        # Check if we should derive imposition constraints
        if self.derive_imposition:
            # Use derived constraints instead of primitive imposition constraints
            self.imposition_constraints = self._derive_imposition()
            # Make premise and conclusion behaviors trivial (always true)
            # This ensures only the negated derived constraints contribute
            self.premise_behavior = lambda premise: z3.BoolVal(True)
            self.conclusion_behavior = lambda conclusion: z3.BoolVal(True)
        else:
            # Use normal imposition constraints and behaviors
            self.premise_behavior = lambda premise: self.true_at(premise, self.main_point)
            self.conclusion_behavior = lambda conclusion: self.false_at(conclusion, self.main_point)

        # Set frame constraints
        self.frame_constraints = [
            possibility_downard_closure,
            is_main_world,
        ] + self.imposition_constraints

    def alt_imposition(self, state_y, state_w, state_u):
        """Determines if a state_u is an alternative world resulting from
        imposing state_y on state_w.
        
        This method permutes the arguments to provide an exact analog of the 
        primitive imposition relation."""

        return self.is_alternative(state_u, state_y, state_w)

    def _derive_imposition(self):
        """Given the definition of `is_alternative`, we may derive analogs
        of the frame constraints for imposition.
        
        When derive_imposition=True, this method returns the disjunction of negated
        derived constraints. This tests whether all derived constraints are entailed
        by the base imposition semantics. If Z3 finds no model (as expected), it
        proves that the frame constraints on primitive imposition fully entail all
        properties that would be imposed by the constructive is_alternative definition."""

        # Define the frame constraints
        x, y, z, u = z3.BitVecs("frame_x frame_y, frame_z, frame_u", self.N)
        alt_inclusion = ForAll(
            [x, y, z],
            z3.Implies(
                self.alt_imposition(x, y, z),
                self.is_part_of(x, z)
            )
        )
        alt_actuality = ForAll(
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
                        self.alt_imposition(x, y, z),
                    )
                )
            )
        )
        alt_incorporation = ForAll(
            [x, y, z, u],
            z3.Implies(
                z3.And(
                    self.alt_imposition(x, y, z),
                    self.is_part_of(u, z)
                ),
                self.alt_imposition(self.fusion(x, u), y, z)
            )
        )
        alt_completeness = ForAll(
            [x, y, z],
            z3.Implies(
                self.alt_imposition(x, y, z),
                self.is_world(z)
            )
        )

        # Negation of at least one of the derived constraints
        neg_alt_constraints = z3.Or(
            z3.Not(alt_inclusion),
            z3.Not(alt_actuality),
            z3.Not(alt_incorporation),
            z3.Not(alt_completeness),
        )

        # Return a list to combine
        return [neg_alt_constraints]

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
                return False
                
        except Exception as e:
            return False
    
    def _update_imposition_relations(self):
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
            # Always print closing separator for countermodels
            print(f"\n{'='*40}", file=output)
            return
    
    def print_imposition(self, output=sys.__stdout__):
        """Print imposition relations in the format 'a ->_w u'."""
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
                
                # Print in format: a ->_w u (meaning: u is the outcome of imposing a on w)
                print(f"  {state_color}{state_str}{RESET} →_{world_color}{world_str}{RESET} {outcome_color}{outcome_str}{RESET}", file=output)
    
    def extract_states(self):
        """Extract categorized states for output."""
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
    
    def extract_evaluation_world(self):
        """Extract the main evaluation world."""
        if hasattr(self.semantics, 'main_world') and self.semantics.main_world is not None:
            world_val = self.semantics.main_world
            if hasattr(world_val, 'as_long'):
                world_val = world_val.as_long()
            return f"s{world_val}"
        return None
    
    def extract_relations(self):
        """Extract imposition relations."""
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
    
    def extract_propositions(self):
        """Extract proposition truth values at states."""
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
    
    def initialize_from_z3_model(self, z3_model):
        """Initialize imposition-specific attributes from Z3 model.
        
        This method is called by the iterator when creating new model structures.
        """
        # Store the Z3 model first
        self.z3_model = z3_model
        
        # Call comprehensive model structure update like exclusion theory does
        # This also handles proposition initialization
        self._update_model_structure(z3_model)
    
    def _update_model_structure(self, z3_model):
        """Update model structure from Z3 model, including semantic relations.
        
        This method ensures all Z3-dependent attributes are correctly set
        based on the provided Z3 model, following the pattern used by
        the exclusion theory.
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
                return False
                
        except Exception:
            return False
    
    def print_model_differences(self, output=sys.__stdout__):
        """Print imposition theory differences."""
        if not hasattr(self, 'model_differences') or not self.model_differences:
            return
        
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
