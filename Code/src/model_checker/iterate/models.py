"""Model creation and validation for iteration.

This module handles building new model structures from Z3 models,
managing model interpretation, and validating model constraints.
"""

import logging
import z3

logger = logging.getLogger(__name__)


class ModelBuilder:
    """Builds and validates model structures for iteration."""
    
    def __init__(self, build_example):
        """Initialize model builder.
        
        Args:
            build_example: Original BuildExample instance
        """
        self.build_example = build_example
    
    def build_new_model_structure(self, z3_model):
        """Build a new model structure with fresh constraints.
        
        This creates new ModelConstraints using the current model's verify/falsify
        functions, ensuring constraint consistency for MODEL 2+.
        
        Args:
            z3_model: Z3 model to use for the new structure
            
        Returns:
            ModelStructure: A new model structure with fresh constraints
        """
        try:
            # Import required modules
            from model_checker.syntactic import Syntax
            from model_checker.models.constraints import ModelConstraints
            import z3
            
            # Get original build example components
            original_build = self.build_example
            settings = original_build.settings.copy()
            
            # Create fresh syntax (reuses sentence parsing)
            syntax = Syntax(
                original_build.premises,
                original_build.conclusions,
                original_build.semantic_theory.get("operators")
            )
            
            # Create new semantics WITHOUT state transfer
            semantics_class = original_build.semantic_theory["semantics"]
            semantics = semantics_class(settings)
            
            # Create fresh ModelConstraints with current context
            proposition_class = original_build.semantic_theory["proposition"]
            model_constraints = ModelConstraints(
                settings,
                syntax,
                semantics,
                proposition_class
            )
            
            # We need to inject the concrete constraints into the model constraints
            # BEFORE creating the model structure, so it solves with them included
            
            # Get semantics from model_constraints
            semantics = model_constraints.semantics
            
            # Create a new solver with the base constraints AND concrete values
            temp_solver = z3.Solver()
            
            # Add the base constraints from model_constraints
            for constraint in model_constraints.all_constraints:
                temp_solver.add(constraint)
            
            # Extract concrete values from Z3 model and add them as constraints
            # Constrain world states
            for state in range(2**semantics.N):
                # Is this state a world in the iterator model?
                is_world_val = z3_model.eval(semantics.is_world(state), model_completion=True)
                if z3.is_true(is_world_val):
                    temp_solver.add(semantics.is_world(state))
                else:
                    temp_solver.add(z3.Not(semantics.is_world(state)))
                
                # Is this state possible in the iterator model?
                is_possible_val = z3_model.eval(semantics.possible(state), model_completion=True)
                if z3.is_true(is_possible_val):
                    temp_solver.add(semantics.possible(state))
                else:
                    temp_solver.add(z3.Not(semantics.possible(state)))
            
            # Constrain verify/falsify for sentence letters
            for letter_obj in syntax.sentence_letters:
                if hasattr(letter_obj, 'sentence_letter'):
                    atom = letter_obj.sentence_letter
                    for state in range(2**semantics.N):
                        # Verify value
                        verify_val = z3_model.eval(semantics.verify(state, atom), model_completion=True)
                        if z3.is_true(verify_val):
                            temp_solver.add(semantics.verify(state, atom))
                        else:
                            temp_solver.add(z3.Not(semantics.verify(state, atom)))
                        
                        # Falsify value (if it exists)
                        if hasattr(semantics, 'falsify'):
                            falsify_val = z3_model.eval(semantics.falsify(state, atom), model_completion=True)
                            if z3.is_true(falsify_val):
                                temp_solver.add(semantics.falsify(state, atom))
                            else:
                                temp_solver.add(z3.Not(semantics.falsify(state, atom)))
            
            # Store the constraints in model_constraints so the model will use them
            model_constraints.all_constraints = list(temp_solver.assertions())
            
            # Now create the model structure which will solve with all constraints
            model_structure_class = original_build.model_structure_class
            model_structure = model_structure_class(model_constraints, settings)
            
            # The model structure constructor already solved with all constraints
            # Check if it was successful
            if not model_structure.z3_model_status:
                logger.warning("Model structure creation was not successful")
                return None
            
            # Interpret the premises and conclusions
            all_sentences = syntax.premises + syntax.conclusions
            model_structure.interpret(all_sentences)
            
            return model_structure
            
        except Exception as e:
            logger.error(f"Failed to build model structure: {str(e)}")
            return None
    
    def _initialize_base_attributes(self, model_structure, model_constraints, settings):
        """Initialize basic model structure attributes.
        
        Args:
            model_structure: Model structure to initialize
            model_constraints: Model constraints object
            settings: Model settings dictionary
        """
        # Set basic attributes from model constraints
        model_structure.settings = settings
        model_structure.model_constraints = model_constraints
        model_structure.semantics = model_constraints.semantics
        
        # Initialize collections
        model_structure.z3_atoms = []
        model_structure.z3_sentence_letters = []
        model_structure.z3_worlds = []
        model_structure.z3_world_states = []
        model_structure.z3_possible_states = []
        model_structure.z3_impossible_states = []
        
        # Initialize interpretation results
        model_structure.premises = []
        model_structure.conclusions = []
        
        # Set solver reference
        model_structure.solver = model_constraints.solver if hasattr(model_constraints, 'solver') else None
    
    def _initialize_z3_dependent_attributes(self, model_structure, z3_model):
        """Initialize attributes that depend on the Z3 model.
        
        Args:
            model_structure: Model structure to initialize  
            z3_model: Z3 model to extract values from
        """
        try:
            semantics = model_structure.semantics
            N = model_structure.settings.get('N', 3)
            
            # Initialize state collections
            world_states = []
            possible_states = []
            impossible_states = []
            
            # Evaluate states using Z3 model
            for state in range(N):
                try:
                    if hasattr(semantics, 'is_world'):
                        # Check if this state is a world
                        is_world_val = self._evaluate_z3_boolean(z3_model, semantics.is_world(state))
                        if is_world_val:
                            world_states.append(state)
                    
                    if hasattr(semantics, 'possible'):
                        # Check if this state is possible
                        is_possible_val = self._evaluate_z3_boolean(z3_model, semantics.possible(state))
                        if is_possible_val:
                            possible_states.append(state)
                        else:
                            impossible_states.append(state)
                            
                except Exception as e:
                    logger.warning(f"Error evaluating state {state}: {e}")
                    continue
            
            # Set the collections
            model_structure.z3_world_states = world_states
            model_structure.z3_possible_states = possible_states
            model_structure.z3_impossible_states = impossible_states
            
            # Also store as attribute for compatibility
            model_structure.z3_worlds = world_states
            
        except Exception as e:
            logger.warning(f"Error initializing Z3-dependent attributes: {e}")
    
    def _evaluate_z3_boolean(self, z3_model, expression):
        """Safely evaluate a Z3 boolean expression.
        
        Args:
            z3_model: Z3 model to use for evaluation
            expression: Z3 expression to evaluate
            
        Returns:
            bool: Evaluation result, defaults to False on error
        """
        try:
            if expression is None:
                return False
                
            # Use Z3 model evaluation with completion
            result = z3_model.eval(expression, model_completion=True)
            
            # Check if the result is a Z3 boolean
            if z3.is_bool(result):
                return z3.is_true(result)
            
            # Handle numeric results (0 = False, non-zero = True)
            if z3.is_int_value(result) or z3.is_real_value(result):
                try:
                    numeric_val = result.as_long() if z3.is_int_value(result) else float(result.as_decimal(6).replace('?', ''))
                    return numeric_val != 0
                except:
                    return False
            
            # Handle string representation as fallback
            result_str = str(result).strip()
            if result_str.lower() in ['true', '1']:
                return True
            elif result_str.lower() in ['false', '0']:
                return False
                
            logger.debug(f"Unknown Z3 result type for {expression}: {result} (type: {type(result)})")
            return False
            
        except Exception as e:
            logger.warning(f"Error evaluating Z3 expression {expression}: {e}")
            return False