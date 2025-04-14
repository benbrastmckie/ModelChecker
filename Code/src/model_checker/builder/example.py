"""BuildExample implementation for handling individual model checking examples.

This module provides the BuildExample class for constructing and evaluating 
individual model checking examples. It handles model construction, constraint 
generation, and result evaluation.
"""

import z3
import sys
import os

from model_checker.model import (
    SemanticDefaults,
    PropositionDefaults,
    ModelConstraints,
    ModelDefaults,
)
from model_checker.syntactic import (
    OperatorCollection,
    Syntax,
)
from model_checker.builder.validation import (
    validate_semantic_theory,
    validate_example_case,
)
from model_checker.builder.z3_utils import (
    create_difference_constraint,
    extract_model_values,
    find_next_model as find_next_z3_model
)

class BuildExample:
    """Handles the creation and evaluation of a single model checking example.
    
    This class takes a semantic theory and an example case (premises, conclusions, and settings),
    constructs a logical model, and evaluates the validity of the argument.
    
    Attributes:
        build_module: The parent module managing the model checking process
        semantic_theory: The semantic theory implementation to use
        semantics: The class implementing the semantic theory
        proposition: The class implementing propositions
        operators: The collection of logical operators
        model_structure_class: The class implementing the model structure
        premises: The premise sentences
        conclusions: The conclusion sentences
        settings: Configuration settings for the model
        model_structure: The resulting model structure after solving
    """

    def __init__(self, build_module, semantic_theory, example_case):
        """Initialize a model checking example.
        
        Args:
            build_module: Parent BuildModule instance
            semantic_theory: Dictionary containing the semantic theory implementation
            example_case: List containing [premises, conclusions, settings]
            
        Raises:
            TypeError: If parameters are invalid
            AttributeError: If required components are missing
        """
        from model_checker.settings import SettingsManager
        
        # Store build_module reference
        self.build_module = build_module
        
        # Validate and extract components from semantic_theory
        self.semantics, self.proposition, self.operators, self.model_structure_class = (
            validate_semantic_theory(semantic_theory)
        )
        self.semantic_theory = semantic_theory
        
        # Validate and extract components from example_case
        self.premises, self.conclusions, self.example_settings = validate_example_case(example_case)
        
        # Create settings manager for this theory
        self.settings_manager = SettingsManager(
            {"semantics": self.semantics},
            build_module.general_settings
        )
        
        # Get complete settings
        self.settings = self.settings_manager.get_complete_settings(
            build_module.general_settings,
            self.example_settings,
            build_module.module_flags
        )
        
        # Create syntax object
        self.example_syntax = Syntax(self.premises, self.conclusions, self.operators)
        
        # Create model constraints
        self.model_constraints = ModelConstraints(
            self.settings,
            self.example_syntax,
            self.semantics(self.settings),
            self.proposition,
        )
        
        # Create model structure
        self.model_structure = self.model_structure_class(
            self.model_constraints,
            self.settings,
        )
        
        # Interpret sentences
        sentence_objects = self.model_structure.premises + self.model_structure.conclusions
        self.model_structure.interpret(sentence_objects)
        
        # Store solver reference
        self.solver = self.model_structure.solver
    
    def get_result(self):
        """Get the result of the model checking.
        
        Returns:
            dict: Model data with structure:
                {
                    "model_found": bool,
                    "runtime": float,
                    "model_structure": dict of model internals
                }
                
        Raises:
            RuntimeError: If model checking has not been performed
        """
        if not hasattr(self, 'model_structure') or self.model_structure is None:
            raise RuntimeError("No model check has been performed")
            
        return {
            "model_found": self.model_structure.z3_model_status,
            "runtime": self.model_structure.z3_model_runtime,
            "model_structure": self._get_model_structure_data()
        }
    
    def _get_model_structure_data(self):
        """Extract relevant data from the model structure.
        
        Returns:
            dict: Model structure data in a serializable format
        """
        # Extract basic model information
        result = {
            "model_found": self.model_structure.z3_model_status,
            "runtime": self.model_structure.z3_model_runtime,
            "settings": self.settings
        }
        
        # Add model structure details if a model was found
        if self.model_structure.z3_model_status and self.model_structure.z3_model:
            # Most model structures will have num_worlds attribute
            if hasattr(self.model_structure, 'num_worlds'):
                result["worlds"] = self.model_structure.num_worlds
            # Add additional model details as needed
            
        return result
    
    def find_next_model(self):
        """Find a new model that differs from the previous one.
        
        Uses the refactored approach to find a semantically distinct model by:
        1. Creating extended constraints requiring difference from the current model
        2. Building a completely new model structure from scratch
        3. Calculating differences between the models for presentation
        
        Returns:
            bool: True if a new distinct model was found, False otherwise
        """
        if self.model_structure.z3_model is None:
            return False
            
        try:
            # Import the ModelIterator dynamically to avoid circular imports
            from model_checker.builder.iterate import ModelIterator
            
            # Create a model iterator for this build example
            iterator = ModelIterator(self)
            
            # Override to find just one more model
            iterator.max_iterations = 2  # Initial + 1 more
            
            # Find the next model
            model_structures = iterator.iterate()
            
            # Check if we found a new model
            if len(model_structures) <= 1:
                return False
                
            # Replace our model structure with the new one
            new_structure = model_structures[-1]
            
            # Keep a reference to the old structure for comparison
            old_structure = self.model_structure
            
            # Update the build example with the new structure
            self.model_structure = new_structure
            
            # We don't need to print differences here since they'll be printed by print_to
            # when the model is displayed through print_model
            
            return True
            
        except z3.Z3Exception as e:
            print(f"Z3 error while finding next model: {e}")
            return False
        except Exception as e:
            print(f"Error while finding next model: {e}")
            import traceback
            print(traceback.format_exc())
            return False
    
    def print_model(self, example_name=None, theory_name=None, output=sys.stdout):
        """Print model to specified output.
        
        Args:
            example_name: Name of the example (optional)
            theory_name: Name of the theory (optional)
            output: Output stream (defaults to stdout)
            
        This is a separate method from get_result() to maintain separation
        of data generation and presentation.
        """
        result = self.get_result()
        
        # Print model details always using print_to
        # The print_to method will handle both model found and no model found cases
        # This maintains compatibility with the original implementation
        self.model_structure.print_to(
            self.settings, 
            example_name or "example", 
            theory_name or "theory",
            output=output
        )
    
    def save_or_append(self, file_name, save_constraints=False, example_name=None, theory_name=None):
        """Save or append model output to a file.
        
        Args:
            file_name: Target filename (empty for append mode)
            save_constraints: Whether to include Z3 constraints in output
            example_name: Name of the example being saved
            theory_name: Name of the semantic theory used
            
        Returns:
            str: Path to the created or updated file
        """
        # Handle the case where file_name is None
        if file_name is None:
            return None
        
        example_name = example_name or "example"
        theory_name = theory_name or "theory"
        
        # Handle empty string (append to existing file)
        if len(file_name) == 0:
            # Append to module file
            module_path = self.build_module.module_path
            with open(module_path, 'a', encoding="utf-8") as f:
                print('\n"""', file=f)
                self.model_structure.print_to(
                    self.settings,
                    example_name, 
                    theory_name, 
                    save_constraints=save_constraints,
                    output=f
                )
                print('"""', file=f)
            print(f"\nAppended output to {module_path}")
            return module_path
        
        # Create new file
        project_name = getattr(self.build_module.module, 'module_name', 'project')
        destination_dir = os.path.join(os.getcwd(), project_name)
        
        # Ensure the directory exists
        os.makedirs(destination_dir, exist_ok=True)
        
        output_file = f"{destination_dir}/{file_name}.py"
        with open(output_file, 'w', encoding="utf-8") as f:
            print(f'# TITLE: {file_name}.py created in {destination_dir}\n"""', file=f)
            self.model_structure.print_to(
                self.settings,
                example_name, 
                theory_name, 
                save_constraints=save_constraints,
                output=f
            )
            print('"""', file=f)
        
        print(f'\n{file_name}.py created in {destination_dir}\n')
        return output_file
    
    def check_result(self):
        """Compare the model findings against expected model existence.
        
        Returns:
            bool: True if model findings match expectations, False otherwise.
        """
        model_expectation = self.settings.get("model", True)
        model_findings = self.model_structure.z3_model_status
        return model_findings == model_expectation