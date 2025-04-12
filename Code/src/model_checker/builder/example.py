"""BuildExample implementation for handling individual model checking examples.

This module provides the BuildExample class for constructing and evaluating 
individual model checking examples. It handles model construction, constraint 
generation, and result evaluation.
"""

import z3
import sys

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
        # This is a placeholder that will be expanded with actual model structure data
        # in a future implementation
        return {}
    
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
        
        # Print headers if names are provided
        if example_name and theory_name:
            print(f"EXAMPLE: {example_name}", file=output)
            print(f"THEORY: {theory_name}", file=output)
        
        # Print model status
        if result["model_found"]:
            print("MODEL FOUND", file=output)
        else:
            print("NO MODEL FOUND", file=output)
            
        # Print runtime
        print(f"Runtime: {result['runtime']:.4f} seconds", file=output)
        
        # Print model details if a model was found
        if result["model_found"] and self.model_structure.z3_model is not None:
            self.model_structure.print_to(
                self.settings, 
                example_name or "example", 
                theory_name or "theory",
                output=output
            )