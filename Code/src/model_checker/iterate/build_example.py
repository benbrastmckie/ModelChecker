"""BuildExample extension for model iteration support.

This module provides IteratorBuildExample which extends BuildExample
to support creating models with pre-existing Z3 values during iteration.
This class is completely theory-agnostic - all theory-specific logic
is delegated to the theory's semantics class.
"""

from model_checker.builder.example import BuildExample
from model_checker.syntactic import Syntax
from model_checker.models.constraints import ModelConstraints


class IteratorBuildExample(BuildExample):
    """Extended BuildExample with iteration support.
    
    This class adds methods for creating models during iteration
    with pre-existing Z3 values. It remains completely theory-agnostic,
    delegating all theory-specific injection to the semantics classes.
    
    The class uses a factory function to create instances without going
    through the normal BuildExample initialization, allowing precise
    control over the model building process for iteration.
    """
    
    def __init__(self):
        """Initialize without calling BuildExample.__init__.
        
        This empty init is intentional - we use factory functions to
        create properly initialized instances.
        """
        pass
    
    def _copy_from_original(self, original):
        """Copy necessary attributes from original BuildExample.
        
        This copies all the configuration needed to build a new model
        while avoiding any mutable state that could cause issues.
        
        Args:
            original: Original BuildExample to copy from
        """
        # Copy immutable configuration
        self.build_module = original.build_module
        self.semantic_theory = original.semantic_theory
        self.semantics = original.semantics
        self.proposition = original.proposition
        self.operators = original.operators
        self.model_structure_class = original.model_structure_class
        
        # Copy example definition
        self.premises = original.premises
        self.conclusions = original.conclusions
        
        # Deep copy settings to avoid mutation
        self.settings = original.settings.copy()
        
        # Copy settings manager for validation
        self.settings_manager = original.settings_manager
        
        # Store reference to original for debugging
        self._original_build = original
    
    def _build_with_injection(self, z3_model):
        """Build model structure with Z3 value injection.
        
        This creates all fresh components and delegates injection
        to the theory-specific semantics class.
        
        Args:
            z3_model: Z3 model with values to inject
        """
        # Create fresh syntax (reuses sentence parsing)
        self.example_syntax = Syntax(
            self.premises,
            self.conclusions,
            self.operators
        )
        
        # Create fresh semantics instance
        self.example_semantics = self.semantics(self.settings)
        
        # Create model constraints
        self.model_constraints = ModelConstraints(
            self.settings,
            self.example_syntax,
            self.example_semantics,
            self.proposition
        )
        
        # Get original semantics for Z3 function evaluation
        original_semantics = self._original_build.model_constraints.semantics
        
        # Delegate injection to theory-specific code
        # This is where theory concepts are handled
        self.model_constraints.inject_z3_values(z3_model, original_semantics)
        
        # Create model structure with injected constraints
        self.model_structure = self.model_structure_class(
            self.model_constraints,
            self.settings
        )
        
        # Store Z3 model for reference
        self.model_structure.z3_model = z3_model
        
        # Mark as iteration model for debugging
        self.model_structure._is_iteration_model = True
        
        # Interpret sentences in the new model
        self._interpret_sentences()
    
    def _interpret_sentences(self):
        """Interpret sentences in the new model structure.
        
        This finalizes the model by interpreting all sentences
        according to the injected values.
        """
        sentence_objects = (self.model_structure.premises + 
                          self.model_structure.conclusions)
        self.model_structure.interpret(sentence_objects)
        
        # Store solver reference as BuildExample does
        self.solver = self.model_structure.solver


def create_with_z3_model(original_build, z3_model):
    """Create a new model structure with Z3 value injection.
    
    This factory function creates a new IteratorBuildExample instance
    that reuses the configuration from an original BuildExample but
    creates a new model with specific Z3 values injected.
    
    Args:
        original_build: Original BuildExample with initial model
        z3_model: Z3 model with concrete values to inject
        
    Returns:
        IteratorBuildExample instance with new model structure
        
    Note:
        This function is completely theory-agnostic. All theory-specific
        injection logic is handled by the theory's semantics class.
    """
    # Create instance without normal initialization
    instance = IteratorBuildExample()
    
    # Copy configuration from original
    instance._copy_from_original(original_build)
    
    # Build new model with Z3 injection
    instance._build_with_injection(z3_model)
    
    return instance