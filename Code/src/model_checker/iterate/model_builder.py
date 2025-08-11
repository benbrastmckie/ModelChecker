"""Model building utilities for the iteration framework.

This module handles the construction of new model structures during
iteration, managing the complex two-phase building process.
"""

import z3
import logging
from typing import Optional, Any, Dict
import traceback

logger = logging.getLogger(__name__)


class IterationModelBuilder:
    """Builds new model structures during iteration.
    
    This class encapsulates the two-phase model building process:
    1. Constraint solving to get a Z3 model
    2. Model structure construction with the Z3 model
    """
    
    def __init__(self, build_example):
        """Initialize with the build example.
        
        Args:
            build_example: The BuildExample instance to use as template
        """
        self.build_example = build_example
        self.theory_module = self._get_theory_module()
    
    def _get_theory_module(self):
        """Get the theory module for model construction."""
        if hasattr(self.build_example, 'model_structure'):
            structure = self.build_example.model_structure
            if hasattr(structure, '__class__'):
                return structure.__class__.__module__
        return None
    
    def build_new_model_structure(self, z3_model: z3.ModelRef, 
                                attempt_number: int = 1,
                                total_attempts: int = 1) -> Optional[Any]:
        """Build a new model structure from a Z3 model.
        
        This method handles the complex process of constructing a new model
        structure that shares the same syntax and semantics as the original
        but uses the new Z3 model for concrete values.
        
        Args:
            z3_model: The Z3 model with new variable assignments
            attempt_number: Current attempt number (for debugging)
            total_attempts: Total attempts being made (for debugging)
            
        Returns:
            New model structure or None if construction fails
        """
        try:
            logger.debug(f"Building new model structure (attempt {attempt_number}/{total_attempts})")
            
            # Get the model structure class
            ModelStructureClass = self._get_model_structure_class()
            if not ModelStructureClass:
                logger.error("Could not determine model structure class")
                return None
            
            # Create new instances of syntax and semantics
            new_syntax = self._create_new_syntax()
            if not new_syntax:
                logger.error("Failed to create new syntax")
                return None
                
            new_semantics = self._create_new_semantics(new_syntax)
            if not new_semantics:
                logger.error("Failed to create new semantics")
                return None
            
            # Build new model constraints with the Z3 model
            new_model_constraints = self._create_new_model_constraints(
                new_syntax, new_semantics, z3_model
            )
            
            # Create the new model structure
            new_structure = ModelStructureClass(
                new_syntax,
                new_semantics,
                new_model_constraints
            )
            
            # Store the Z3 model
            new_structure.z3_model = z3_model
            
            # Copy over essential attributes
            self._copy_essential_attributes(new_structure)
            
            # Ensure theory-specific setup is complete
            self._ensure_theory_setup(new_structure, new_model_constraints)
            
            return new_structure
            
        except Exception as e:
            logger.error(f"Error building new model structure: {str(e)}")
            logger.error(f"Full traceback:\n{traceback.format_exc()}")
            return None
    
    def _get_model_structure_class(self):
        """Get the appropriate model structure class."""
        if hasattr(self.build_example, 'model_structure'):
            return self.build_example.model_structure.__class__
        
        # Try to import based on theory module
        if self.theory_module:
            try:
                parts = self.theory_module.split('.')
                if 'relevance' in parts:
                    from model_checker.theory_lib.logos.subtheories.relevance.model import RelevanceModelStructure
                    return RelevanceModelStructure
                elif 'logos' in parts:
                    from model_checker.theory_lib.logos.model import LogosModelStructure
                    return LogosModelStructure
                # Add other theories as needed
            except ImportError:
                pass
        
        return None
    
    def _create_new_syntax(self):
        """Create a new syntax instance."""
        if hasattr(self.build_example, 'example_syntax'):
            original = self.build_example.example_syntax
            
            # For Syntax class (not theory-specific), it needs the original infix expressions
            if original.__class__.__name__ == 'Syntax':
                # Get from build_example which has the raw premises/conclusions
                from model_checker.syntactic import Syntax
                return Syntax(
                    self.build_example.premises,
                    self.build_example.conclusions,
                    self.build_example.semantic_theory.get("operators")
                )
            
            # For theory-specific syntax classes
            SyntaxClass = original.__class__
            
            # Common pattern: theory syntax classes take proposition and operator lists
            if hasattr(original, 'propositions') and hasattr(original, 'defined_operators'):
                return SyntaxClass(
                    propositions=original.propositions,
                    defined_operators=original.defined_operators
                )
            else:
                # Try copying all attributes
                try:
                    # Create instance without calling __init__
                    new_syntax = SyntaxClass.__new__(SyntaxClass)
                    # Copy attributes
                    for attr in dir(original):
                        if not attr.startswith('_'):
                            try:
                                setattr(new_syntax, attr, getattr(original, attr))
                            except:
                                pass
                    return new_syntax
                except:
                    return original  # Fall back to using the same syntax
        
        return None
    
    def _create_new_semantics(self, syntax):
        """Create a new semantics instance."""
        # Use semantic theory from build example
        if hasattr(self.build_example, 'semantic_theory'):
            semantics_class = self.build_example.semantic_theory["semantics"]
            settings = self.build_example.settings.copy()
            
            # Create new semantics WITHOUT state transfer
            return semantics_class(settings)
        
        # Fallback to copying from existing
        if hasattr(self.build_example, 'example_semantics'):
            SemanticsClass = self.build_example.example_semantics.__class__
            original = self.build_example.example_semantics
            
            # Use settings
            if hasattr(self.build_example, 'settings'):
                return SemanticsClass(self.build_example.settings)
            
            # Copy basic settings
            kwargs = {}
            for attr in ['N', 'M', 'T', 'W']:
                if hasattr(original, attr):
                    kwargs[attr] = getattr(original, attr)
            
            # Create new instance
            return SemanticsClass(**kwargs)
        
        return None
    
    def _create_new_model_constraints(self, syntax, semantics, z3_model):
        """Create new model constraints with the given Z3 model."""
        if hasattr(self.build_example, 'model_constraints'):
            ConstraintsClass = self.build_example.model_constraints.__class__
            original = self.build_example.model_constraints
            
            # Get settings
            settings = getattr(self.build_example, 'settings', {})
            
            # Check if we need proposition_class (for ModelConstraints)
            if ConstraintsClass.__name__ == 'ModelConstraints':
                # Try to get proposition class from various sources
                proposition_class = None
                
                # Try semantic theory
                if hasattr(self.build_example, 'semantic_theory') and 'proposition_class' in self.build_example.semantic_theory:
                    proposition_class = self.build_example.semantic_theory["proposition_class"]
                # Try from original constraints
                elif hasattr(original, 'proposition_class'):
                    proposition_class = original.proposition_class
                # Try from syntax
                elif hasattr(syntax, 'proposition_class'):
                    proposition_class = syntax.proposition_class
                else:
                    # Fall back based on theory
                    if 'logos' in str(type(original)):
                        from model_checker.theory_lib.logos.proposition import LogosProposition
                        proposition_class = LogosProposition
                    else:
                        # Generic proposition
                        from model_checker.syntactic.proposition import Proposition
                        proposition_class = Proposition
                
                new_constraints = ConstraintsClass(syntax, semantics, settings, proposition_class)
            else:
                # Theory-specific constraints
                new_constraints = ConstraintsClass(syntax, semantics, settings)
            
            # Important: We need to make the constraints use our Z3 model
            # This is the key to making iteration work
            if hasattr(new_constraints, 'solver'):
                # Replace the solver's model with ours
                new_constraints.z3_model = z3_model
            
            return new_constraints
        
        return None
    
    def _copy_essential_attributes(self, new_structure):
        """Copy essential attributes from original structure."""
        original = self.build_example.model_structure
        
        # Copy formula lists
        for attr in ['premise_formulas', 'conclusion_formulas', 'defined_premise_formulas']:
            if hasattr(original, attr):
                setattr(new_structure, attr, getattr(original, attr))
        
        # Copy sentence letters
        if hasattr(original, 'sentence_letters'):
            new_structure.sentence_letters = original.sentence_letters
    
    def _ensure_theory_setup(self, structure, model_constraints):
        """Ensure theory-specific setup is complete."""
        # For logos-based theories, ensure states are set up
        if hasattr(structure, 'z3_possible_states') and hasattr(model_constraints, 'z3_possible_states'):
            structure.z3_possible_states = model_constraints.z3_possible_states
            structure.z3_world_states = getattr(model_constraints, 'z3_world_states', [])
        
        # For bimodal theory, ensure world histories are set up
        if hasattr(structure, 'world_histories') and hasattr(model_constraints, 'world_histories'):
            structure.world_histories = model_constraints.world_histories
        
        # Ensure all_states is populated
        if hasattr(structure.semantics, 'N') and not hasattr(structure, 'all_states'):
            structure.all_states = list(range(2 ** structure.semantics.N))
    
    def validate_model_structure(self, structure) -> bool:
        """Validate that a model structure is properly constructed.
        
        Args:
            structure: The model structure to validate
            
        Returns:
            True if valid, False otherwise
        """
        # Check required attributes
        required = ['z3_model', 'semantics', 'syntax']
        for attr in required:
            if not hasattr(structure, attr):
                logger.error(f"Model structure missing required attribute: {attr}")
                return False
        
        # Check theory-specific requirements
        if 'logos' in str(type(structure)):
            if not hasattr(structure, 'z3_possible_states'):
                logger.error("Logos model missing z3_possible_states")
                return False
        
        return True