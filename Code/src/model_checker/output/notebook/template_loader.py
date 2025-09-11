"""Template loader for notebook generation.

Discovers and loads the appropriate template based on the semantic class.
"""

from typing import Any


class TemplateLoader:
    """Load and manage notebook templates for different theory types."""
    
    def get_template_for_class(self, semantics_class: Any):
        """Get the appropriate template for a semantic class.
        
        Args:
            semantics_class: The semantics class from the theory configuration
            
        Returns:
            Template instance for the theory type
            
        Raises:
            ValueError: If no template is available for the semantic class
        """
        # Get class name for matching
        class_name = semantics_class.__name__ if hasattr(semantics_class, '__name__') else str(semantics_class)
        
        # Import templates based on class name
        if class_name == 'LogosSemantics':
            from .templates.logos import LogosNotebookTemplate
            return LogosNotebookTemplate()
        elif class_name == 'WitnessSemantics':
            from .templates.exclusion import ExclusionNotebookTemplate
            return ExclusionNotebookTemplate()
        elif class_name == 'ImpositionSemantics':
            from .templates.imposition import ImpositionNotebookTemplate
            return ImpositionNotebookTemplate()
        else:
            # Try to use a generic template as fallback
            from .templates.base import DirectNotebookTemplate
            return DirectNotebookTemplate()