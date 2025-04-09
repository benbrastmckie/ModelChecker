"""
Theory-specific adapters for Jupyter integration.

These adapters provide a consistent interface for working with different
semantic theories in the notebook environment.
"""

# import importlib
from abc import ABC, abstractmethod
from typing import Any #, Dict, List, Optional, Union, Tuple

# Import as needed to avoid circular imports
# import networkx as nx
# import matplotlib.pyplot as plt


class TheoryAdapter(ABC):
    """Base class for theory-specific adapters."""
    
    def __init__(self, theory_name: str):
        """
        Initialize the adapter with a theory name.
        
        Args:
            theory_name: Name of the theory
        """
        self.theory_name = theory_name
    
    @abstractmethod
    def model_to_graph(self, model: Any) -> 'nx.DiGraph': # type: ignore
        """
        Convert a model to a networkx graph for visualization.
        
        Args:
            model: ModelStructure object
        
        Returns:
            nx.DiGraph: Directed graph representation of the model
        """
        pass
        
    @abstractmethod
    def format_formula(self, formula: str) -> str:
        """
        Format a formula for display.
        
        Args:
            formula: Formula string
            
        Returns:
            str: Formatted formula for display
        """
        pass
    
    @abstractmethod
    def format_model(self, model: Any) -> str:
        """
        Format a model for display.
        
        Args:
            model: Model object
            
        Returns:
            str: HTML string for model display
        """
        pass
    
    @classmethod
    def get_adapter(cls, theory_name: str) -> 'TheoryAdapter':
        """
        Factory method to get the appropriate adapter.
        
        Args:
            theory_name: Name of the theory
            
        Returns:
            TheoryAdapter: The appropriate adapter instance
        """
        # Registry of theory adapters
        registry = {
            "default": DefaultTheoryAdapter,
            "exclusion": ExclusionTheoryAdapter,
            "imposition": ImpositionTheoryAdapter,
            "bimodal": BimodalTheoryAdapter,
        }
        
        adapter_class = registry.get(theory_name, DefaultTheoryAdapter)
        return adapter_class(theory_name)


class DefaultTheoryAdapter(TheoryAdapter):
    """Adapter for the default hyperintensional theory."""
    
    def model_to_graph(self, model: Any) -> 'nx.DiGraph': # type: ignore
        """
        Convert default model to graph.
        
        Args:
            model: ModelStructure object
            
        Returns:
            nx.DiGraph: Directed graph representation of the model
        """
        import networkx as nx
        from model_checker.utils import bitvec_to_substates
        
        G = nx.DiGraph()
        
        # Add nodes (states)
        for state in model.z3_world_states:
            # Convert BitVec to string representation
            if hasattr(model.semantics, 'bitvec_to_substates'):
                state_str = model.semantics.bitvec_to_substates(state, model.N)
            else:
                state_str = bitvec_to_substates(state, model.N)
                
            attrs = {"world": True}
            G.add_node(state_str, **attrs)
        
        # Add the main/evaluation world with special attribute
        main_world = model.main_point["world"]
        if hasattr(model.semantics, 'bitvec_to_substates'):
            main_str = model.semantics.bitvec_to_substates(main_world, model.N)
        else:
            main_str = bitvec_to_substates(main_world, model.N)
        
        # Update the node or add it if it doesn't exist
        if main_str in G.nodes:
            G.nodes[main_str]['main'] = True
        else:
            G.add_node(main_str, world=True, main=True)
        
        # Add accessibility relations if available
        if hasattr(model, 'accessibility_relation'):
            # Process accessibility relations
            # This is theory-specific and would need to be implemented
            pass
            
        return G
        
    def format_formula(self, formula: str) -> str:
        """
        Format formula for default theory.
        
        Args:
            formula: Formula string
            
        Returns:
            str: Formatted formula string
        """
        from .unicode import normalize_formula
        from .utils import sanitize_formula
        
        # Convert and sanitize for HTML display
        normalized = normalize_formula(formula, format_type="unicode")
        return sanitize_formula(normalized)
        
    def format_model(self, model: Any) -> str:
        """
        Format model for default theory.
        
        Args:
            model: ModelStructure object
            
        Returns:
            str: HTML representation of the model
        """
        # Get model key properties for display
        html = f"<h4>Default Theory Model</h4>"
        
        # Show key model attributes
        if hasattr(model, 'model_structure'):
            ms = model.model_structure
            
            # Get number of atomic propositions
            n = getattr(ms, 'N', 'Unknown')
            html += f"<p>Atomic States: {n}</p>"
            
            # Get the main evaluation world if available
            if hasattr(ms, 'main_point'):
                html += f"<p>Main Evaluation Point: {ms.main_point}</p>"
            
            # Add settings summary
            if hasattr(model, 'settings') or hasattr(model, 'example_settings'):
                settings = getattr(model, 'settings', getattr(model, 'example_settings', {}))
                html += "<p>Settings:</p><ul>"
                for key, value in settings.items():
                    html += f"<li><b>{key}:</b> {value}</li>"
                html += "</ul>"
        
        return html


class ExclusionTheoryAdapter(TheoryAdapter):
    """Adapter for exclusion theory."""
    
    def model_to_graph(self, model: Any) -> 'nx.DiGraph': # type: ignore
        """
        Convert exclusion model to graph.
        
        Args:
            model: ModelStructure object
            
        Returns:
            nx.DiGraph: Directed graph representation of the model
        """
        import networkx as nx
        from model_checker.utils import bitvec_to_substates
        
        G = nx.DiGraph()
        
        # Add nodes (states) - Exclusion-specific implementation
        # This would need to be customized for exclusion theory's 
        # specific state representation
        
        # For now, use the default implementation as a fallback
        return DefaultTheoryAdapter(self.theory_name).model_to_graph(model)
        
    def format_formula(self, formula: str) -> str:
        """
        Format formula for exclusion theory.
        
        Args:
            formula: Formula string
            
        Returns:
            str: Formatted formula string
        """
        from .unicode import normalize_formula
        from .utils import sanitize_formula
        
        # Convert and sanitize for HTML display, using exclusion operators
        normalized = normalize_formula(formula, format_type="unicode")
        
        # Add special formatting for exclusion operators if needed
        # This could include additional replacements for theory-specific symbols
        
        return sanitize_formula(normalized)
        
    def format_model(self, model: Any) -> str:
        """
        Format model for exclusion theory.
        
        Args:
            model: ModelStructure object
            
        Returns:
            str: HTML representation of the model
        """
        # Format for exclusion-specific model details
        html = f"<h4>Exclusion Theory Model</h4>"
        
        # Show key model attributes - customize for exclusion theory
        if hasattr(model, 'model_structure'):
            ms = model.model_structure
            
            # Get number of atomic propositions
            n = getattr(ms, 'N', 'Unknown')
            html += f"<p>Atomic States: {n}</p>"
            
            # Add exclusion-specific model information
            # This would need to be customized based on the exclusion theory
            
            # Add settings summary
            if hasattr(model, 'settings') or hasattr(model, 'example_settings'):
                settings = getattr(model, 'settings', getattr(model, 'example_settings', {}))
                html += "<p>Settings:</p><ul>"
                for key, value in settings.items():
                    html += f"<li><b>{key}:</b> {value}</li>"
                html += "</ul>"
        
        return html


class ImpositionTheoryAdapter(TheoryAdapter):
    """Adapter for imposition theory."""
    
    def model_to_graph(self, model: Any) -> 'nx.DiGraph': # type: ignore
        """
        Convert imposition model to graph.
        
        Args:
            model: ModelStructure object
            
        Returns:
            nx.DiGraph: Directed graph representation of the model
        """
        # For now, use the default implementation as a fallback
        return DefaultTheoryAdapter(self.theory_name).model_to_graph(model)
        
    def format_formula(self, formula: str) -> str:
        """
        Format formula for imposition theory.
        
        Args:
            formula: Formula string
            
        Returns:
            str: Formatted formula string
        """
        from .unicode import normalize_formula
        from .utils import sanitize_formula
        
        # Convert and sanitize for HTML display
        normalized = normalize_formula(formula, format_type="unicode")
        return sanitize_formula(normalized)
        
    def format_model(self, model: Any) -> str:
        """
        Format model for imposition theory.
        
        Args:
            model: ModelStructure object
            
        Returns:
            str: HTML representation of the model
        """
        # Use default implementation for now
        return DefaultTheoryAdapter(self.theory_name).format_model(model)


class BimodalTheoryAdapter(TheoryAdapter):
    """Adapter for bimodal theory."""
    
    def model_to_graph(self, model: Any) -> 'nx.DiGraph': # type: ignore
        """
        Convert bimodal model to graph.
        
        Args:
            model: ModelStructure object
            
        Returns:
            nx.DiGraph: Directed graph representation of the model
        """
        # For now, use the default implementation as a fallback
        return DefaultTheoryAdapter(self.theory_name).model_to_graph(model)
        
    def format_formula(self, formula: str) -> str:
        """
        Format formula for bimodal theory.
        
        Args:
            formula: Formula string
            
        Returns:
            str: Formatted formula string
        """
        from .unicode import normalize_formula
        from .utils import sanitize_formula
        
        # Convert and sanitize for HTML display
        normalized = normalize_formula(formula, format_type="unicode")
        return sanitize_formula(normalized)
        
    def format_model(self, model: Any) -> str:
        """
        Format model for bimodal theory.
        
        Args:
            model: ModelStructure object
            
        Returns:
            str: HTML representation of the model
        """
        # Use default implementation for now
        return DefaultTheoryAdapter(self.theory_name).format_model(model)
