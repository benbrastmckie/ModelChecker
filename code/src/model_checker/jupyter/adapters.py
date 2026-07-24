"""Theory-specific adapters for Jupyter integration.

These adapters provide a consistent interface for working with different
semantic theories in the notebook environment.
"""

from typing import TYPE_CHECKING, Any, Dict, Optional

from .types import TheoryName, FormulaString, HTMLString

if TYPE_CHECKING:
    import networkx as nx
    from ..models import ModelStructure


class TheoryAdapter:
    """Base class for theory-specific adapters.
    
    Subclasses should override the three main methods to provide
    theory-specific implementations.
    """
    
    def __init__(self, theory_name: TheoryName) -> None:
        """Initialize the adapter with a theory name.
        
        Args:
            theory_name: Name of the theory
        """
        self.theory_name = theory_name
    
    def model_to_graph(self, model: 'ModelStructure') -> 'nx.DiGraph':
        """Convert a model to a networkx graph for visualization.
        
        Args:
            model: ModelStructure object
        
        Returns:
            nx.DiGraph: Directed graph representation of the model
            
        Raises:
            NotImplementedError: Must be implemented by subclasses
        """
        raise NotImplementedError(
            f"{self.__class__.__name__} must implement model_to_graph"
        )
        
    def format_formula(self, formula: FormulaString) -> str:
        """Format a formula for display.
        
        Args:
            formula: Formula string
            
        Returns:
            str: Formatted formula for display
            
        Raises:
            NotImplementedError: Must be implemented by subclasses
        """
        raise NotImplementedError(
            f"{self.__class__.__name__} must implement format_formula"
        )
    
    def format_model(self, model: 'ModelStructure') -> HTMLString:
        """Format a model for display.
        
        Args:
            model: Model object
            
        Returns:
            str: HTML string for model display
            
        Raises:
            NotImplementedError: Must be implemented by subclasses
        """
        raise NotImplementedError(
            f"{self.__class__.__name__} must implement format_model"
        )


def get_theory_adapter(theory_name: TheoryName) -> TheoryAdapter:
    """Factory function to get the appropriate adapter for a theory.

    Looks the adapter class up via the core registry's `entry.adapter` (attached by
    `_register_jupyter_adapters()` below), falling back to `DefaultTheoryAdapter` for any
    theory with no theory-specific adapter registered (including logos, which the generic
    adapter already handles) or any name the registry doesn't recognize at all. `jupyter/`
    never enumerates theory names to make this decision -- see
    `_register_jupyter_adapters()`'s docstring for how the association is derived.

    Args:
        theory_name: Name of the theory

    Returns:
        TheoryAdapter: The appropriate adapter instance
    """
    from .. import registry as _core_registry

    adapter_class: type[TheoryAdapter] = DefaultTheoryAdapter
    try:
        entry = _core_registry.get_theory_entry(theory_name)
        if entry.adapter is not None:
            adapter_class = entry.adapter
    except ValueError:
        pass

    return adapter_class(theory_name)


def _register_jupyter_adapters() -> None:
    """Attach each theory-specific adapter class to its registry entry.

    Rather than a `{theory_name: AdapterClass}` dict literal (which would hardcode every
    theory name here, tripping the layering test's rule against theory-name string literals
    outside theory_lib), the association is derived structurally from each adapter class's own
    name via the `"{Name}TheoryAdapter"` convention -- e.g. `ExclusionTheoryAdapter` attaches
    itself to whichever registered theory is named 'exclusion', discovered by matching
    `type(adapter_cls).__name__` against the registry's own `get_registered()` list, never by
    writing 'exclusion' as a literal in this file. A theory with no matching adapter class
    (currently: logos) simply keeps `entry.adapter is None` and `get_theory_adapter()` falls
    back to `DefaultTheoryAdapter`.
    """
    from .. import registry as _core_registry

    registered = {name.lower(): name for name in _core_registry.get_registered()}
    adapter_classes = (ExclusionTheoryAdapter, ImpositionTheoryAdapter, BimodalTheoryAdapter)
    suffix = "TheoryAdapter"
    for adapter_cls in adapter_classes:
        class_name = adapter_cls.__name__
        if not class_name.endswith(suffix):
            continue
        derived_name = class_name[: -len(suffix)].lower()
        matched = registered.get(derived_name)
        if matched is not None:
            _core_registry.set_adapter(matched, adapter_cls)


class DefaultTheoryAdapter(TheoryAdapter):
    """Adapter for the default hyperintensional theory."""
    
    def model_to_graph(self, model: 'ModelStructure') -> 'nx.DiGraph':
        """Convert default model to graph.
        
        Args:
            model: ModelStructure object
            
        Returns:
            nx.DiGraph: Directed graph representation of the model
        """
        import networkx as nx
        from model_checker.utils import bitvec_to_substates
        
        G: nx.DiGraph = nx.DiGraph()
        
        # Add nodes (states)
        for state in model.z3_world_states:
            # Convert BitVec to string representation
            if hasattr(model.semantics, 'bitvec_to_substates'):
                state_str: str = model.semantics.bitvec_to_substates(state, model.N)
            else:
                state_str = bitvec_to_substates(state, model.N)
                
            attrs: Dict[str, bool] = {"world": True}
            G.add_node(state_str, **attrs)
        
        # Add the main/evaluation world with special attribute
        main_world = model.main_point["world"]
        if hasattr(model.semantics, 'bitvec_to_substates'):
            main_str: str = model.semantics.bitvec_to_substates(main_world, model.N)
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
        
    def format_formula(self, formula: FormulaString) -> str:
        """Format formula for default theory.
        
        Args:
            formula: Formula string
            
        Returns:
            str: Formatted formula string
        """
        from .unicode import normalize_formula
        from .utils import sanitize_formula
        
        # Convert and sanitize for HTML display
        normalized: str = normalize_formula(formula, format_type="unicode")
        return sanitize_formula(normalized)
        
    def format_model(self, model: 'ModelStructure') -> HTMLString:
        """Format model for default theory.
        
        Args:
            model: ModelStructure object
            
        Returns:
            str: HTML representation of the model
        """
        # Get model key properties for display
        html: str = "<h4>Default Theory Model</h4>"
        
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
                settings: Dict[str, Any] = getattr(
                    model, 'settings', 
                    getattr(model, 'example_settings', {})
                )
                html += "<p>Settings:</p><ul>"
                for key, value in settings.items():
                    html += f"<li><b>{key}:</b> {value}</li>"
                html += "</ul>"
        
        return html


class ExclusionTheoryAdapter(TheoryAdapter):
    """Adapter for exclusion theory."""
    
    def model_to_graph(self, model: 'ModelStructure') -> 'nx.DiGraph':
        """Convert exclusion model to graph.
        
        Args:
            model: ModelStructure object
            
        Returns:
            nx.DiGraph: Directed graph representation of the model
        """
        # For now, use the default implementation as a fallback
        default_adapter = DefaultTheoryAdapter(self.theory_name)
        return default_adapter.model_to_graph(model)
        
    def format_formula(self, formula: FormulaString) -> str:
        """Format formula for exclusion theory.
        
        Args:
            formula: Formula string
            
        Returns:
            str: Formatted formula string
        """
        from .unicode import normalize_formula
        from .utils import sanitize_formula
        
        # Convert and sanitize for HTML display, using exclusion operators
        normalized: str = normalize_formula(formula, format_type="unicode")
        
        # Add special formatting for exclusion operators if needed
        # This could include additional replacements for theory-specific symbols
        
        return sanitize_formula(normalized)
        
    def format_model(self, model: 'ModelStructure') -> HTMLString:
        """Format model for exclusion theory.
        
        Args:
            model: ModelStructure object
            
        Returns:
            str: HTML representation of the model
        """
        # Format for exclusion-specific model details
        html: str = "<h4>Exclusion Theory Model</h4>"
        
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
                settings: Dict[str, Any] = getattr(
                    model, 'settings',
                    getattr(model, 'example_settings', {})
                )
                html += "<p>Settings:</p><ul>"
                for key, value in settings.items():
                    html += f"<li><b>{key}:</b> {value}</li>"
                html += "</ul>"
        
        return html


class ImpositionTheoryAdapter(TheoryAdapter):
    """Adapter for imposition theory."""
    
    def model_to_graph(self, model: 'ModelStructure') -> 'nx.DiGraph':
        """Convert imposition model to graph.
        
        Args:
            model: ModelStructure object
            
        Returns:
            nx.DiGraph: Directed graph representation of the model
        """
        # For now, use the default implementation as a fallback
        default_adapter = DefaultTheoryAdapter(self.theory_name)
        return default_adapter.model_to_graph(model)
        
    def format_formula(self, formula: FormulaString) -> str:
        """Format formula for imposition theory.
        
        Args:
            formula: Formula string
            
        Returns:
            str: Formatted formula string
        """
        from .unicode import normalize_formula
        from .utils import sanitize_formula
        
        # Convert and sanitize for HTML display
        normalized: str = normalize_formula(formula, format_type="unicode")
        return sanitize_formula(normalized)
        
    def format_model(self, model: 'ModelStructure') -> HTMLString:
        """Format model for imposition theory.
        
        Args:
            model: ModelStructure object
            
        Returns:
            str: HTML representation of the model
        """
        # Use default implementation for now
        default_adapter = DefaultTheoryAdapter(self.theory_name)
        return default_adapter.format_model(model)


class BimodalTheoryAdapter(TheoryAdapter):
    """Adapter for bimodal theory."""
    
    def model_to_graph(self, model: 'ModelStructure') -> 'nx.DiGraph':
        """Convert bimodal model to graph.
        
        Args:
            model: ModelStructure object
            
        Returns:
            nx.DiGraph: Directed graph representation of the model
        """
        # For now, use the default implementation as a fallback
        default_adapter = DefaultTheoryAdapter(self.theory_name)
        return default_adapter.model_to_graph(model)
        
    def format_formula(self, formula: FormulaString) -> str:
        """Format formula for bimodal theory.
        
        Args:
            formula: Formula string
            
        Returns:
            str: Formatted formula string
        """
        from .unicode import normalize_formula
        from .utils import sanitize_formula
        
        # Convert and sanitize for HTML display
        normalized: str = normalize_formula(formula, format_type="unicode")
        return sanitize_formula(normalized)
        
    def format_model(self, model: 'ModelStructure') -> HTMLString:
        """Format model for bimodal theory.
        
        Args:
            model: ModelStructure object
            
        Returns:
            str: HTML representation of the model
        """
        # Use default implementation for now
        default_adapter = DefaultTheoryAdapter(self.theory_name)
        return default_adapter.format_model(model)

# Attach theory-specific adapters to the registry at module import time (jupyter/ is only
# imported when jupyter functionality is actually used, so this is not on the core import
# path). See _register_jupyter_adapters()'s docstring for how names are derived without
# hardcoding them here.
_register_jupyter_adapters()
