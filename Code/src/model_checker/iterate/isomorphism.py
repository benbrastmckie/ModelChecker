"""Graph-based isomorphism detection for model iteration.

This module handles detecting whether newly found models are structurally 
isomorphic to previously found models, using NetworkX for graph comparison.
"""

import logging
from model_checker.iterate.graph_utils import ModelGraph

logger = logging.getLogger(__name__)

# Check if NetworkX is available for isomorphism checking
try:
    import networkx as nx
    HAS_NETWORKX = True
except ImportError:
    HAS_NETWORKX = False


class IsomorphismChecker:
    """Checks for structural isomorphism between models."""
    
    def __init__(self):
        """Initialize isomorphism checker."""
        self.model_graphs = []
        self.isomorphism_cache = {}
    
    def check_isomorphism(self, new_structure, new_model, previous_structures, previous_models):
        """Check if new model is isomorphic to any previous model.
        
        Args:
            new_structure: New model structure to check
            new_model: New Z3 model
            previous_structures: List of previous model structures
            previous_models: List of previous Z3 models
            
        Returns:
            tuple: (is_isomorphic: bool, isomorphic_model: Z3Model or None)
        """
        if not HAS_NETWORKX:
            logger.debug("NetworkX not available - skipping isomorphism check")
            return False, None
            
        try:
            # Create graph for the new model
            new_graph = ModelGraph(new_structure, new_model)
            
            # Check against all previous models
            for i, (prev_structure, prev_model) in enumerate(zip(previous_structures, previous_models)):
                try:
                    # Get or create graph for previous model
                    if i < len(self.model_graphs):
                        prev_graph = self.model_graphs[i]
                    else:
                        prev_graph = ModelGraph(prev_structure, prev_model)
                        self.model_graphs.append(prev_graph)
                    
                    # Check if graphs are isomorphic
                    if self._check_graph_isomorphism(new_graph, prev_graph):
                        logger.debug(f"Model is isomorphic to model {i + 1}")
                        return True, prev_model
                        
                except Exception as e:
                    logger.warning(f"Error checking isomorphism with model {i + 1}: {e}")
                    continue
            
            # If we get here, model is not isomorphic to any previous model
            self.model_graphs.append(new_graph)
            return False, None
            
        except Exception as e:
            logger.warning(f"Error in isomorphism checking: {e}")
            # If isomorphism checking fails, assume not isomorphic to be safe
            return False, None
    
    def _check_graph_isomorphism(self, graph1, graph2):
        """Check if two ModelGraph instances are isomorphic.
        
        Args:
            graph1: First ModelGraph
            graph2: Second ModelGraph
            
        Returns:
            bool: True if graphs are isomorphic
        """
        try:
            # Generate cache keys for both graphs
            key1 = self._generate_graph_cache_key(graph1)
            key2 = self._generate_graph_cache_key(graph2)
            
            # Check cache first
            cache_key = tuple(sorted([key1, key2]))
            if cache_key in self.isomorphism_cache:
                return self.isomorphism_cache[cache_key]
            
            # Quick structural checks first
            if not self._graphs_structurally_compatible(graph1, graph2):
                result = False
            else:
                # Use NetworkX for full isomorphism check
                result = self._networkx_isomorphism_check(graph1.graph, graph2.graph)
            
            # Cache the result
            self.isomorphism_cache[cache_key] = result
            return result
            
        except Exception as e:
            logger.warning(f"Error in graph isomorphism check: {e}")
            return False
    
    def _graphs_structurally_compatible(self, graph1, graph2):
        """Quick structural compatibility check.
        
        Args:
            graph1: First ModelGraph
            graph2: Second ModelGraph
            
        Returns:
            bool: True if graphs could potentially be isomorphic
        """
        try:
            # Check basic graph properties
            if graph1.graph.number_of_nodes() != graph2.graph.number_of_nodes():
                return False
                
            if graph1.graph.number_of_edges() != graph2.graph.number_of_edges():
                return False
            
            # Check degree sequences
            degree_seq1 = sorted([d for n, d in graph1.graph.degree()])
            degree_seq2 = sorted([d for n, d in graph2.graph.degree()])
            if degree_seq1 != degree_seq2:
                return False
                
            return True
            
        except Exception as e:
            logger.warning(f"Error in structural compatibility check: {e}")
            return True  # Assume compatible if check fails
    
    def _networkx_isomorphism_check(self, nx_graph1, nx_graph2):
        """Use NetworkX to check graph isomorphism.
        
        Args:
            nx_graph1: First NetworkX graph
            nx_graph2: Second NetworkX graph
            
        Returns:
            bool: True if graphs are isomorphic
        """
        try:
            # Use NetworkX graph isomorphism
            return nx.is_isomorphic(nx_graph1, nx_graph2)
            
        except Exception as e:
            logger.warning(f"NetworkX isomorphism check failed: {e}")
            return False
    
    def _generate_graph_cache_key(self, graph):
        """Generate a cache key for a ModelGraph.
        
        Args:
            graph: ModelGraph instance
            
        Returns:
            tuple: Cache key for the graph
        """
        try:
            # Use the ModelGraph's invariant hash if available
            if hasattr(graph, 'get_invariant_hash'):
                return graph.get_invariant_hash()
            
            # Fallback to basic graph properties
            nx_graph = graph.graph
            return (
                nx_graph.number_of_nodes(),
                nx_graph.number_of_edges(),
                tuple(sorted([d for n, d in nx_graph.degree()])),
                hash(tuple(sorted(nx_graph.nodes()))),
                hash(tuple(sorted(nx_graph.edges())))
            )
            
        except Exception as e:
            logger.warning(f"Error generating graph cache key: {e}")
            # Return a basic key based on object identity
            return (id(graph), hash(str(graph)))
    
    def clear_cache(self):
        """Clear the isomorphism cache."""
        self.isomorphism_cache.clear()
        logger.debug("Isomorphism cache cleared")
    
    def get_cache_stats(self):
        """Get statistics about the isomorphism cache.
        
        Returns:
            dict: Cache statistics
        """
        return {
            'cache_size': len(self.isomorphism_cache),
            'model_graphs': len(self.model_graphs),
            'has_networkx': HAS_NETWORKX
        }