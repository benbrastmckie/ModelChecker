"""Graph representation and isomorphism detection for model iteration.

This module provides tools for representing logical models as graphs
and checking for isomorphism between models. It is used by the iteration
framework to detect structurally equivalent models.
"""

import networkx as nx
from hashlib import sha256
import json
import logging
import sys
from typing import List, Optional, Set, Any, Tuple

# Configure logging
logger = logging.getLogger(__name__)
if not logger.handlers:
    handler = logging.StreamHandler(sys.stdout)
    formatter = logging.Formatter('[GRAPH] %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    logger.setLevel(logging.INFO)

# Check if NetworkX is available for isomorphism checking
try:
    import networkx as nx
    HAS_NETWORKX = True
except ImportError:
    HAS_NETWORKX = False


class ModelGraph:
    """Represents a logical model as a graph for isomorphism checking.
    
    The graph representation captures the essential structure of the model:
    - Worlds as nodes with proposition truth values as attributes
    - Accessibility relations as directed edges
    - Support for theory-specific structural properties
    
    Attributes:
        model_structure: Reference to the original model structure
        z3_model: The Z3 model being represented
        graph: The NetworkX graph representation
    """
    
    def __init__(self, model_structure, z3_model):
        """Create a graph representation of a logical model.
        
        Args:
            model_structure: The ModelStructure instance
            z3_model: The Z3 model to represent as a graph
        """
        self.model_structure = model_structure
        self.z3_model = z3_model
        self.graph = self._create_graph()
        
    def _create_graph(self):
        """Create a NetworkX graph representing the model structure.
        
        Returns:
            nx.DiGraph: Directed graph with worlds as nodes and relations as edges
        """
        G = nx.DiGraph()
        
        # Log creation
        with open("/tmp/graph_debug.log", "a") as f:
            f.write("\n" + "="*60 + "\n")
            f.write(f"Creating graph for model {id(self.z3_model)}\n")
            f.write(f"Model structure type: {type(self.model_structure)}\n")
        
        # Add worlds as nodes with proposition values as attributes
        try:
            world_states = getattr(self.model_structure, 'z3_world_states', [])
            with open("/tmp/graph_debug.log", "a") as f:
                f.write(f"World states: {world_states}\n")
            
            # Get semantics and constraints for proposition evaluation
            semantics = getattr(self.model_structure, 'semantics', None)
            constraints = getattr(self.model_structure, 'model_constraints', None)
            
            # Add each world as a node with its properties
            for i, world in enumerate(world_states):
                # Convert world to state index if needed
                if hasattr(world, 'as_long'):
                    state = world.as_long()
                else:
                    state = i
                
                # Get proposition values at this world
                properties = {'world_index': i, 'state': state}
                
                # Try to get sentence letter values
                if constraints and hasattr(constraints, 'sentence_letters'):
                    for letter in constraints.sentence_letters:
                        try:
                            # Use the model's true_at function to determine if the letter is true at this world
                            if hasattr(semantics, 'true_at'):
                                # Create a sentence for this letter
                                from model_checker.syntactic import Sentence
                                letter_sentence = Sentence(letter)
                                value = self.z3_model.eval(
                                    semantics.true_at(letter_sentence, world),
                                    model_completion=True
                                )
                                properties[str(letter)] = str(value)
                            else:
                                # Direct evaluation if true_at is not available
                                if hasattr(letter, '__call__'):
                                    value = self.z3_model.eval(letter(i), model_completion=True)
                                else:
                                    value = self.z3_model.eval(letter, model_completion=True)
                                properties[str(letter)] = str(value)
                        except Exception as e:
                            with open("/tmp/graph_debug.log", "a") as f:
                                f.write(f"Error evaluating {letter} at world {i}: {str(e)}\n")
                
                G.add_node(i, **properties)
                with open("/tmp/graph_debug.log", "a") as f:
                    f.write(f"Added node {i} with properties: {properties}\n")
                
        except Exception as e:
            with open("/tmp/graph_debug.log", "a") as f:
                f.write(f"Error adding nodes: {str(e)}\n")
        
        # Add edges for accessibility relations
        try:
            # Check for standard modal accessibility
            if hasattr(semantics, 'accessible'):
                for i in range(len(world_states)):
                    for j in range(len(world_states)):
                        # Check if world i can access world j
                        try:
                            if hasattr(semantics.accessible, '__call__'):
                                # It's a function, call it with world indices
                                acc_expr = semantics.accessible(i, j)
                                is_accessible = self.z3_model.eval(acc_expr, model_completion=True)
                                if str(is_accessible).lower() == 'true':
                                    G.add_edge(i, j, relation='accessible')
                            else:
                                # Check if it's a relation stored differently
                                # This is theory-specific and may need adjustment
                                pass
                        except Exception as e:
                            with open("/tmp/graph_debug.log", "a") as f:
                                f.write(f"Error checking accessibility {i}->{j}: {str(e)}\n")
            
            # Check for other types of relations (theory-specific)
            # e.g., temporal relations, imposition relations, etc.
            self._add_theory_specific_edges(G, world_states, semantics)
            
        except Exception as e:
            with open("/tmp/graph_debug.log", "a") as f:
                f.write(f"Error adding edges: {str(e)}\n")
        
        # Log final graph info
        with open("/tmp/graph_debug.log", "a") as f:
            f.write(f"Graph created with {len(G.nodes())} nodes and {G.number_of_edges()} edges\n")
            f.write(f"Nodes: {list(G.nodes())}\n")
            f.write(f"Edges: {list(G.edges())}\n")
        
        return G
    
    def _add_theory_specific_edges(self, G, world_states, semantics):
        """Add theory-specific edges to the graph.
        
        Args:
            G: NetworkX graph to add edges to
            world_states: List of world states
            semantics: Theory semantics object
        """
        try:
            # Bimodal theories might have temporal relations
            if hasattr(semantics, 'earlier'):
                self._add_relation_edges(G, world_states, semantics.earlier, 'earlier')
            
            # Other theory-specific relations can be added here
            
        except Exception as e:
            with open("/tmp/graph_debug.log", "a") as f:
                f.write(f"Error getting relation edges: {str(e)}\n")
        
        with open("/tmp/graph_debug.log", "a") as f:
            f.write(f"Final graph has {len(G.nodes())} nodes and {G.number_of_edges()} edges\n")
            
        return G
    
    def get_invariant_hash(self):
        """Get a hash that's invariant to isomorphism.
        
        This creates a hash based on graph properties that don't change
        under isomorphism, useful for quick equality checks.
        
        Returns:
            str: Hex string hash of invariant properties
        """
        invariants = {}
        
        # Basic graph properties
        invariants["num_nodes"] = self.graph.number_of_nodes()
        invariants["num_edges"] = self.graph.number_of_edges()
        
        # Degree sequence (sorted)
        invariants["degree_sequence"] = sorted([d for n, d in self.graph.degree()])
        
        # Node property distribution
        property_counts = {}
        for node, attrs in self.graph.nodes(data=True):
            for key, value in attrs.items():
                if key != 'world_index':  # Exclude index-specific properties
                    prop_key = f"{key}:{value}"
                    property_counts[prop_key] = property_counts.get(prop_key, 0) + 1
        
        invariants["property_distribution"] = sorted([
            (str(k), v) for k, v in property_counts.items()
        ])
        
        # Get degree distribution
        in_degrees = sorted(d for _, d in self.graph.in_degree())
        out_degrees = sorted(d for _, d in self.graph.out_degree())
        invariants["in_degrees"] = in_degrees
        invariants["out_degrees"] = out_degrees
        
        # Count small motifs - safely check if graph is big enough for triangles
        if len(self.graph) >= 3 and self.graph.to_undirected().number_of_edges() > 0:
            try:
                invariants["triangles"] = sorted(nx.triangles(self.graph.to_undirected()).values())
            except Exception:
                invariants["triangles"] = []
        else:
            invariants["triangles"] = []
        
        # Create a hash of the invariant data
        invariant_str = json.dumps(invariants, sort_keys=True)
        return sha256(invariant_str.encode()).hexdigest()
    
    def _add_relation_edges(self, G, world_states, relation_func, relation_name):
        """Add edges for a specific relation function.
        
        Args:
            G: NetworkX graph
            world_states: List of world states
            relation_func: Function that returns Z3 expression for relation
            relation_name: Name of the relation for edge attributes
        """
        for i in range(len(world_states)):
            for j in range(len(world_states)):
                try:
                    rel_expr = relation_func(i, j)
                    is_related = self.z3_model.eval(rel_expr, model_completion=True)
                    if str(is_related).lower() == 'true':
                        G.add_edge(i, j, relation=relation_name)
                except Exception as e:
                    with open("/tmp/graph_debug.log", "a") as f:
                        f.write(f"Error checking {relation_name} {i}->{j}: {str(e)}\n")
    
    def to_dict(self):
        """Convert the graph to a dictionary representation.
        
        Returns:
            dict: Dictionary with nodes and edges
        """
        return {
            'nodes': [{'id': n, **attrs} for n, attrs in self.graph.nodes(data=True)],
            'edges': [{'source': u, 'target': v, **attrs} 
                     for u, v, attrs in self.graph.edges(data=True)]
        }
    
    def __str__(self):
        """String representation of the model graph."""
        return (f"ModelGraph(nodes={self.graph.number_of_nodes()}, "
                f"edges={self.graph.number_of_edges()})")
    
    def __repr__(self):
        """Detailed representation of the model graph."""
        return self.__str__()


def compare_model_graphs(graph1: ModelGraph, graph2: ModelGraph) -> dict:
    """Compare two model graphs and return structural differences.
    
    Args:
        graph1: First ModelGraph instance
        graph2: Second ModelGraph instance
        
    Returns:
        dict: Dictionary describing the differences
    """
    differences = {}
    
    # Compare basic metrics
    if graph1.graph.number_of_nodes() != graph2.graph.number_of_nodes():
        differences['node_count'] = {
            'graph1': graph1.graph.number_of_nodes(),
            'graph2': graph2.graph.number_of_nodes()
        }
    
    if graph1.graph.number_of_edges() != graph2.graph.number_of_edges():
        differences['edge_count'] = {
            'graph1': graph1.graph.number_of_edges(),
            'graph2': graph2.graph.number_of_edges()
        }
    
    # Compare degree sequences
    deg_seq1 = sorted([d for n, d in graph1.graph.degree()])
    deg_seq2 = sorted([d for n, d in graph2.graph.degree()])
    
    if deg_seq1 != deg_seq2:
        differences['degree_sequences'] = {
            'graph1': deg_seq1,
            'graph2': deg_seq2
        }
    
    return differences


def get_graph_metrics(model_graph: ModelGraph) -> dict:
    """Get various metrics about a model graph.
    
    Args:
        model_graph: ModelGraph instance
        
    Returns:
        dict: Dictionary of graph metrics
    """
    G = model_graph.graph
    metrics = {}
    
    # Basic metrics
    metrics['num_worlds'] = G.number_of_nodes()
    metrics['num_relations'] = G.number_of_edges()
    
    # Degree distributions
    in_degrees = sorted(d for _, d in G.in_degree())
    out_degrees = sorted(d for _, d in G.out_degree())
    metrics['in_degree_distribution'] = in_degrees
    metrics['out_degree_distribution'] = out_degrees
    
    # Connected components (for accessibility)
    if len(G) > 0:
        metrics['weakly_connected_components'] = nx.number_weakly_connected_components(G)
        metrics['strongly_connected_components'] = nx.number_strongly_connected_components(G)
    
    # Clustering coefficient (if applicable)
    if G.to_undirected().number_of_edges() > 0:
        try:
            metrics['avg_clustering'] = nx.average_clustering(G.to_undirected())
        except:
            metrics['avg_clustering'] = 0.0
    
    return metrics


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
            logger.warning(
                "NetworkX not available - isomorphism detection disabled. "
                "This may result in duplicate models being found. "
                "To enable isomorphism detection, install NetworkX: pip install networkx"
            )
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