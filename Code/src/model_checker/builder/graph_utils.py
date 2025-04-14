"""Graph utilities for model structure representation and isomorphism checking.

This module provides tools for representing logical models as graphs
and checking for isomorphism between models.
"""

import networkx as nx
from hashlib import sha256
import json
import z3
import logging
import sys

# Configure logging
logger = logging.getLogger(__name__)
if not logger.handlers:
    handler = logging.StreamHandler(sys.stdout)
    formatter = logging.Formatter('[GRAPH] %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    logger.setLevel(logging.INFO)

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
        
        The graph contains:
        - Nodes for each world, with attributes for proposition truth values
        - Edges for accessibility relations
        - Additional theory-specific attributes
        
        Returns:
            nx.DiGraph: Directed graph representing the model
        """
        G = nx.DiGraph()
        
        # Get important references
        constraints = self.model_structure.model_constraints
        semantics = constraints.semantics
        
        # Log debugging info
        with open("/tmp/graph_debug.log", "a") as f:
            f.write("\n=== Creating Graph ===\n")
            f.write(f"Model Structure Type: {type(self.model_structure).__name__}\n")
            f.write(f"Z3 Model Valid: {self.z3_model is not None}\n")
            if hasattr(self.model_structure, 'z3_world_states'):
                f.write(f"World States: {len(getattr(self.model_structure, 'z3_world_states', []))}\n")
            if hasattr(self.model_structure, 'z3_possible_states'):
                f.write(f"Possible States: {len(getattr(self.model_structure, 'z3_possible_states', []))}\n")
                
        # Use the model's world states directly instead of assuming numeric indices
        world_states = getattr(self.model_structure, 'z3_world_states', [])
        if not world_states and hasattr(self.model_structure, 'world_states'):
            world_states = getattr(self.model_structure, 'world_states', [])
            
        # Log world states
        with open("/tmp/graph_debug.log", "a") as f:
            f.write(f"World States to use: {len(world_states)}\n")
            
        # Add nodes for each world state
        for i, world in enumerate(world_states):
            # Create a properties dictionary for this world
            properties = {"world_index": i}
            
            # Add truth values for each sentence letter at this world
            for letter in constraints.sentence_letters:
                try:
                    # Use the model's true_at function to determine if the letter is true at this world
                    if hasattr(semantics, 'true_at'):
                        # Create a sentence for this letter
                        from model_checker.syntactic import Sentence
                        letter_sentence = Sentence(sentence_letter=letter)
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
                        f.write(f"Error evaluating letter {letter} at world {i}: {str(e)}\n")
            
            # Add theory-specific world properties
            if hasattr(self.model_structure, 'get_world_properties'):
                try:
                    theory_properties = self.model_structure.get_world_properties(world, self.z3_model)
                    properties.update(theory_properties)
                except Exception as e:
                    with open("/tmp/graph_debug.log", "a") as f:
                        f.write(f"Error getting world properties for world {i}: {str(e)}\n")
            
            # Add the node with its properties
            G.add_node(i, **properties)
            
            with open("/tmp/graph_debug.log", "a") as f:
                f.write(f"Added node {i} with properties: {properties}\n")
        
        # Add edges for accessibility relations
        if hasattr(semantics, 'R') and len(world_states) > 0:
            for i, w1 in enumerate(world_states):
                for j, w2 in enumerate(world_states):
                    try:
                        # Check if w2 is accessible from w1
                        relation_value = self.z3_model.eval(
                            semantics.R(w1, w2), 
                            model_completion=True
                        )
                        if relation_value and str(relation_value) == 'True':
                            G.add_edge(i, j)
                            with open("/tmp/graph_debug.log", "a") as f:
                                f.write(f"Added edge from {i} to {j}\n")
                    except Exception as e:
                        with open("/tmp/graph_debug.log", "a") as f:
                            f.write(f"Error checking relation R({i},{j}): {str(e)}\n")
        
        # Add theory-specific relations
        if hasattr(self.model_structure, 'get_relation_edges'):
            try:
                extra_edges = self.model_structure.get_relation_edges(self.z3_model)
                for src, dst, attrs in extra_edges:
                    G.add_edge(src, dst, **attrs)
                    with open("/tmp/graph_debug.log", "a") as f:
                        f.write(f"Added theory-specific edge from {src} to {dst}\n")
            except Exception as e:
                with open("/tmp/graph_debug.log", "a") as f:
                    f.write(f"Error getting relation edges: {str(e)}\n")
        
        with open("/tmp/graph_debug.log", "a") as f:
            f.write(f"Final graph has {len(G.nodes())} nodes and {G.number_of_edges()} edges\n")
            
        return G
    
    def get_invariant_hash(self):
        """Get a hash that's invariant to isomorphism.
        
        This creates a hash based on:
        1. A sorted list of node property frequencies
        2. A sorted list of motif counts
        3. Other graph invariants like degree distribution
        
        Returns:
            str: A hash string that will be the same for isomorphic graphs
        """
        invariants = {}
        
        # Count property combinations
        property_counts = {}
        for _, attrs in self.graph.nodes(data=True):
            # Sort attributes to ensure consistent representation
            prop_tuple = tuple(sorted((k, v) for k, v in attrs.items()))
            property_counts[prop_tuple] = property_counts.get(prop_tuple, 0) + 1
        
        # Store sorted property counts
        invariants["property_counts"] = sorted([
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
        return sha256(invariant_str.encode('utf-8')).hexdigest()
    
    def is_isomorphic(self, other_graph):
        """Check if this graph is isomorphic to another model graph.
        
        Args:
            other_graph: Another ModelGraph instance to compare with
            
        Returns:
            bool: True if the graphs are isomorphic, False otherwise
        """
        # Debug log file for examining isomorphism
        with open("/tmp/isomorphism_debug.log", "a") as debug_file:
            debug_file.write(f"\n--- Starting isomorphism comparison ---\n")
            
            # Log information about this graph
            debug_file.write(f"Graph 1: {len(self.graph)} nodes, {self.graph.number_of_edges()} edges\n")
            debug_file.write(f"Graph 1 hash: {self.get_invariant_hash()}\n")
            
            # Log information about the other graph
            debug_file.write(f"Graph 2: {len(other_graph.graph)} nodes, {other_graph.graph.number_of_edges()} edges\n")
            debug_file.write(f"Graph 2 hash: {other_graph.get_invariant_hash()}\n")
            
        # Quick check using invariant hash
        if self.get_invariant_hash() != other_graph.get_invariant_hash():
            with open("/tmp/isomorphism_debug.log", "a") as debug_file:
                debug_file.write(f"  RESULT: Graph hashes differ - not isomorphic\n")
            return False
        
        # Check if graphs have the same number of nodes and edges
        if (len(self.graph) != len(other_graph.graph) or 
            self.graph.number_of_edges() != other_graph.graph.number_of_edges()):
            with open("/tmp/isomorphism_debug.log", "a") as debug_file:
                debug_file.write(f"  RESULT: Graph structures differ - not isomorphic\n")
            return False
        
        # Log node attributes for debugging
        with open("/tmp/isomorphism_debug.log", "a") as debug_file:
            debug_file.write("\nNode attributes for graph 1:\n")
            for node, attrs in self.graph.nodes(data=True):
                debug_file.write(f"Node {node}: {attrs}\n")
            
            debug_file.write("\nNode attributes for graph 2:\n")
            for node, attrs in other_graph.graph.nodes(data=True):
                debug_file.write(f"Node {node}: {attrs}\n")
        
        # Full isomorphism check
        result = nx.is_isomorphic(
            self.graph, 
            other_graph.graph,
            node_match=self._node_match
        )
        with open("/tmp/isomorphism_debug.log", "a") as debug_file:
            if result:
                debug_file.write("  RESULT: FOUND ISOMORPHIC GRAPHS!\n")
            else:
                debug_file.write("  RESULT: Graphs are NOT isomorphic\n")
        return result
    
    def _node_match(self, node1_attrs, node2_attrs):
        """Check if two nodes match for isomorphism purposes.
        
        Args:
            node1_attrs: Attributes of the first node
            node2_attrs: Attributes of the second node
            
        Returns:
            bool: True if the nodes match, False otherwise
        """
        # Compare all attributes
        if set(node1_attrs.keys()) != set(node2_attrs.keys()):
            return False
            
        for key in node1_attrs:
            if node1_attrs[key] != node2_attrs[key]:
                return False
                
        return True
    
    def get_structural_metrics(self):
        """Get structural metrics about the graph for display.
        
        Returns:
            dict: Dictionary of metrics including node count, edge count,
                 degree distributions, etc.
        """
        metrics = {}
        
        # Basic counts
        metrics['num_worlds'] = len(self.graph)
        metrics['num_relations'] = self.graph.number_of_edges()
        
        # Degree distributions
        in_degrees = sorted(d for _, d in self.graph.in_degree())
        out_degrees = sorted(d for _, d in self.graph.out_degree())
        metrics['in_degree_distribution'] = in_degrees
        metrics['out_degree_distribution'] = out_degrees
        
        # Connected components (for accessibility)
        if len(self.graph) > 0:
            # Convert to undirected for components
            undirected = self.graph.to_undirected()
            metrics['connected_components'] = nx.number_connected_components(undirected)
        else:
            metrics['connected_components'] = 0
        
        # Add theory-specific metrics if available
        if hasattr(self.model_structure, 'get_structural_metrics'):
            theory_metrics = self.model_structure.get_structural_metrics(self.z3_model)
            metrics.update(theory_metrics)
            
        return metrics