"""Semantic evaluation framework for model checking.

This module contains the SemanticDefaults class which provides the base
semantic evaluation framework that all theory implementations extend.
"""

from functools import reduce
from z3 import (
    And,
    ArrayRef,
    BitVecSort,
    BitVecVal,
    EmptySet,
    IntVal,
    IsMember,
    Not,
    SetAdd,
    simplify,
)


class SemanticDefaults:
    """Base class providing fundamental semantic operations for a modal logic system.
    
    This class defines the core semantic functionality used across all theories in the
    model checker. It provides methods for working with bit vectors representing states,
    set operations, and foundational semantic relations like part-of and fusion.
    
    Each theory should extend this class to implement its specific semantics for modal
    operators and provide concrete implementations of the truth/falsity conditions.
    
    Attributes:
        name (str): Name of the semantics implementation class
        N (int): Bit-width for state representation (if provided in settings)
        full_state (BitVecVal): Maximum possible state (if N is provided)
        null_state (BitVecVal): Empty state (if N is provided)
        all_states (list): All possible bit vectors of width N (if N is provided)
        M (int): Number of times for temporal semantics (if provided in settings)
        all_times (list): All possible time points (if M is provided)
        main_point (dict): The primary evaluation point for the model
        frame_constraints (list): Z3 constraints defining the logical frame
        premise_behavior (str): How premises should be handled for validity
        conclusion_behavior (str): How conclusions should be handled for validity
    """

    def __init__(self, combined_settings):
        # Reset any global state to avoid cross-example interference
        self._reset_global_state()
        
        # Store the name
        self.name = self.__class__.__name__

        # Define all states and top and bottom if N is specified
        if 'N' in combined_settings.keys():
            self.N = combined_settings['N']
            max_value = (1 << self.N) - 1 # NOTE: faster than 2**self.N - 1
            self.full_state = BitVecVal(max_value, self.N)
            self.null_state = BitVecVal(0, self.N)
            self.all_states = [BitVecVal(i, self.N) for i in range(1 << self.N)]

        # Define all times between 0 and M inclusive
        if 'M' in combined_settings.keys():
            self.M = combined_settings['M']
            self.all_times = [IntVal(i) for i in range(self.M)]

        # Define main_point
        self.main_point = None

        # Define the frame constraints
        self.frame_constraints = None

        # Define invalidity conditions
        self.premise_behavior = None
        self.conclusion_behavior = None
        
    def _reset_global_state(self):
        """Reset any global state that could cause interference between examples.
        
        Following the fail-fast philosophy, this method explicitly resets all cached
        state that could lead to non-deterministic behavior between examples.
        
        Subclasses MUST override this method and call super()._reset_global_state()
        to ensure proper cleanup of both shared and theory-specific resources.
        
        Example for subclasses:
        
        def _reset_global_state(self):
            # Always call parent implementation first
            super()._reset_global_state()
            
            # Reset theory-specific caches
            self._theory_specific_cache = {}
            
            # Clear any references to model structures
            if hasattr(self, 'model_structure'):
                delattr(self, 'model_structure')
                
            # Reset mutable data structures but preserve immutable definitions
            self.data_cache = {}
        """
        # Reset general caches
        self._cached_values = {}

    def fusion(self, bit_s, bit_t):
        """Performs the fusion operation on two bit vectors.
        
        In most modal logics, fusion corresponds to combining or merging states.
        This implementation uses bitwise OR as the default fusion operation,
        but specific theories might override with different implementations.
        
        Args:
            bit_s (BitVecRef): The first bit vector
            bit_t (BitVecRef): The second bit vector
            
        Returns:
            BitVecRef: The result of fusing the two input bit vectors
        """
        return bit_s | bit_t

    def z3_set(self, python_set, N):
        """Convert a Python set to a Z3 set representation with specified bit-width.
        
        Args:
            python_set (set): The Python set to convert
            N (int): The bit-width for the resulting Z3 set
            
        Returns:
            z3.SetRef: A Z3 set containing the elements from the input Python set
            
        Note:
            The resulting Z3 set will have elements of bit-width N
        """
        z3_set = EmptySet(BitVecSort(N))
        for elem in python_set:
            z3_set = SetAdd(z3_set, elem)
        return z3_set

    def z3_set_to_python_set(self, z3_set, domain):
        """Convert a Z3 set to a Python set by checking membership of domain elements.
        
        Args:
            z3_set (z3.SetRef): The Z3 set to convert
            domain (list): Collection of elements to check for membership
            
        Returns:
            set: A Python set containing elements from domain that are members of z3_set
            
        Note:
            Uses Z3's IsMember and simplify functions to determine set membership
        """
        python_set = set()
        for elem in domain:
            if bool(simplify(IsMember(elem, z3_set))):
                python_set.add(elem)
        return python_set

    def total_fusion(self, set_P):
        """Compute the fusion of all elements in a set of bit vectors.
        
        Takes a set of bit vectors and returns their total fusion by applying
        the fusion operation (bitwise OR) to all elements in the set.
        
        Args:
            set_P: A set or Z3 array of bit vectors to be fused
            
        Returns:
            BitVecRef: The result of fusing all elements in the input set
            
        Note:
            If set_P is empty, returns the null bit vector (all zeros)
        """
        if isinstance(set_P, ArrayRef):
            set_P = self.z3_set_to_python_set(set_P, self.all_states)
        return reduce(self.fusion, list(set_P))

    def is_part_of(self, bit_s, bit_t):
        """Checks if one bit vector is part of another where one bit vector is
        a part of another if their fusion is identical to the second bit vector.
        
        Args:
            bit_s (BitVecRef): The potential part
            bit_t (BitVecRef): The potential whole
            
        Returns:
            BoolRef: A Z3 constraint that is True when bit_s is part of bit_t
        """
        return self.fusion(bit_s, bit_t) == bit_t

    def is_proper_part_of(self, bit_s, bit_t):
        """Checks if one bit vector is a proper part of another.
        
        A bit vector is a proper part of another if it is a part of it but not equal to it.
        
        Args:
            bit_s (BitVecRef): The potential proper part
            bit_t (BitVecRef): The potential whole
            
        Returns:
            BoolRef: A Z3 constraint that is True when bit_s is a proper part of bit_t
        """
        return And(self.is_part_of(bit_s, bit_t), bit_s != bit_t)

    def non_null_part_of(self, bit_s, bit_t):
        """Checks if a bit vector is a non-null part of another bit vector.
        
        Args:
            bit_s (BitVecRef): The potential non-null part
            bit_t (BitVecRef): The potential whole
            
        Returns:
            BoolRef: A Z3 constraint that is True when bit_s is both:
                    1. Not the null state (not zero)
                    2. A part of bit_t
        """
        return And(Not(bit_s == 0), self.is_part_of(bit_s, bit_t))

    def product(self, set_A, set_B):
        """Compute the set of all pairwise fusions between elements of two sets.
        
        Args:
            set_A (set): First set of bit vectors
            set_B (set): Second set of bit vectors
            
        Returns:
            set: A set containing the fusion of each element from set_A with each element from set_B
            
        Note:
            Uses bitwise OR as the fusion operation between elements
        """
        product_set = set()
        for bit_a in set_A:
            for bit_b in set_B:
                bit_ab = simplify(bit_a | bit_b)
                product_set.add(bit_ab)
        return product_set

    def coproduct(self, set_A, set_B):
        """Compute the union of two sets closed under pairwise fusion.
        
        Takes two sets and returns their union plus all possible fusions between
        their elements. The result is a set containing:
        1. All elements from both input sets
        2. All pairwise fusions between elements of the input sets
        
        Args:
            set_A (set): First set of bit vectors
            set_B (set): Second set of bit vectors
            
        Returns:
            set: The union of set_A and set_B closed under pairwise fusion
        """
        A_U_B = set_A.union(set_B)
        return A_U_B.union(self.product(set_A, set_B))
    
    def initialize_with_state(self, verify_falsify_state, sentence_letters):
        """Initialize verify/falsify functions with specific values.
        
        This method is used by the iterator to ensure MODEL 2+ use their own
        verify/falsify functions when building constraints, preventing constraint
        mismatches that lead to false premises or true conclusions.
        
        Args:
            verify_falsify_state: Dict mapping (state, letter) -> (verify, falsify)
            sentence_letters: List of sentence letters in the model
            
        NO OPTIONAL PARAMETERS - Both arguments are required per style guide.
        """
        import logging
        logger = logging.getLogger(__name__)
        logger.info(f"Initializing semantics with state for letters: {sentence_letters}")
        logger.info(f"State map has {len(verify_falsify_state)} entries")
        
        self._constrained_state = verify_falsify_state
        self._sentence_letters = sentence_letters
        
        # Store original functions
        self._unconstrained_verify = self.verify
        self._unconstrained_falsify = self.falsify
        
        # Replace with constrained versions
        self.verify = self._make_constrained_verify()
        self.falsify = self._make_constrained_falsify()
    
    def _make_constrained_verify(self):
        """Create a constrained verify function using stored state."""
        import z3
        import logging
        logger = logging.getLogger(__name__)
        
        def constrained_verify(state, letter):
            key = (state, letter)
            if key in self._constrained_state:
                # Return Z3 BoolVal based on stored boolean
                value = self._constrained_state[key][0]
                logger.debug(f"Constrained verify({state}, {letter}) = {value}")
                return z3.BoolVal(value)
            # Fall back to original function
            logger.debug(f"Unconstrained verify({state}, {letter})")
            return self._unconstrained_verify(state, letter)
        return constrained_verify
    
    def _make_constrained_falsify(self):
        """Create a constrained falsify function using stored state."""
        import z3
        
        def constrained_falsify(state, letter):
            key = (state, letter)
            if key in self._constrained_state:
                # Return Z3 BoolVal based on stored boolean
                return z3.BoolVal(self._constrained_state[key][1])
            # Fall back to original function
            return self._unconstrained_falsify(state, letter)
        return constrained_falsify