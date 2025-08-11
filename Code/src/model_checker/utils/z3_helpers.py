"""Z3 helper utilities for ModelChecker.

This module provides helper functions for working with Z3, including:
- Universal and existential quantification over bit vectors
- Set operations (future)
"""

from z3 import BitVecVal, And, Or, substitute


def ForAll(bvs, formula):
    """Implements universal quantification over bit vectors for Z3.
    
    This function explicitly generates universal quantification by substituting
    all possible bit vector values for the variables in the formula and taking
    the conjunction of the resulting constraints. This approach allows for
    more direct control over quantification than using Z3's built-in ForAll.
    
    Args:
        bvs: Either a single Z3 bit vector or a list of bit vectors to quantify over
        formula: The Z3 formula to quantify
        
    Returns:
        BoolRef: A Z3 formula representing the conjunction of all substituted constraints
    """
    constraints = []
    if not isinstance(bvs, list):
        bvs = [bvs]
    bv_test = bvs[0]
    temp_N = bv_test.size()
    num_bvs = 2 ** temp_N
    if len(bvs) == 1:
        bv = bvs[0]
        for i in range(num_bvs):
            substituted_formula = substitute(formula, (bv, BitVecVal(i, temp_N)))
            constraints.append(substituted_formula)
    else:
        bv = bvs[0]
        remaining_bvs = bvs[1:]
        reduced_formula = ForAll(remaining_bvs, formula)
        for i in range(num_bvs):
            substituted_reduced_formula = substitute(reduced_formula, (bv, BitVecVal(i, temp_N)))
            constraints.append(substituted_reduced_formula)
    return And(constraints)


def Exists(bvs, formula):
    """Implements existential quantification over bit vectors for Z3.
    
    This function explicitly generates existential quantification by substituting
    all possible bit vector values for the variables in the formula and taking
    the disjunction of the resulting constraints. This approach allows for
    more direct control over quantification than using Z3's built-in Exists.
    
    Args:
        bvs: Either a single Z3 bit vector or a list of bit vectors to quantify over
        formula: The Z3 formula to quantify
        
    Returns:
        BoolRef: A Z3 formula representing the disjunction of all substituted constraints
    """
    constraints = []
    if not isinstance(bvs, list):
        bvs = [bvs]
    sample_bv = bvs[0]
    N = sample_bv.size()
    num_bvs = 2 ** N
    if len(bvs) == 1:
        bv = bvs[0]
        for i in range(num_bvs):
            substituted_formula = substitute(formula, (bv, BitVecVal(i, N)))
            constraints.append(substituted_formula)
    else:
        bv = bvs[0]
        remaining_bvs = bvs[1:]
        reduced_formula = Exists(remaining_bvs, formula) # Exists or ForAll?
        for i in range(num_bvs):
            substituted_reduced_formula = substitute(reduced_formula, (bv, BitVecVal(i, N)))
            constraints.append(substituted_reduced_formula)
    return Or(constraints)


def safe_getattr(obj, attr_name, default=None):
    """Safely get an attribute with a default value.
    
    This is a simple wrapper around getattr that ensures consistent
    attribute access patterns throughout the codebase. It's particularly
    useful for accessing model structure attributes that may not always
    be present.
    
    Args:
        obj: The object to get the attribute from
        attr_name: The name of the attribute to get
        default: The default value to return if attribute doesn't exist
        
    Returns:
        The attribute value if it exists, otherwise the default value
    """
    return getattr(obj, attr_name, default)