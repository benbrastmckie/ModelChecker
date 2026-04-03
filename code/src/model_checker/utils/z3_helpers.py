"""Z3 helper utilities for ModelChecker.

This module provides helper functions for working with Z3, including:
- Universal and existential quantification over bit vectors
- Toggleable quantifier mode (finitary/native/auto)
- Set operations (future)
"""

from typing import List, Union, Any, Literal, TYPE_CHECKING

from model_checker.solver.expressions import BitVecVal, And, Or, substitute

if TYPE_CHECKING:
    from model_checker.z3_shim import BitVecRef, BoolRef


# Quantifier mode: "finitary", "native", or "auto"
# - finitary: explicit enumeration (2^N conjuncts/disjuncts) - default
# - native: use solver's native ForAll/Exists quantifiers
# - auto: use native if bit width > 4, finitary otherwise
_quantifier_mode: Literal["finitary", "native", "auto"] = "finitary"


def set_quantifier_mode(mode: Literal["finitary", "native", "auto"]) -> None:
    """Set the quantifier implementation mode.

    Args:
        mode:
            "finitary" - Use explicit enumeration (2^N conjuncts/disjuncts)
            "native" - Use solver's native ForAll/Exists quantifiers
            "auto" - Use native for bit width > 4, finitary otherwise

    Example:
        >>> from model_checker.utils.z3_helpers import set_quantifier_mode
        >>> set_quantifier_mode("native")  # Use solver's native quantifiers
    """
    global _quantifier_mode
    if mode not in ("finitary", "native", "auto"):
        raise ValueError(f"Invalid quantifier mode: {mode}. Must be 'finitary', 'native', or 'auto'")
    _quantifier_mode = mode


def get_quantifier_mode() -> Literal["finitary", "native", "auto"]:
    """Get current quantifier mode.

    Returns:
        The current quantifier mode ("finitary", "native", or "auto")
    """
    return _quantifier_mode


def _native_forall(bvs: Union["BitVecRef", List["BitVecRef"]], formula: "BoolRef") -> "BoolRef":
    """Native quantifier via solver backend.

    Uses the solver's native ForAll implementation, which may use
    quantifier instantiation heuristics rather than explicit enumeration.

    Args:
        bvs: Either a single Z3 bit vector or a list of bit vectors to quantify over
        formula: The Z3 formula to quantify

    Returns:
        BoolRef: A Z3 formula with native quantification
    """
    from model_checker.solver.expressions import ForAll as NativeForAll
    if not isinstance(bvs, list):
        bvs = [bvs]
    return NativeForAll(bvs, formula)


def _native_exists(bvs: Union["BitVecRef", List["BitVecRef"]], formula: "BoolRef") -> "BoolRef":
    """Native existential quantifier via solver backend.

    Uses the solver's native Exists implementation, which may use
    quantifier instantiation heuristics rather than explicit enumeration.

    Args:
        bvs: Either a single Z3 bit vector or a list of bit vectors to quantify over
        formula: The Z3 formula to quantify

    Returns:
        BoolRef: A Z3 formula with native existential quantification
    """
    from model_checker.solver.expressions import Exists as NativeExists
    if not isinstance(bvs, list):
        bvs = [bvs]
    return NativeExists(bvs, formula)


def _finitary_forall(bvs: Union["BitVecRef", List["BitVecRef"]], formula: "BoolRef") -> "BoolRef":
    """Finitary universal quantification via explicit enumeration.

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
        # Use _finitary_forall directly to avoid mode dispatch during recursion
        reduced_formula = _finitary_forall(remaining_bvs, formula)
        for i in range(num_bvs):
            substituted_reduced_formula = substitute(reduced_formula, (bv, BitVecVal(i, temp_N)))
            constraints.append(substituted_reduced_formula)
    return And(constraints)


def _finitary_exists(bvs: Union["BitVecRef", List["BitVecRef"]], formula: "BoolRef") -> "BoolRef":
    """Finitary existential quantification via explicit enumeration.

    This function explicitly generates existential quantification by substituting
    all possible bit vector values for the variables in the formula and taking
    the disjunction of the resulting constraints.

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
        # Use _finitary_exists directly to avoid mode dispatch during recursion
        reduced_formula = _finitary_exists(remaining_bvs, formula)
        for i in range(num_bvs):
            substituted_reduced_formula = substitute(reduced_formula, (bv, BitVecVal(i, N)))
            constraints.append(substituted_reduced_formula)
    return Or(constraints)


def ForAll(bvs: Union["BitVecRef", List["BitVecRef"]], formula: "BoolRef") -> "BoolRef":
    """Universal quantification with mode-aware implementation.

    This function dispatches to either finitary enumeration or native solver
    quantifiers based on the current quantifier mode set via set_quantifier_mode().

    Args:
        bvs: Either a single Z3 bit vector or a list of bit vectors to quantify over
        formula: The Z3 formula to quantify

    Returns:
        BoolRef: A Z3 formula representing universal quantification
    """
    if _quantifier_mode == "native":
        return _native_forall(bvs, formula)
    elif _quantifier_mode == "auto":
        # Use native if domain is large (bit width > 4 means > 16 elements)
        bv_test = bvs[0] if isinstance(bvs, list) else bvs
        if bv_test.size() > 4:
            return _native_forall(bvs, formula)
    # Default: finitary
    return _finitary_forall(bvs, formula)


def Exists(bvs: Union["BitVecRef", List["BitVecRef"]], formula: "BoolRef") -> "BoolRef":
    """Existential quantification with mode-aware implementation.

    This function dispatches to either finitary enumeration or native solver
    quantifiers based on the current quantifier mode set via set_quantifier_mode().

    Args:
        bvs: Either a single Z3 bit vector or a list of bit vectors to quantify over
        formula: The Z3 formula to quantify

    Returns:
        BoolRef: A Z3 formula representing existential quantification
    """
    if _quantifier_mode == "native":
        return _native_exists(bvs, formula)
    elif _quantifier_mode == "auto":
        # Use native if domain is large (bit width > 4 means > 16 elements)
        bv_test = bvs[0] if isinstance(bvs, list) else bvs
        if bv_test.size() > 4:
            return _native_exists(bvs, formula)
    # Default: finitary
    return _finitary_exists(bvs, formula)


def safe_getattr(obj: Any, attr_name: str, default: Any = None) -> Any:
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