"""Bitvector operation utilities for ModelChecker.

This module provides functions for converting between Z3 bitvectors and
human-readable state representations, including:
- Binary string conversions
- State space indexing
- Substate and world state representations
"""

import string
from z3 import BitVecVal


def binary_bitvector(bit, N):
    """Converts a Z3 bit vector to a binary string representation.
    
    This function takes a Z3 bit vector and converts it to a binary string
    representation with the appropriate number of bits. For bit widths that
    are not multiples of 4, it uses the raw string expression; otherwise,
    it converts from hexadecimal to binary.
    
    Args:
        bit: A Z3 bit vector
        N (int): The bit width to use for the representation
        
    Returns:
        str: A binary string representation of the bit vector
    """
    return (
        bit.sexpr()
        if N % 4 != 0
        else int_to_binary(int(bit.sexpr()[2:], 16), N)
    )


def int_to_binary(integer, number):
    '''Converts a hexadecimal string to a binary string.'''
    binary_str = bin(integer)[2:]  # Convert to binary string and remove '0b' prefix
    padding = number - len(binary_str)  # Calculate padding
    return '#b' + '0' * padding + binary_str


def index_to_substate(index):
    '''
    test cases should make evident what's going on
    >>> index_to_substate(0)
    'a'
    >>> index_to_substate(26)
    'aa'
    >>> index_to_substate(27)
    'bb'
    >>> index_to_substate(194)
    'mmmmmmmm'
    used in bitvec_to_substates
    '''
    number = index + 1 # because python indices start at 0
    alphabet = string.ascii_lowercase  # 'abcdefghijklmnopqrstuvwxyz'
    letter = alphabet[number % 26 - 1]  # Get corresponding letter
    return ((number//26) + 1) * letter


def bitvec_to_substates(bit_vec, N):
    '''converts bitvectors to fusions of atomic states.'''
    # Safety check for non-BitVec objects
    if not hasattr(bit_vec, 'sexpr'):
        # Handle the case where we don't have a proper BitVec
        if hasattr(bit_vec, '__int__'):
            # If it can be converted to int, use that
            return bitvec_to_substates(BitVecVal(int(bit_vec), N), N)
        else:
            # Check if it's a Z3 QuantifierRef or other Z3 object
            if hasattr(bit_vec, 'ast') or hasattr(bit_vec, 'ctx'):
                # It's a Z3 object but not a BitVec - return a placeholder
                return f"<z3-obj>"
            # Fall back to a safe representation
            return f"<unknown-{str(bit_vec)}>"
    
    bit_vec_as_string = bit_vec.sexpr()
    
    # Handle different formats of bit vector representation
    if 'x' in bit_vec_as_string:  # hexadecimal format
        integer = int(bit_vec_as_string[2:], 16)
        bit_vec_as_string = int_to_binary(integer, N)
    elif bit_vec_as_string.startswith('#'):  # already in binary format
        bit_vec_as_string = bit_vec_as_string
    else:  # decimal format
        try:
            integer = int(bit_vec_as_string)
            bit_vec_as_string = '#b' + format(integer, f'0{N}b')
        except ValueError:
            # If we can't parse as integer, assume it's already in correct format
            pass
    
    # Remove the '#b' prefix if present
    if bit_vec_as_string.startswith('#b'):
        bit_vec_as_string = bit_vec_as_string[2:]
    
    # Ensure we have the correct number of bits
    if len(bit_vec_as_string) < N:
        bit_vec_as_string = '0' * (N - len(bit_vec_as_string)) + bit_vec_as_string
    
    # Process the bits
    bit_vec_backwards = bit_vec_as_string[::-1]
    state_repr = ""
    
    # If all zeros, return null state
    if all(b == '0' for b in bit_vec_backwards):
        return "□"
        
    for i, char in enumerate(bit_vec_backwards):
        if char == "1":
            state_repr += index_to_substate(i)
            state_repr += "."
            
    # Remove trailing dot if present
    return state_repr[:-1] if state_repr else "□"


def bitvec_to_worldstate(bit_vec, N=None):
    """Converts a bitvector to a simple alphabetic world state label.
    
    Maps bitvector values to letters: 0→a, 1→b, 2→c, ..., 25→z, 26→aa, 27→bb, etc.
    
    Args:
        bit_vec: Z3 bitvector or integer value
        N: number of bits (optional, only used for error handling)
        
    Returns:
        A string representation of the world state using letters
    """
    try:
        # Get integer value from bitvector
        if hasattr(bit_vec, 'as_long'):
            value = bit_vec.as_long()
        elif hasattr(bit_vec, 'sexpr'):
            # Handle different formats of bit vector representation
            bit_vec_as_string = bit_vec.sexpr()
            if 'x' in bit_vec_as_string:  # hexadecimal format
                value = int(bit_vec_as_string[2:], 16)
            elif bit_vec_as_string.startswith('#b'):  # binary format
                value = int(bit_vec_as_string[2:], 2)
            else:  # decimal format
                value = int(bit_vec_as_string)
        elif isinstance(bit_vec, int):
            value = bit_vec
        else:
            return f"<unknown-{bit_vec}>"
            
        # Convert integer to letter representation
        if value < 26:
            # Single letter for values 0-25 (a-z)
            return chr(97 + value)  # ASCII 'a' starts at 97
        else:
            # Double letters for values >= 26 (aa, bb, etc.)
            letter_idx = value % 26
            repeat = value // 26 + 1
            letter = chr(97 + letter_idx)
            return letter * repeat
            
    except (AttributeError, ValueError):
        return f"<unknown-{bit_vec}>"