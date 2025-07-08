"""
Utility functions for the model checker system.

This module provides various helper functions for manipulating bit vectors,
parsing logical expressions, and converting between different representations
used throughout the model checker.

It also includes functions for versioning and licensing information.

NOTES:
- Any LaTeX commands must have double backslash 
- Operators include `\\` (e.g., `\\wedge`) and sentence letters do not
- The operators `\\top` and `\\bot` are reserved for tautology and contradiction
"""

### IMPORTS AND DEFINITIONS ###

import string
import os
import importlib
import datetime
from importlib.metadata import version

from z3 import(
    And,
    BitVecVal,
    Or,
    substitute,
)

class Z3ContextManager:
    """Provides centralized management of Z3 solver contexts.
    
    This class ensures proper isolation between different solver instances by explicitly
    resetting the Z3 global context when needed. It implements a fail-fast approach
    and enforces deterministic behavior by preventing state leakage between examples.
    """
    
    @staticmethod
    def reset_context():
        """Explicitly reset the Z3 global context.
        
        This method forces Z3 to create a fresh context for the next solver instance,
        ensuring complete isolation between different examples.
        
        Note: Z3 stores its context in either '_main_ctx' or 'main_ctx' depending on
        the Z3 version. This method handles both cases for maximum compatibility.
        """
        import z3
        
        # Handle both possible attribute names for Z3 context
        if hasattr(z3, '_main_ctx'):
            # Reset the context completely
            z3._main_ctx = None
            
        elif hasattr(z3, 'main_ctx'):
            z3.main_ctx = None
            
        # Try to clear other Z3 caches that might persist
        if hasattr(z3, 'clear_parser_cache'):
            z3.clear_parser_cache()
            
        # Re-import z3 to use the new context
        import importlib
        importlib.reload(z3)

### SYNTACTIC HELPERS ###

def parse_expression(tokens):
    """Parses a list of tokens representing a propositional expression and returns
    the expression in prefix notation.
    """
    if not tokens:  # Check if tokens are empty before processing
        raise ValueError("Empty token list")
    token = tokens.pop(0)  # Get the next token
    if token == "(":  # Handle binary operator case (indicated by parentheses)
        if not tokens:  # Check if tokens are empty after removing first token
            raise ValueError(f"Empty token list after opening parenthesis")
        closing_parentheses = tokens.pop()  # Remove the closing parenthesis
        if closing_parentheses != ")":
            raise SyntaxError(
                f"The sentence {tokens} is missing a closing parenthesis."
            )
        if not tokens:  # Check if tokens are empty after removing parentheses
            raise ValueError(f"Empty token list after removing parentheses")
        operator, left, right = op_left_right(tokens)
        left_arg, left_comp = parse_expression(left)  # Parse the left argument
        right_arg, right_comp = parse_expression(right)  # Parse the right argument
        complexity = left_comp + right_comp + 1
        return [operator, left_arg, right_arg], complexity 
    if token.isalnum():  # Handle atomic sentences
        return [token], 0
    elif token.startswith("\\"):  # Handle all LaTeX operators 
        # This includes: \top, \bot, \Future, \Past, \future, \past, etc.
        # Special case for nullary operators like \top and \bot
        if token in {"\\top", "\\bot"}:
            return [token], 0
        if not tokens:  # Check if tokens are empty after operator
            raise ValueError(f"Empty token list after operator {token}")
        arg, comp = parse_expression(tokens)
        return [token, arg], comp + 1
    arg, comp = parse_expression(tokens)
    return [token, arg], comp + 1 

def op_left_right(tokens):
    """Divides whatever is inside a pair of parentheses into the left argument,
    right argument, and the operator."""

    def balanced_parentheses(tokens):
        """Check if parentheses are balanced in the argument."""
        stack = []
        for token in tokens:
            if token == "(":
                stack.append(token)
            elif token == ")":
                if not stack:
                    return False
                stack.pop()
        return len(stack) == 0

    def check_right(tokens, operator):
        if not tokens:
            raise ValueError(f"Expected an argument after the operator {operator}")
        if not balanced_parentheses(tokens):
            raise ValueError(
                f"Unbalanced parentheses for the tokens {tokens} " + 
                f"with the operator {operator}."
            )
        return tokens  # Remaining tokens are the right argument

    def cut_parentheses(left, tokens):
        count = 1  # To track nested parentheses
        while tokens:
            token = tokens.pop(0)
            if token == "(":
                count += 1
                left.append(token)
            elif token == ")":
                count -= 1
                left.append(token)
            elif count > 0:
                left.append(token)
            elif not tokens:
                raise ValueError(f"Extra parentheses in {tokens}.")
            else:
                operator = token
                right = check_right(tokens, operator)
                return operator, left, right
        raise ValueError(f"The expression {tokens} is incomplete.")

    def process_operator(tokens):
        if tokens:
            return tokens.pop(0)
        raise ValueError("Operator missing after operand")

    def extract_arguments(tokens):
        """Extracts the left argument and right argument from tokens."""
        left = []
        while tokens:
            token = tokens.pop(0)
            if token == "(":
                left.append(token)
                return cut_parentheses(left, tokens)
            elif token.isalnum() or token in {"\\top", "\\bot"}:
                left.append(token)
                operator = process_operator(tokens)
                right = check_right(tokens, operator)
                return operator, left, right
            else:
                left.append(token)
        raise ValueError("Invalid expression or unmatched parentheses")

    result = extract_arguments(tokens)
    if result is None:
        raise ValueError("Failed to extract arguments")
    return result



### PRINT HELPERS ###

def pretty_set_print(set_with_strings):
    """Formats a set of strings for readable display.
    
    This function takes a set of strings and returns a properly formatted string
    representation with the elements sorted and separated by commas. It removes
    quotation marks from the elements and displays an empty set using the
    mathematical empty set symbol.
    
    Args:
        set_with_strings (set): A set containing string elements
        
    Returns:
        str: A formatted string representation of the set
        
    Examples:
        >>> pretty_set_print({'a', 'c', 'b'})
        '{a, b, c}'
        >>> pretty_set_print(set())
        '∅'
    """
    sorted_set = sorted(list(set_with_strings))  # actually type list, not set
    print_str = "{"
    for i, elem in enumerate(sorted_set):
        print_str += elem
        if i != len(sorted_set) - 1:
            print_str += ", "
    print_str += "}"
    return print_str if print_str != "{}" else '∅'

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


# def bitvec_to_substates(bit_vec, N):
#     '''converts bitvectors to fusions of atomic states.'''
#     bit_vec_as_string = bit_vec.sexpr()
#     if 'x' in bit_vec_as_string: # if we have a hexadecimal, ie N=4m
#         integer = int(bit_vec_as_string[2:],16)
#         bit_vec_as_string = int_to_binary(integer, N)
#     bit_vec_backwards = bit_vec_as_string[::-1]
#     state_repr = ""
#     for i, char in enumerate(bit_vec_backwards):
#         if char == "b":
#             if not state_repr:
#                 return "□"  #  null state
#             return state_repr[0 : len(state_repr) - 1]
#         if char == "1":
#             state_repr += index_to_substate(i)
#             state_repr += "."
#     raise ValueError("should have run into 'b' at the end but didn't")


# TODO: refactor creating a worlds-specific function
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


### Z3 HELPERS ###

# def z3_set_to_python_set(z3_set, domain):
#     python_set = set()
#     for elem in domain:
#         if z3.simplify(z3.IsMember(elem, z3_set)):
#             python_set.add(elem)
#     return python_set

# def z3_simplify(z3_expr):
#     """
#     This will get rid of need for all the bit_ functions.
#     However, it does not get rid of e.g. find_compatible_parts.
#     """
#     if isinstance(z3_expr, BoolRef):
#         return bool(simplify(z3_expr))
#     return simplify(z3_expr)

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




### ERROR REPORTING ###

def not_implemented_string(cl_name):
    """Return a message for NotImplemented Errors on Operator and Proposition classes.
    The error is raised when a user creates an Operator object or a Proposition object,
    and directs them to implement a subclass and create instances of the subclass."""
    if cl_name == "PropositionDefaults":
        return (f"User should implement subclass(es) of {cl_name} for propositions. The "
            f"{cl_name} class should never be instantiated.")
    return (f"User should implement subclass(es) of {cl_name} for {cl_name.lower()}s. The "
            f"{cl_name} class should never be instantiated.")

def flatten(structured_list):
    """
    helper for making sure that derived operators are not defined in terms of each other.
    takes in a list of lists; returns that list of lists flattened. 
    can in principle flatten a list with any amount of embedding. 
    """
    flattened = []
    for elem in structured_list:
        if not isinstance(elem, list):
            flattened.append(elem)
        if isinstance(elem, list):
            flattened.extend(flatten(elem))
    return flattened


### API ###

def get_example(name, example_range):
    """Get a specific example by name from the provided example range
    
    Args:
        name (str): Name of the example to retrieve
        example_range (dict): Dictionary containing the examples
        
    Returns:
        list: [premises, conclusions, settings]
    """
    if name not in example_range:
        raise KeyError(f"Example {name} not found. Available examples: {list(example_range.keys())}")
    return example_range[name]

def get_theory(name, semantic_theories=None):
    """Get a specific semantic theory by name
    
    This function can be called in two ways:
    1. With just the theory name (e.g., 'default') - will automatically load the semantic theories
    2. With both name and semantic_theories - useful when you already have the semantic theories loaded
    
    Args:
        name (str): Name of the theory to retrieve (e.g., 'default', 'exclusion')
        semantic_theories (dict, optional): Dictionary containing semantic theories. 
                                           If None, will be loaded automatically.
        
    Returns:
        dict: Dictionary containing semantics, proposition, model, and operators
        
    Raises:
        ValueError: If the theory name is not found or the theory_lib module can't be loaded
        KeyError: If the specific theory is not found in the semantic_theories
    """
    # If semantic_theories is not provided, try to load it
    if semantic_theories is None:
        try:
            # Import here to avoid circular imports
            from model_checker.theory_lib import get_semantic_theories
            semantic_theories = get_semantic_theories(name)
        except ImportError as e:
            available_theories = []
            try:
                from model_checker.theory_lib import AVAILABLE_THEORIES
                available_theories = AVAILABLE_THEORIES
            except ImportError:
                pass
            
            raise ValueError(f"Could not load theory_lib module. Available theories: {available_theories}") from e
        except ValueError as e:
            raise ValueError(f"Theory '{name}' not found in theory_lib") from e
    
    # Handle special case for default theory which may have a different name
    if name == "default" and "default" not in semantic_theories and "Brast-McKie" in semantic_theories:
        return semantic_theories["Brast-McKie"]
    
    # For theories with only one variant, return that variant regardless of name
    if len(semantic_theories) == 1:
        return list(semantic_theories.values())[0]
    
    # Standard case - look up the theory by name
    if name not in semantic_theories:
        raise KeyError(f"Theory '{name}' not found. Available theories: {list(semantic_theories.keys())}")
    
    return semantic_theories[name]


### VERSIONING AND LICENSING ###

def get_model_checker_version():
    """Get the current model_checker package version.
    
    Returns:
        str: Current version as defined in pyproject.toml or "unknown"
    """
    try:
        return version("model-checker")
    except ImportError:
        # Try fallback method by reading __init__.py
        try:
            from model_checker import __version__
            return __version__
        except (ImportError, AttributeError):
            return "unknown"

def get_theory_version(theory_name):
    """Get the version of a specific theory.
    
    Args:
        theory_name (str): Name of the theory
        
    Returns:
        str: Theory version or "unknown" if not found
        
    Raises:
        ValueError: If theory_name is not a valid registered theory
    """
    try:
        # Import theory_lib
        from model_checker.theory_lib import AVAILABLE_THEORIES
        
        if theory_name not in AVAILABLE_THEORIES:
            raise ValueError(f"Theory '{theory_name}' not found. Available theories: {AVAILABLE_THEORIES}")
        
        # Import the theory module
        theory_module = importlib.import_module(f"model_checker.theory_lib.{theory_name}")
        
        # Get version
        if hasattr(theory_module, "__version__"):
            return theory_module.__version__
        
        return "unknown"
    except ImportError as e:
        raise ValueError(f"Could not load theory '{theory_name}': {str(e)}")

def check_theory_compatibility(theory_name):
    """Check if a theory is compatible with the current model_checker version.
    
    Args:
        theory_name (str): Name of the theory
        
    Returns:
        bool: True if compatible, False otherwise
        
    Raises:
        ValueError: If theory_name is not a valid registered theory
    """
    try:
        # Import theory_lib
        from model_checker.theory_lib import AVAILABLE_THEORIES
        
        if theory_name not in AVAILABLE_THEORIES:
            raise ValueError(f"Theory '{theory_name}' not found. Available theories: {AVAILABLE_THEORIES}")
        
        # Import the theory module
        theory_module = importlib.import_module(f"model_checker.theory_lib.{theory_name}")
        
        # Check if the theory has model_checker version info
        if hasattr(theory_module, "__model_checker_version__"):
            theory_mc_version = theory_module.__model_checker_version__
            current_mc_version = get_model_checker_version()
            
            # Simple version comparison for now
            # Could be enhanced with more sophisticated version comparison logic
            return theory_mc_version == current_mc_version
        
        # If no version info is available, assume compatible
        return True
    except ImportError:
        # If we can't import the theory, it's not compatible
        return False

def get_license_template(license_type="GPL-3.0", author_info=None):
    """Get license text for a specified license type (placeholder).
    
    Args:
        license_type (str): Type of license (GPL-3.0, MIT, etc.)
        author_info (dict): Author information (name, email, year)
        
    Returns:
        str: License text with author information filled in
    """
    year = datetime.datetime.now().year
    author_name = author_info.get("name", "[Author Name]") if author_info else "[Author Name]"
    
    return f"[LICENSE PLACEHOLDER - {license_type}]\nCopyright (c) {year} {author_name}"

### TESTING ###

def run_test(
    example_case,
    semantic_class,
    proposition_class,
    operator_collection,
    syntax_class,
    model_constraints,
    model_structure,
):
    """Run a model checking test with the given components.
    
    This function creates a complete model checking pipeline by instantiating
    the syntax, semantics, model constraints, and model structure with the
    provided components. It then checks if the resulting model matches the
    expected behavior defined in the example settings.
    
    Args:
        example_case (list): A list containing [premises, conclusions, settings]
        semantic_class: The semantic theory class to use
        proposition_class: The proposition class to use
        operator_collection (OperatorCollection): Collection of operators
        syntax_class: The syntax class to use (normally Syntax)
        model_constraints: The model constraints class to use
        model_structure: The model structure class to use
        
    Returns:
        bool: True if the model matches the expected behavior, False otherwise
    """
    premises, conclusions, settings = example_case
    example_syntax = syntax_class(premises, conclusions, operator_collection)
    semantics = semantic_class(settings)
    # Create model constraints
    model_constraints = model_constraints(
        settings,
        example_syntax,
        semantics,
        proposition_class,
    )
    # Create model structure
    model_structure = model_structure(
        model_constraints, 
        settings,
    )
    return model_structure.check_result()


class TestResultData:
    """Data class to hold detailed test analysis results."""
    
    def __init__(self):
        self.model_found = False
        self.check_result = False
        self.premise_evaluations = []
        self.conclusion_evaluations = []
        self.solving_time = 0.0
        self.z3_model_status = None
        self.function_witnesses = {}
        self.error_message = None
        self.strategy_name = None
        
    def is_valid_countermodel(self):
        """Check if this represents a valid countermodel (true premises, false conclusions)."""
        if not self.model_found:
            return False
        
        # All premises must be true
        premises_valid = all(self.premise_evaluations)
        # All conclusions must be false  
        conclusions_valid = all(not c for c in self.conclusion_evaluations)
        
        return premises_valid and conclusions_valid


def run_enhanced_test(
    example_case,
    semantic_class,
    proposition_class,
    operator_collection,
    syntax_class,
    model_constraints,
    model_structure,
    strategy_name="default"
):
    """Run a model checking test with enhanced data collection.
    
    This function extends run_test to capture detailed evaluation data
    for analysis and comparison across different strategies.
    
    Args:
        example_case (list): A list containing [premises, conclusions, settings]
        semantic_class: The semantic theory class to use
        proposition_class: The proposition class to use
        operator_collection (OperatorCollection): Collection of operators
        syntax_class: The syntax class to use (normally Syntax)
        model_constraints: The model constraints class to use
        model_structure: The model structure class to use
        strategy_name (str): Name of the strategy being tested
        
    Returns:
        TestResultData: Detailed test results and analysis
    """
    import time
    
    result_data = TestResultData()
    result_data.strategy_name = strategy_name
    
    try:
        start_time = time.time()
        
        premises, conclusions, settings = example_case
        example_syntax = syntax_class(premises, conclusions, operator_collection)
        semantics = semantic_class(settings)
        
        # Create model constraints
        model_constraints_obj = model_constraints(
            settings,
            example_syntax,
            semantics,
            proposition_class,
        )
        
        # Create model structure
        model_structure_obj = model_structure(
            model_constraints_obj, 
            settings,
        )
        
        result_data.solving_time = time.time() - start_time
        result_data.check_result = model_structure_obj.check_result()
        result_data.z3_model_status = model_structure_obj.z3_model_status
        result_data.model_found = model_structure_obj.z3_model is not None
        
        # Extract detailed evaluation data if model was found
        if result_data.model_found and model_structure_obj.z3_model:
            try:
                # Interpret the sentences to get propositions
                model_structure_obj.interpret(example_syntax.premises)
                model_structure_obj.interpret(example_syntax.conclusions)
                
                # Debug: Check if sentences exist and have propositions
                premise_count = len(example_syntax.premises)
                conclusion_count = len(example_syntax.conclusions)
                
                # Evaluate premises
                for i, premise_sentence in enumerate(example_syntax.premises):
                    if hasattr(premise_sentence, 'proposition') and premise_sentence.proposition:
                        eval_result = premise_sentence.proposition.truth_value_at(
                            model_structure_obj.semantics.main_point
                        )
                        result_data.premise_evaluations.append(eval_result)
                    else:
                        # If no proposition was created, this indicates an interpretation issue
                        result_data.premise_evaluations.append(None)
                
                # Evaluate conclusions
                for i, conclusion_sentence in enumerate(example_syntax.conclusions):
                    if hasattr(conclusion_sentence, 'proposition') and conclusion_sentence.proposition:
                        eval_result = conclusion_sentence.proposition.truth_value_at(
                            model_structure_obj.semantics.main_point
                        )
                        result_data.conclusion_evaluations.append(eval_result)
                    else:
                        # If no proposition was created, this indicates an interpretation issue
                        result_data.conclusion_evaluations.append(None)
                        
            except Exception as interpret_error:
                # If interpretation fails, at least record the structure
                result_data.premise_evaluations = [None] * len(premises)
                result_data.conclusion_evaluations = [None] * len(conclusions)
                if result_data.error_message is None:
                    result_data.error_message = f"Interpretation error: {interpret_error}"
        
        # Even if no model found, record the expected counts for analysis
        if not result_data.model_found:
            # Record expected counts based on example structure
            result_data.premise_evaluations = [None] * len(premises)
            result_data.conclusion_evaluations = [None] * len(conclusions)
            
            # Extract function witnesses if available
            if hasattr(model_structure_obj.semantics, 'extract_function_witness'):
                try:
                    result_data.function_witnesses = model_structure_obj.semantics.extract_function_witness(
                        model_structure_obj.z3_model
                    )
                except Exception as e:
                    result_data.function_witnesses = {"error": str(e)}
        
    except Exception as e:
        result_data.error_message = str(e)
        result_data.solving_time = time.time() - start_time if 'start_time' in locals() else 0.0
    
    return result_data


def run_strategy_test(
    example_case,
    strategy_name,
    semantic_class=None,
    proposition_class=None,
    syntax_class=None,
    model_constraints=None,
    model_structure=None
):
    """Run a model checking test with a specific exclusion strategy.
    
    This is a convenience function that automatically creates the operator collection
    for the specified strategy and runs the enhanced test.
    
    Args:
        example_case (list): A list containing [premises, conclusions, settings]
        strategy_name (str): Name of exclusion strategy ("QA", "QI", "QI2", "BQI", "NF", "NA")
        semantic_class: The semantic theory class to use (defaults to ExclusionSemantics)
        proposition_class: The proposition class to use (defaults to UnilateralProposition)
        syntax_class: The syntax class to use (defaults to Syntax)
        model_constraints: The model constraints class to use (defaults to ModelConstraints)
        model_structure: The model structure class to use (defaults to ExclusionStructure)
        
    Returns:
        TestResultData: Detailed test results and analysis
        
    Raises:
        ValueError: If strategy_name is not recognized
    """
    # Import default classes if not provided
    if semantic_class is None:
        from model_checker.theory_lib.exclusion import ExclusionSemantics
        semantic_class = ExclusionSemantics
    
    if proposition_class is None:
        from model_checker.theory_lib.exclusion import UnilateralProposition
        proposition_class = UnilateralProposition
    
    if syntax_class is None:
        from model_checker import Syntax
        syntax_class = Syntax
    
    if model_constraints is None:
        from model_checker import ModelConstraints
        model_constraints = ModelConstraints
    
    if model_structure is None:
        from model_checker.theory_lib.exclusion import ExclusionStructure
        model_structure = ExclusionStructure
    
    # Create operator collection for the specified strategy
    from model_checker.theory_lib.exclusion.operators import create_operator_collection
    operator_collection = create_operator_collection(strategy_name)
    
    # Run the enhanced test with the strategy-specific operator collection
    return run_enhanced_test(
        example_case=example_case,
        semantic_class=semantic_class,
        proposition_class=proposition_class,
        operator_collection=operator_collection,
        syntax_class=syntax_class,
        model_constraints=model_constraints,
        model_structure=model_structure,
        strategy_name=strategy_name
    )

