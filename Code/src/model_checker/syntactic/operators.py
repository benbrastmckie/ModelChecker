"""
Operator classes for logical formula processing.

This module provides the base classes for all logical operators in the model checker:
- Operator: Abstract base class for all logical operators
- DefinedOperator: Base class for operators defined in terms of other operators
"""

import inspect

from model_checker.utils import (
    bitvec_to_substates,
    not_implemented_string,
    pretty_set_print,
)


class Operator:
    """Base class for all logical operators in the model checker.
    
    This abstract class defines the interface and common functionality for all logical
    operators in the system. It provides core functionality for operator instantiation,
    equality testing, and printing methods used in result visualization.
    
    Concrete operator classes must implement specific semantic functions such as:
    - true_at/false_at: For truth/falsity conditions
    - extended_verify/extended_falsify: For hyperintensional semantics 
    - find_verifiers_and_falsifiers: For finding exact verification sets
    - print_method: For displaying evaluation details
    
    Class Attributes:
        name (str): The symbol representing this operator
        arity (int): The number of arguments this operator takes
        primitive (bool): Whether this operator is primitive (default: True)
    
    Attributes:
        semantics (object): The semantics object this operator uses for evaluation
    """

    name = None
    arity = None
    primitive = True

    def __init__(self, semantics):
        op_class = self.__class__.__name__
        if self.__class__ == Operator:
            raise NotImplementedError(not_implemented_string(op_class))
        if self.name is None or self.arity is None:
            raise NameError(
                f"Your operator class {op_class} is missing a name or an arity. "
                + f"Please add them as class properties of {op_class}."
            )
        self.semantics = semantics

    def __str__(self):
        return str(self.name)

    def __repr__(self):
        return str(self.name)

    def __eq__(self, other):
        if isinstance(other, Operator):
            return self.name == other.name and self.arity == other.arity
        return False

    def __hash__(self):
        return hash((self.name, self.arity))

    def general_print(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints a general evaluation of a sentence at a given evaluation point.

        This method provides a standard way to print a sentence's evaluation results,
        including the sentence itself and its subformulas (arguments) recursively.

        Args:
            sentence_obj (Sentence): The sentence object to be printed
            eval_point (dict): The evaluation point containing world, time, and other context
            indent_num (int): The number of indentation levels for formatting
            use_colors (bool): Whether to use ANSI color codes in the output

        The method first prints the proposition for the sentence at the given evaluation
        point, then recursively prints all subformulas (if any) with increased indentation.
        """
        proposition = sentence_obj.proposition
        model_structure = proposition.model_structure

        proposition.print_proposition(eval_point, indent_num, use_colors)
        indent_num += 1

        if sentence_obj.original_arguments:
            for arg in sentence_obj.original_arguments:
                model_structure.recursive_print(arg, eval_point, indent_num, use_colors)

    # TODO: make this method more deterministic
    def print_over_worlds(self, sentence, eval_point, all_worlds, indent_num, use_colors):
        """Print evaluation details for modal/counterfactual operators across possible worlds.

        This method handles the printing of evaluation results for modal and counterfactual
        operators, showing both the evaluation in the current world and in alternative worlds.
        For counterfactuals, it prints the antecedent in the evaluation world and the
        consequent in each alternative world.

        Args:
            sentence (Sentence): The sentence object being evaluated
            eval_point (dict): The current evaluation point containing world and time info
            all_worlds (list): List of all relevant alternative worlds to consider
            indent_num (int): Number of spaces to indent the output
            use_colors (bool): Whether to use ANSI color codes in output

        The output format shows:
        1. The full sentence evaluation at the current point
        2. For unary operators: evaluation in each alternative world
        3. For binary operators: antecedent evaluation, followed by consequent
           evaluation in each alternative world
        """
        # Move to class or config for flexibility
        if use_colors:
            CYAN, RESET = '\033[36m', '\033[0m'
        else:
            CYAN, RESET = '', ''

        arguments = sentence.original_arguments
        proposition = sentence.proposition
        model_structure = proposition.model_structure
        N = proposition.N

        proposition.print_proposition(eval_point, indent_num, use_colors)
        indent_num += 1

        if len(arguments) == 1:
            sentence = arguments[0]
            for world in all_worlds:
                pass_point = eval_point.copy()
                # Set the world directly - could be a world_id (int) or world array
                # The downstream print_proposition method should handle both appropriately
                pass_point["world"] = world
                model_structure.recursive_print(sentence, pass_point, indent_num, use_colors)
                
        if len(arguments) == 2:
            left_argument, right_argument = arguments
            model_structure.recursive_print(left_argument, eval_point, indent_num, use_colors)
            indent_num += 1
            
            # TODO: is there an approach that is agnostic about what the eval_point includes?
            # Handle displaying world state for both traditional and new approach
            if "world" in eval_point:
                if "time" in eval_point and hasattr(eval_point["world"], "__getitem__"):
                    # Bimodal case: world is an array/mapping indexed by time
                    current_world_state = bitvec_to_substates(eval_point["world"][eval_point["time"]], N)
                elif hasattr(eval_point["world"], "as_ast") or isinstance(eval_point["world"], int):
                    # Default case: world is directly a bitvec
                    current_world_state = bitvec_to_substates(eval_point["world"], N)
                else:
                    # Any other case
                    current_world_state = str(eval_point["world"])
            else:
                current_world_state = "current world"
                
            other_world_strings = set()
            for world in all_worlds:
                try:
                    # Try to get the world state at the current time
                    if "time" in eval_point and hasattr(world, "__getitem__"):
                        # Bimodal case: world is an array/mapping indexed by time
                        world_state = bitvec_to_substates(world[eval_point["time"]], N)
                        other_world_strings.add(str(world_state))
                    elif hasattr(world, "as_ast") or isinstance(world, int):
                        # Default case: world is directly a bitvec
                        world_state = bitvec_to_substates(world, N)
                        other_world_strings.add(str(world_state))
                    else:
                        other_world_strings.add(str(world))
                except Exception as e:
                    # Add error information if needed for debugging
                    # print(f"Error getting world state: {e}")
                    other_world_strings.add(str(world))
                    
            print(
                f'{"  " * indent_num}{CYAN}|{left_argument}|-alternatives '
                f'to {current_world_state} = '
                f'{pretty_set_print(other_world_strings)}{RESET}'
            )
            
            indent_num += 1
            for alt_world in all_worlds:
                alt_point = eval_point.copy()
                # Set the world directly - could be a world_id (int) or world array
                # The downstream print_proposition method should handle both appropriately
                alt_point["world"] = alt_world
                model_structure.recursive_print(right_argument, alt_point, indent_num, use_colors)
    
    def print_over_times(self, sentence_obj, eval_point, other_times, indent_num, use_colors):
        """Print evaluation details for temporal operators across different time points.

        This method handles the printing of evaluation results for temporal operators,
        showing both the evaluation at the current time point and at other relevant
        time points. For binary temporal operators, it prints the first argument at
        the evaluation time and the second argument at each alternative time point.

        Args:
            sentence_obj (Sentence): The sentence object being evaluated
            eval_point (dict): The current evaluation point containing world and time info
            other_times (list): List of all relevant alternative time points to consider
            indent_num (int): Number of spaces to indent the output
            use_colors (bool): Whether to use ANSI color codes in output
        """
        if use_colors:
            CYAN, RESET = '\033[36m', '\033[0m'
        else:
            CYAN, RESET = '', ''

        arguments = sentence_obj.original_arguments
        proposition = sentence_obj.proposition
        model_structure = proposition.model_structure
        
        # Store the original time value to restore it later
        original_time = eval_point["time"]

        # Print the main proposition
        proposition.print_proposition(eval_point, indent_num, use_colors)
        indent_num += 1

        if len(arguments) == 1:
            # For unary operators like Future/Past, we evaluate at different times
            argument = arguments[0]
            for time in other_times:
                # Create a copy with updated time but same world
                temp_point = eval_point.copy()
                temp_point["time"] = time
                model_structure.recursive_print(argument, temp_point, indent_num, use_colors)
            
            # Restore the original time value
            eval_point["time"] = original_time
                
        if len(arguments) == 2:
            # For binary operators
            left_argument, right_argument = arguments
            model_structure.recursive_print(left_argument, eval_point, indent_num, use_colors)
            indent_num += 1
            
            # Display the time alternatives
            print(
                f'{"  " * indent_num}{CYAN}|{left_argument}|-alternatives '
                f'to time {eval_point["time"]} = '
                f'{pretty_set_print([f"t={t}" for t in other_times])}{RESET}'
            )
            
            indent_num += 1
            for alt_time in other_times:
                alt_point = eval_point.copy()
                alt_point["time"] = alt_time
                model_structure.recursive_print(right_argument, alt_point, indent_num, use_colors)
    

class DefinedOperator(Operator):
    """Represents a logical operator defined in terms of other operators.
    
    Defined operators are non-primitive operators that can be expressed using 
    combinations of more basic operators. For example, implication (→) can be 
    defined in terms of negation and disjunction (¬p ∨ q).
    
    Subclasses must implement the derived_definition method which specifies
    how the operator can be expressed in terms of other operators. The class
    validates that the arity matches the defined derivation.
    
    Class Attributes:
        primitive (bool): Always False for defined operators
        
    Required methods for subclasses:
        derived_definition(*args): Returns the definition in terms of other operators
    """

    primitive = False

    def derived_definition(self, *args):
        """
        Returns the definition of the operator in terms of other operators.
        
        This method specifies how a defined operator can be expressed using other
        (typically primitive) operators. For example, an implementation for implication
        might return ['∨', ['¬', arg1], arg2] where arg1 and arg2 are the arguments.
        
        Args:
            *args: The arguments to the operator (number must match the operator's arity)
            
        Returns:
            list: A nested list structure representing the definition in prefix notation
            
        Raises:
            NotImplementedError: This method must be implemented by all subclasses
        """
        raise NotImplementedError(
            f"Derived operator class {self.__class__.__name__} must implement the derived_definition method."
        )

    def __init__(self, semantics):
        super().__init__(semantics)
        self._validate_arity()

    def _validate_arity(self):
        """
        Validates that the operator's declared arity matches its implementation.
        
        This method ensures consistency between the operator's declared 'arity' class attribute
        and the number of parameters in its 'derived_definition' method. This validation is
        crucial for maintaining type safety and preventing runtime errors.
        
        For example, if an operator declares arity=2 but its derived_definition method
        only accepts one argument (plus self), this validation will fail.
        
        Raises:
            AttributeError: If the operator class doesn't define an 'arity' attribute
            ValueError: If the declared arity doesn't match the number of parameters
                       in the derived_definition method
        """
        # Retrieve the signature of the derived_definition method
        signature = inspect.signature(self.derived_definition)
        params = list(signature.parameters.values())

        # Exclude 'self' if present
        if params and params[0].name == 'self':
            params = params[1:]

        derived_def_num_args = len(params)

        # Check if 'arity' is defined
        if not hasattr(self, 'arity'):
            raise AttributeError(
                f"{self.__class__.__name__} must define an 'arity' attribute."
            )

        # Validate that 'arity' matches the number of arguments
        if self.arity != derived_def_num_args:
            raise ValueError(
                f"The specified arity of {self.arity} for {self.__class__.__name__} does not match "
                f"the number of arguments ({derived_def_num_args}) for its 'derived_definition' method."
            )