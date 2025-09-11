"""Custom exception classes for syntactic operations.

This module provides a hierarchy of exceptions for handling errors
in formula parsing, validation, and transformation operations.
"""

from typing import Dict, Any, Optional, Union


class SyntacticError(Exception):
    """Base exception for all syntactic operations.
    
    Provides context-aware error reporting with formula details,
    position information, and helpful suggestions for resolution.
    """
    
    def __init__(
        self, 
        message: str,
        formula: Optional[str] = None,
        position: Optional[int] = None,
        context: Optional[Dict[str, Any]] = None
    ):
        """Initialize syntactic error with context.
        
        Args:
            message: Human-readable error description
            formula: The formula that caused the error
            position: Character position where error occurred
            context: Additional context like suggestions or details
        """
        super().__init__(message)
        self.formula = formula
        self.position = position
        self.context = context or {}


class ParseError(SyntacticError):
    """Raised when formula parsing fails.
    
    Indicates issues with converting from infix to prefix notation
    or other parsing-related failures.
    """
    pass


class ValidationError(SyntacticError):
    """Raised when formula validation fails.
    
    Indicates issues with operator usage, arity mismatches,
    or other validation failures.
    """
    pass


class TransformationError(SyntacticError):
    """Raised when AST or formula transformation fails.
    
    Indicates issues during formula transformation operations
    like operator substitution or simplification.
    """
    pass


class SyntaxError(ParseError):
    """Raised for syntax errors in formulas.
    
    Specific to malformed formula syntax like unbalanced parentheses
    or invalid operator placement.
    """
    
    def __init__(self, message: str, formula: str, position: int):
        """Initialize syntax error with specific position.
        
        Args:
            message: Description of the syntax issue
            formula: The malformed formula
            position: Exact position of syntax error
        """
        super().__init__(
            message=f"Syntax error at position {position}: {message}",
            formula=formula,
            position=position
        )


class UnbalancedParenthesesError(ParseError):
    """Raised when parentheses are unbalanced in a formula.
    
    Provides specific information about missing or extra parentheses.
    """
    
    def __init__(self, formula: str, open_count: int, close_count: int):
        """Initialize with parenthesis counts.
        
        Args:
            formula: The formula with unbalanced parentheses
            open_count: Number of opening parentheses
            close_count: Number of closing parentheses
        """
        if open_count > close_count:
            message = f"Missing {open_count - close_count} closing parenthes{'is' if open_count - close_count == 1 else 'es'}"
        else:
            message = f"Extra {close_count - open_count} closing parenthes{'is' if close_count - open_count == 1 else 'es'}"
        
        super().__init__(
            message=message,
            formula=formula,
            context={
                'open_count': open_count,
                'close_count': close_count,
                'suggestion': 'Check parentheses balance in the formula'
            }
        )


class UnknownOperatorError(ValidationError):
    """Raised when an unknown operator is encountered.
    
    Provides information about the unknown operator and available alternatives.
    """
    
    def __init__(self, operator: str, available_operators: Optional[list] = None):
        """Initialize with operator information.
        
        Args:
            operator: The unknown operator
            available_operators: List of valid operators
        """
        message = f"Unknown operator: {operator}"
        context = {'operator': operator}
        
        if available_operators:
            context['available'] = available_operators
            context['suggestion'] = f"Available operators: {', '.join(available_operators[:5])}"
            if len(available_operators) > 5:
                context['suggestion'] += f" and {len(available_operators) - 5} more"
        
        super().__init__(
            message=message,
            context=context
        )


class InvalidFormulaError(ValidationError):
    """Raised when formula structure is invalid.
    
    Covers various structural issues like empty formulas,
    invalid nesting, or malformed expressions.
    """
    pass


class CircularDefinitionError(ValidationError):
    """Raised when circular operator definitions are detected.
    
    Occurs when defined operators reference themselves directly
    or through a chain of other definitions.
    """
    
    def __init__(self, operator: str, chain: list):
        """Initialize with circular dependency information.
        
        Args:
            operator: The operator with circular definition
            chain: The chain of operators forming the cycle
        """
        cycle_str = " -> ".join(chain) + f" -> {operator}"
        super().__init__(
            message=f"Circular definition detected for operator '{operator}'",
            context={
                'operator': operator,
                'cycle': cycle_str,
                'chain': chain,
                'suggestion': 'Break the circular dependency by redefining one of the operators'
            }
        )


class ArityError(ValidationError):
    """Raised when operator arity doesn't match usage.
    
    Indicates mismatch between expected and actual number of arguments.
    """
    
    def __init__(self, operator: str, expected: int, actual: int):
        """Initialize with arity information.
        
        Args:
            operator: The operator with arity mismatch
            expected: Expected number of arguments
            actual: Actual number of arguments provided
        """
        super().__init__(
            message=f"Operator '{operator}' expects {expected} argument(s), got {actual}",
            context={
                'operator': operator,
                'expected_arity': expected,
                'actual_arity': actual,
                'suggestion': f"Provide exactly {expected} argument(s) for '{operator}'"
            }
        )


class DuplicateOperatorError(ValidationError):
    """Raised when attempting to register a duplicate operator.
    
    Prevents operator name conflicts in the collection.
    """
    
    def __init__(self, operator_name: str, existing_class: str):
        """Initialize with duplication information.
        
        Args:
            operator_name: Name of the duplicate operator
            existing_class: Class name of existing operator
        """
        super().__init__(
            message=f"Operator '{operator_name}' already registered",
            context={
                'operator': operator_name,
                'existing_class': existing_class,
                'suggestion': 'Use a different name or remove the existing operator first'
            }
        )