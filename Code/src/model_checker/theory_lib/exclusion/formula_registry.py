#!/usr/bin/env python3
"""
Formula Registry for ensuring formula consistency between constraint generation and evaluation.

This module implements the Formula Registry pattern to solve the false premise issue
by ensuring that the same formulas (with the same Skolem functions) are used in both
the constraint generation phase and the truth evaluation phase.
"""

import z3
from typing import Dict, Tuple, Any


class FormulaRegistry:
    """Registry to ensure formulas are created once and reused."""
    
    def __init__(self, semantics):
        """
        Initialize the registry.
        
        Args:
            semantics: The semantic structure instance
        """
        self.semantics = semantics
        self.atomic_formulas = {}  # Maps (sentence_letter, world) -> formula
        self.compound_formulas = {}  # Maps (operator, args, world) -> formula
        self.skolem_functions = {}  # Maps function_name -> z3.Function
        self.skolem_counter = 0
        
    def get_atomic_formula(self, sentence_letter, eval_world):
        """
        Get or create formula for atomic sentence.
        
        Args:
            sentence_letter: The atomic sentence letter
            eval_world: The world at which to evaluate
            
        Returns:
            Z3 formula for the atomic sentence
        """
        key = (str(sentence_letter), str(eval_world))
        
        if key not in self.atomic_formulas:
            # Create Skolem function
            func_name = f"f_atom_{sentence_letter}"
            if func_name not in self.skolem_functions:
                self.skolem_counter += 1
                f_atom = z3.Function(
                    func_name,
                    z3.BitVecSort(self.semantics.N),
                    z3.BitVecSort(self.semantics.N)
                )
                self.skolem_functions[func_name] = f_atom
            else:
                f_atom = self.skolem_functions[func_name]
            
            # Create formula
            formula = z3.And(
                self.semantics.is_part_of(f_atom(eval_world), eval_world),
                self.semantics.verify(f_atom(eval_world), sentence_letter)
            )
            self.atomic_formulas[key] = formula
            
        return self.atomic_formulas[key]
    
    def get_exclusion_formula(self, operator, argument, eval_world):
        """
        Get or create formula for exclusion operator.
        
        Args:
            operator: The exclusion operator instance
            argument: The argument to the exclusion operator
            eval_world: The world at which to evaluate
            
        Returns:
            Z3 formula for the exclusion operator application
        """
        # Create a unique key based on the operator and argument structure
        arg_str = self._serialize_argument(argument)
        key = (operator.name, arg_str, str(eval_world))
        
        if key not in self.compound_formulas:
            # Create the formula using consistent Skolem functions
            formula = self._create_exclusion_formula(operator, argument, eval_world)
            self.compound_formulas[key] = formula
            
        return self.compound_formulas[key]
    
    def _serialize_argument(self, argument):
        """
        Create a string representation of an argument for use as a key.
        
        Args:
            argument: The argument to serialize
            
        Returns:
            String representation of the argument
        """
        if hasattr(argument, 'sentence_letter') and argument.sentence_letter is not None:
            return f"atom_{argument.sentence_letter}"
        elif hasattr(argument, 'operator') and argument.operator is not None:
            op_name = argument.operator.name
            args = argument.arguments or ()
            arg_strs = [self._serialize_argument(arg) for arg in args]
            return f"{op_name}({','.join(arg_strs)})"
        else:
            return str(argument)
    
    def _create_exclusion_formula(self, operator, argument, eval_world):
        """
        Create skolemized exclusion formula.
        
        Args:
            operator: The exclusion operator
            argument: The argument to the operator
            eval_world: The evaluation world
            
        Returns:
            Skolemized formula for exclusion
        """
        from model_checker.utils import Exists
        
        # Create the exclusion formula directly
        # This matches what ExclusionOperatorBase.true_at does
        N = self.semantics.N
        
        # Create a unique variable for this exclusion
        # Use the argument serialization to make it unique
        arg_str = self._serialize_argument(argument)
        x = z3.BitVec(f"ver_exclude_{arg_str}_{self.skolem_counter}", N)
        self.skolem_counter += 1
        
        eval_point = {"world": eval_world}
        
        # The exclusion formula: ∃x. (x verifies argument ∧ x ⊑ eval_world)
        return Exists(
            x,
            z3.And(
                self.semantics.extended_verify(x, argument, eval_point),
                self.semantics.is_part_of(x, eval_world)
            )
        )
    
    def clear(self):
        """Clear all cached formulas and reset counters."""
        self.atomic_formulas.clear()
        self.compound_formulas.clear()
        self.skolem_functions.clear()
        self.skolem_counter = 0