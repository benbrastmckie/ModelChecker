"""
Correct Skolemized Implementation of Exclusion Operator

This module implements the SK exclusion operator strategy by extending the base
ExclusionOperatorBase class and providing a proper extended_verify method.
"""

import z3
from model_checker.utils import ForAll, Exists
from model_checker.theory_lib.exclusion.operators import ExclusionOperatorBase


class SK_ExclusionOperator(ExclusionOperatorBase):
    """Exclusion operator using Skolem functions for correct recursive semantics."""
    
    name = "\\exclude"
    arity = 1
    
    def __init__(self, semantics):
        super().__init__(semantics)
        self._sk_counter = 0
        
    def get_sk_id(self):
        """Get unique ID for Skolem function naming."""
        self._sk_counter += 1
        return self._sk_counter
    
    def extended_verify(self, state, argument, eval_point):
        """
        Implement extended verification using Skolem functions.
        
        This follows the three-condition pattern from the original exclusion
        semantics but uses Skolem functions h_sk and y_sk to encode the
        existential quantifiers properly.
        
        A state s verifies ¬A iff:
        1. For every verifier x of A, there exists y_sk(x) part of x where h_sk(x) excludes y_sk(x)
        2. For every verifier x of A, h_sk(x) is part of state s
        3. State s is minimal with respect to condition 2
        """
        # Abbreviations
        semantics = self.semantics
        N = semantics.N
        extended_verify = semantics.extended_verify
        excludes = semantics.excludes
        is_part_of = semantics.is_part_of
        
        # Create unique Skolem functions for this verification
        sk_id = self.get_sk_id()
        h_sk = z3.Function(f"h_sk_{sk_id}", z3.BitVecSort(N), z3.BitVecSort(N))
        y_sk = z3.Function(f"y_sk_{sk_id}", z3.BitVecSort(N), z3.BitVecSort(N))
        
        # Variables
        x, z = z3.BitVecs(f"sk_x_{sk_id} sk_z_{sk_id}", N)
        
        return z3.And(
            # Condition 1: For every verifier x of argument, y_sk(x) is part of x and h_sk(x) excludes y_sk(x)
            ForAll([x], z3.Implies(
                extended_verify(x, argument, eval_point),
                z3.And(
                    is_part_of(y_sk(x), x),
                    excludes(h_sk(x), y_sk(x))
                )
            )),
            
            # Condition 2: For every verifier x of argument, h_sk(x) is part of state
            ForAll([x], z3.Implies(
                extended_verify(x, argument, eval_point),
                is_part_of(h_sk(x), state)
            )),
            
            # Condition 3: State is minimal - for any z that satisfies condition 2, state is part of z
            ForAll([z], z3.Implies(
                ForAll([x], z3.Implies(
                    extended_verify(x, argument, eval_point),
                    is_part_of(h_sk(x), z)
                )),
                is_part_of(state, z)
            ))
        )


def create_sk_exclusion_operators():
    """Create operator collection with SK exclusion operator."""
    from model_checker.syntactic import OperatorCollection
    from model_checker.theory_lib.exclusion.operators import (
        UniAndOperator,
        UniOrOperator,
        UniIdentityOperator
    )
    
    operators = OperatorCollection()
    
    # Use SK exclusion operator
    operators.add_operator(SK_ExclusionOperator)
    
    # Use standard operators for the rest
    operators.add_operator(UniAndOperator)
    operators.add_operator(UniOrOperator)
    operators.add_operator(UniIdentityOperator)
    
    return operators