"""
Operators that work with witness predicates.

This module implements logical operators that can query witness predicates
from the model to determine verifiers. The key innovation is that exclusion
verification can be computed by checking the three conditions using the
witness predicates stored in the model.
"""

import z3
from model_checker.syntactic import Operator, OperatorCollection
from model_checker.utils import ForAll, Exists
from typing import List, Set, Optional
from .semantic import WitnessAwareModel


class UniNegationOperator(Operator):
    """
    UniNegation operator that queries witness predicates from the model.
    """
    
    name = "\\func_unineg"
    arity = 1
    
    def true_at(self, arg, eval_point):
        """UniNegation is true when there's a verifier in the evaluation world."""
        x = z3.BitVec(f"ver_{self.semantics.counter}", self.semantics.N)
        self.semantics.counter += 1
        
        return Exists(
            [x],
            z3.And(
                self.extended_verify(x, arg, eval_point),
                self.semantics.is_part_of(x, eval_point["world"])
            )
        )
        
    def compute_verifiers(self, argument, model, eval_point):
        """
        Compute verifiers by querying witness predicates.
        """
        # Require witness-aware model
        assert isinstance(model, WitnessAwareModel), \
            "UniNegationOperator requires WitnessAwareModel with witness predicates"
            
        # Get verifiers of the argument
        arg_verifiers = self.semantics.extended_compute_verifiers(
            argument, model, eval_point
        )
        
        # Get formula string for witness lookup
        formula_str = f"\\func_unineg({self.semantics._formula_to_string(argument)})"
        
        verifiers = []
        for state in range(2**self.semantics.N):
            if self._verifies_uninegation_with_predicates(
                state, formula_str, arg_verifiers, model
            ):
                verifiers.append(state)
                
        return verifiers
        
    def _verifies_uninegation_with_predicates(self, state: int, formula_str: str,
                                          arg_verifiers: List[int],
                                          model: WitnessAwareModel) -> bool:
        """
        Check if state verifies uninegation using witness predicates.
        """
        # Require witness predicates for this formula
        assert model.has_witness_for(formula_str), \
            f"Missing witness predicates for formula: {formula_str}"
            
        # Verify three conditions using witness predicates
        # Condition 1 & 2: For each verifier, check h and y values
        for v in arg_verifiers:
            h_v = model.get_h_witness(formula_str, v)
            y_v = model.get_y_witness(formula_str, v)
            
            assert h_v is not None and y_v is not None, \
                f"Witness values must exist for verifier {v} in formula {formula_str}"
                
            # Check condition 1: y_v ⊑ v and h_v excludes y_v
            if not self._eval_is_part_of(y_v, v, model):
                return False
            if not self._eval_excludes(h_v, y_v, model):
                return False
                
            # Check condition 2: h_v ⊑ state
            if not self._eval_is_part_of(h_v, state, model):
                return False
                
        # Check condition 3: minimality
        if not self._check_minimality(state, formula_str, arg_verifiers, model):
            return False
            
        return True
        
    def _check_minimality(self, state: int, formula_str: str,
                         arg_verifiers: List[int],
                         model: WitnessAwareModel) -> bool:
        """
        Check minimality condition using witness predicates.
        """
        # For each proper part z of state
        for z in range(2**self.semantics.N):
            if z == state:
                continue
                
            if not self._eval_is_part_of(z, state, model):
                continue
                
            # Check if all h values fit in z
            all_h_fit_in_z = True
            for v in arg_verifiers:
                h_v = model.get_h_witness(formula_str, v)
                assert h_v is not None, f"h witness must exist for verifier {v}"
                if not self._eval_is_part_of(h_v, z, model):
                    all_h_fit_in_z = False
                    break
                        
            if all_h_fit_in_z:
                # z should not satisfy condition 1
                z_satisfies_cond1 = True
                for v in arg_verifiers:
                    h_v = model.get_h_witness(formula_str, v)
                    y_v = model.get_y_witness(formula_str, v)
                    
                    assert h_v is not None and y_v is not None, \
                        f"Witness values must exist for verifier {v}"
                        
                    if not (self._eval_is_part_of(y_v, v, model) and
                           self._eval_excludes(h_v, y_v, model)):
                        z_satisfies_cond1 = False
                        break
                        
                if z_satisfies_cond1:
                    # Minimality violated
                    return False
                    
        return True
        
    def _eval_is_part_of(self, x: int, y: int, model: WitnessAwareModel) -> bool:
        """Evaluate is_part_of relation using the model."""
        x_bv = z3.BitVecVal(x, self.semantics.N)
        y_bv = z3.BitVecVal(y, self.semantics.N)
        result = model.eval(self.semantics.is_part_of(x_bv, y_bv))
        return z3.is_true(result)
        
    def _eval_excludes(self, x: int, y: int, model: WitnessAwareModel) -> bool:
        """Evaluate excludes relation using the model."""
        x_bv = z3.BitVecVal(x, self.semantics.N)
        y_bv = z3.BitVecVal(y, self.semantics.N)
        result = model.eval(self.semantics.excludes(x_bv, y_bv))
        return z3.is_true(result)
        
    def eval_fusion(self, x: int, y: int, model) -> Optional[int]:
        """Evaluate fusion operation using the model."""
        x_bv = z3.BitVecVal(x, self.semantics.N)
        y_bv = z3.BitVecVal(y, self.semantics.N)
        result = model.eval(self.semantics.fusion(x_bv, y_bv))
        if z3.is_bv_value(result):
            return result.as_long()
        return None
        
    def extended_verify(self, state, argument, eval_point):
        """
        Implement three-condition uninegation semantics with witness predicates.
        
        This implements the full uninegation semantics directly in the operator,
        making it modular and self-contained while using witness predicates
        for the existential quantification.
        """
        # Abbreviations
        sem = self.semantics
        N = sem.N
        extended_verify = sem.extended_verify
        excludes = sem.excludes
        is_part_of = sem.is_part_of
        
        # Get formula string for witness lookup
        # Handle different argument types
        if hasattr(argument, 'sentence_letter') and argument.sentence_letter is not None:
            # Z3 expression - extract the name
            if hasattr(argument.sentence_letter, 'decl') and hasattr(argument.sentence_letter.decl(), 'name'):
                arg_str = argument.sentence_letter.decl().name()
            else:
                arg_str = str(argument.sentence_letter)
        elif hasattr(argument, 'name'):
            arg_str = argument.name
        elif hasattr(argument, 'proposition'):
            arg_str = argument.proposition
        else:
            arg_str = str(argument)
            
        formula_str = f"\\func_unineg({arg_str})"
        
        # Ensure witness predicates are registered for this formula
        if f"{formula_str}_h" not in sem.witness_registry.predicates:
            sem.witness_registry.register_witness_predicates(formula_str)
            
        # Get witness predicates for this formula - they must exist
        h_pred = sem.witness_registry.predicates[f"{formula_str}_h"]
        y_pred = sem.witness_registry.predicates[f"{formula_str}_y"]
        
        # Use witness predicates for the three-condition semantics
        x = z3.BitVec(f"wp_x_{sem.counter}", N)
        z = z3.BitVec(f"wp_z_{sem.counter}", N)
        sem.counter += 1

        return z3.And(
            # Condition 1: For every verifier x of argument, 
            # y_pred(x) is part of x and h_pred(x) excludes y_pred(x)
            ForAll([x], z3.Implies(
                extended_verify(x, argument, eval_point), 
                z3.And(
                    is_part_of(y_pred(x), x), 
                    excludes(h_pred(x), y_pred(x))
                )
            )),
            
            # Condition 2 (Upper Bound): For every verifier x of argument, 
            # h_pred(x) is part of state
            ForAll([x], z3.Implies(
                extended_verify(x, argument, eval_point), 
                is_part_of(h_pred(x), state)
            )),
            
            # Condition 3 (Least Upper Bound): state is the smallest state 
            # satisfying the UB condition
            ForAll([z], z3.Implies(
                ForAll([x], z3.Implies(
                    extended_verify(x, argument, eval_point), 
                    is_part_of(h_pred(x), z)
                )), 
                is_part_of(state, z)
            ))
        )
        
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print uninegation."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class UniConjunctionOperator(Operator):
    """Conjunction operator for witness semantics."""
    
    name = "\\uniwedge"
    arity = 2
    
    def true_at(self, leftarg, rightarg, eval_point):
        """Conjunction is true when both arguments are true."""
        sem = self.semantics
        return z3.And(
            sem.true_at(leftarg, eval_point),
            sem.true_at(rightarg, eval_point)
        )
        
    def compute_verifiers(self, arg1, arg2, model, eval_point):
        """Standard conjunction semantics using product of verifier sets."""
        # Get verifiers for each argument by using the semantics' verifier computation
        ver1 = self.semantics.extended_compute_verifiers(arg1, model, eval_point)
        ver2 = self.semantics.extended_compute_verifiers(arg2, model, eval_point)
        
        # Use product method to compute all fusions
        return self.semantics.product(set(ver1), set(ver2))
        
    def extended_verify(self, state, arg1, arg2, eval_point):
        """Standard conjunction constraint."""
        x1 = z3.BitVec(f'conj_x1_{self.semantics.counter}', self.semantics.N)
        x2 = z3.BitVec(f'conj_x2_{self.semantics.counter}', self.semantics.N)
        self.semantics.counter += 1
        
        # Use the same structure as the main exclusion theory
        from model_checker.utils import Exists
        return Exists(
            [x1, x2],
            z3.And(
                self.semantics.fusion(x1, x2) == state,
                self.semantics.extended_verify(x1, arg1, eval_point),
                self.semantics.extended_verify(x2, arg2, eval_point),
            )
        )
        
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print conjunction."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class UniDisjunctionOperator(Operator):
    """Disjunction operator for witness semantics."""
    
    name = "\\univee"
    arity = 2
    
    def true_at(self, leftarg, rightarg, eval_point):
        """Disjunction is true when at least one argument is true."""
        sem = self.semantics
        return z3.Or(
            sem.true_at(leftarg, eval_point), 
            sem.true_at(rightarg, eval_point)
        )
        
    def compute_verifiers(self, arg1, arg2, model, eval_point):
        """Standard disjunction semantics."""
        ver1 = self.semantics.extended_compute_verifiers(arg1, model, eval_point)
        ver2 = self.semantics.extended_compute_verifiers(arg2, model, eval_point)
        
        # Union of verifiers
        return list(set(ver1 + ver2))
        
    def extended_verify(self, state, arg1, arg2, eval_point):
        """Standard disjunction constraint."""
        return z3.Or(
            self.semantics.extended_verify(state, arg1, eval_point),
            self.semantics.extended_verify(state, arg2, eval_point)
        )
        
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print disjunction."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class UniIdentityOperator(Operator):
    """Identity operator for witness semantics."""
    
    name = "\\uniequiv"
    arity = 2
    
    def true_at(self, leftarg, rightarg, eval_point):
        """Identity holds when arguments have same verifiers."""
        N = self.semantics.N
        sem = self.semantics
        x = z3.BitVec("t_id_x", N)
        return z3.And(
            ForAll([x],
                z3.Implies(
                    sem.extended_verify(x, leftarg, eval_point),
                    sem.extended_verify(x, rightarg, eval_point)
                )
            ),
            ForAll([x],
                z3.Implies(
                    sem.extended_verify(x, rightarg, eval_point),
                    sem.extended_verify(x, leftarg, eval_point)
                )
            )
        )
        
    def compute_verifiers(self, arg1, arg2, model, eval_point):
        """Standard identity semantics - verifiers when both sides have same verifiers."""
        ver1 = self.semantics.extended_compute_verifiers(arg1, model, eval_point)
        ver2 = self.semantics.extended_compute_verifiers(arg2, model, eval_point)
        
        # Identity holds at all states when verifier sets are equal
        if set(ver1) == set(ver2):
            return list(range(2**self.semantics.N))
        else:
            return []
        
    def extended_verify(self, state, arg1, arg2, eval_point):
        """Standard identity constraint."""
        x = z3.BitVec('x_id', self.semantics.N)
        return z3.And(
            z3.ForAll([x],
                z3.Implies(
                    self.semantics.extended_verify(x, arg1, eval_point),
                    self.semantics.extended_verify(x, arg2, eval_point)
                )
            ),
            z3.ForAll([x],
                z3.Implies(
                    self.semantics.extended_verify(x, arg2, eval_point),
                    self.semantics.extended_verify(x, arg1, eval_point)
                )
            )
        )
        
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print identity."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


def create_operators():
    """Create operator collection for witness uninegation semantics."""
    return OperatorCollection(
        UniNegationOperator,
        UniConjunctionOperator,
        UniDisjunctionOperator,
        UniIdentityOperator,
    )

# Export the operator collection
witness_operators = create_operators()
