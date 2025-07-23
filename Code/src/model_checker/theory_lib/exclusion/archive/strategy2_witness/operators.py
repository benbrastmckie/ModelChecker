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
        using witness predicates for the existential quantification.
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


class FineUniNegation(Operator):
    """
    Fine preclusion operator - implements Fine's set-based preclusion semantics.
    No witness functions needed since all quantifiers are over finite state space.
    """
    
    name = "\\set_unineg"
    arity = 1
    
    def true_at(self, arg, eval_point):
        """Fine preclusion is true when there's a verifier in the evaluation world."""
        x = z3.BitVec(f"fine_ver_{self.semantics.counter}", self.semantics.N)
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
        Compute verifiers using Fine preclusion semantics.
        No witness predicates needed - directly check set conditions.
        """
        # Get verifiers of the argument (set S)
        S_verifiers = self.semantics.extended_compute_verifiers(
            argument, model, eval_point
        )
        
        if not S_verifiers:
            # If S is empty, any state vacuously Fine-precludes it
            return list(range(2**self.semantics.N))
        
        verifiers = []
        # Check each potential verifier e
        for e in range(2**self.semantics.N):
            if self._verifies_fine_preclusion(e, S_verifiers, model):
                verifiers.append(e)
                
        return verifiers
    
    def _verifies_fine_preclusion(self, e: int, S_verifiers: List[int], 
                                  model) -> bool:
        """
        Check if state e Fine-precludes the set S_verifiers.
        e Fine-precludes S if e = ⊔T where:
        1. Coverage: ∀s∈S ∃t∈T: t excludes some part of s
        2. Relevance: ∀t∈T ∃s∈S: t excludes some part of s
        """
        # Try all possible subsets T of states
        num_states = 2**self.semantics.N
        
        # For each possible subset T (represented as a bitmask)
        for T_mask in range(2**num_states):
            T_states = [i for i in range(num_states) if (T_mask >> i) & 1]
            
            if not T_states:
                continue  # Empty T cannot work
                
            # Check if e is the fusion of T
            if not self._check_fusion_equals(e, T_states, model):
                continue
                
            # Check coverage condition
            if not self._check_coverage(S_verifiers, T_states, model):
                continue
                
            # Check relevance condition  
            if not self._check_relevance(T_states, S_verifiers, model):
                continue
                
            # Found a valid T
            return True
            
        return False
    
    def _check_fusion_equals(self, e: int, T_states: List[int], model) -> bool:
        """Check if e equals the fusion of states in T."""
        if not T_states:
            return False
            
        # Compute fusion of all states in T
        fusion_result = T_states[0]
        for t in T_states[1:]:
            fusion_val = self._eval_fusion(fusion_result, t, model)
            if fusion_val is None:
                return False
            fusion_result = fusion_val
            
        return fusion_result == e
    
    def _check_coverage(self, S_verifiers: List[int], T_states: List[int], 
                       model) -> bool:
        """Check coverage: ∀s∈S ∃t∈T: t excludes some part of s."""
        for s in S_verifiers:
            found_excluding_t = False
            for t in T_states:
                # Check if t excludes some part of s
                if self._excludes_some_part(t, s, model):
                    found_excluding_t = True
                    break
            if not found_excluding_t:
                return False
        return True
    
    def _check_relevance(self, T_states: List[int], S_verifiers: List[int], 
                        model) -> bool:
        """Check relevance: ∀t∈T ∃s∈S: t excludes some part of s."""
        for t in T_states:
            found_excluded_s = False
            for s in S_verifiers:
                # Check if t excludes some part of s
                if self._excludes_some_part(t, s, model):
                    found_excluded_s = True
                    break
            if not found_excluded_s:
                return False
        return True
    
    def _excludes_some_part(self, t: int, s: int, model) -> bool:
        """Check if t excludes some part of s."""
        # Check all parts of s
        for part in range(2**self.semantics.N):
            if self._eval_is_part_of(part, s, model):
                if self._eval_excludes(t, part, model):
                    return True
        return False
    
    def _eval_is_part_of(self, x: int, y: int, model) -> bool:
        """Evaluate is_part_of relation using the model."""
        x_bv = z3.BitVecVal(x, self.semantics.N)
        y_bv = z3.BitVecVal(y, self.semantics.N)
        result = model.eval(self.semantics.is_part_of(x_bv, y_bv))
        return z3.is_true(result)
    
    def _eval_excludes(self, x: int, y: int, model) -> bool:
        """Evaluate excludes relation using the model."""
        x_bv = z3.BitVecVal(x, self.semantics.N)
        y_bv = z3.BitVecVal(y, self.semantics.N)
        result = model.eval(self.semantics.excludes(x_bv, y_bv))
        return z3.is_true(result)
    
    def _eval_fusion(self, x: int, y: int, model) -> Optional[int]:
        """Evaluate fusion operation using the model."""
        x_bv = z3.BitVecVal(x, self.semantics.N)
        y_bv = z3.BitVecVal(y, self.semantics.N)
        result = model.eval(self.semantics.fusion(x_bv, y_bv))
        if z3.is_bv_value(result):
            return result.as_long()
        return None
    
    def extended_verify(self, state, argument, eval_point):
        """
        Fine preclusion verification conditions as Z3 constraints.
        
        State verifies \\finexclude(A) if state Fine-precludes the set of A-verifiers.
        """
        sem = self.semantics
        N = sem.N
        
        # We'll use a different encoding: represent T as constraints on states
        # For efficiency, we'll directly encode the Fine preclusion conditions
        
        # Variables for the computation
        counter = self.semantics.counter
        self.semantics.counter += 1
        
        # Helper: check if a given subset T works
        def check_T_subset(T_states_constraint):
            # Variables
            s = z3.BitVec(f"s_fine_{counter}", N)
            t = z3.BitVec(f"t_fine_{counter}", N)
            y = z3.BitVec(f"y_fine_{counter}", N)
            
            # Coverage: ∀s∈S ∃t∈T: t excludes some part of s
            coverage = ForAll([s],
                z3.Implies(
                    sem.extended_verify(s, argument, eval_point),
                    Exists([t, y],
                        z3.And(
                            T_states_constraint(t),
                            sem.is_part_of(y, s),
                            sem.excludes(t, y)
                        )
                    )
                )
            )
            
            # Relevance: ∀t∈T ∃s∈S: t excludes some part of s
            relevance = ForAll([t],
                z3.Implies(
                    T_states_constraint(t),
                    Exists([s, y],
                        z3.And(
                            sem.extended_verify(s, argument, eval_point),
                            sem.is_part_of(y, s),
                            sem.excludes(t, y)
                        )
                    )
                )
            )
            
            return z3.And(coverage, relevance)
        
        # Try different approaches to find a valid T
        # Approach 1: T consists of all states that exclude some part of some S-verifier
        s1 = z3.BitVec(f"s1_{counter}", N) 
        y1 = z3.BitVec(f"y1_{counter}", N)
        
        T_constraint = lambda t: Exists([s1, y1],
            z3.And(
                sem.extended_verify(s1, argument, eval_point),
                sem.is_part_of(y1, s1),
                sem.excludes(t, y1)
            )
        )
        
        # Check if state is fusion of such T
        # For simplicity, we'll check specific cases
        
        # Case 1: state itself forms T (singleton)
        case1 = z3.And(
            check_T_subset(lambda t: t == state),
            # state must exclude part of some S-verifier
            Exists([s1, y1],
                z3.And(
                    sem.extended_verify(s1, argument, eval_point),
                    sem.is_part_of(y1, s1),
                    sem.excludes(state, y1)
                )
            )
        )
        
        # Case 2: state is fusion of multiple excluding states
        # This is more complex - for now we'll use a simplified version
        x1 = z3.BitVec(f"x1_{counter}", N)
        x2 = z3.BitVec(f"x2_{counter}", N)
        
        case2 = Exists([x1, x2],
            z3.And(
                sem.fusion(x1, x2) == state,
                x1 != x2,  # Non-trivial decomposition
                # Both parts must be in our T
                T_constraint(x1),
                T_constraint(x2),
                # Check coverage and relevance for {x1, x2}
                check_T_subset(lambda t: z3.Or(t == x1, t == x2))
            )
        )
        
        # Return disjunction of cases
        return z3.Or(case1, case2)
    
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print Fine preclusion."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


def create_operators():
    """Create operator collection for witness uninegation semantics."""
    return OperatorCollection(
        UniNegationOperator,
        FineUniNegation,
        UniConjunctionOperator,
        UniDisjunctionOperator,
        UniIdentityOperator,
    )

# Export the operator collection
witness_operators = create_operators()
