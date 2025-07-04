"""
Incremental exclusion operators with witness tracking support.

Each operator extends the standard interface with methods for incremental
verification, maintaining the recursive semantic design pattern while adding
witness tracking capabilities.
"""

import z3
import itertools
from model_checker.utils import ForAll, Exists
from model_checker import syntactic


class UniAndOperator(syntactic.Operator):
    """Unilateral conjunction operator with incremental witness support."""

    name = "\\uniwedge"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Conjunction is true when both arguments are true."""
        sem = self.semantics
        return z3.And(
            sem.true_at(leftarg, eval_point),
            sem.true_at(rightarg, eval_point)
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """State verifies conjunction when it's the fusion of verifiers for each conjunct."""
        x = z3.BitVec("ex_ver_x", self.semantics.N)
        y = z3.BitVec("ex_ver_y", self.semantics.N)
        return Exists(
            [x, y],
            z3.And(
                self.semantics.fusion(x, y) == state,
                self.semantics.extended_verify(x, leftarg, eval_point),
                self.semantics.extended_verify(y, rightarg, eval_point),
            ),
        )

    def find_verifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Find verifiers by taking product of component verifiers."""
        Y_V = left_sent_obj.proposition.find_proposition()
        Z_V = right_sent_obj.proposition.find_proposition()
        return self.semantics.product(Y_V, Z_V)

    def compute_verifiers(self, left_arg, right_arg, witness_store, truth_cache):
        """Compute verifiers incrementally by taking product of component verifiers."""
        left_verifiers = truth_cache.get_verifiers(left_arg, witness_store)
        right_verifiers = truth_cache.get_verifiers(right_arg, witness_store)
        return self.semantics.product(left_verifiers, right_verifiers)
    
    def evaluate_with_witnesses(self, left_arg, right_arg, eval_point, witness_store, truth_cache):
        """Evaluate conjunction truth incrementally using witnesses."""
        verifiers = self.compute_verifiers(left_arg, right_arg, witness_store, truth_cache)
        eval_world = eval_point['world']
        return any(self.semantics.is_part_of(v, eval_world) for v in verifiers)
    
    def has_sufficient_witnesses(self, left_arg, right_arg, witness_store):
        """Check if arguments have sufficient witnesses for incremental evaluation."""
        # Recursively check both arguments
        left_sufficient = (left_arg.sentence_letter is not None or 
                          left_arg.operator.has_sufficient_witnesses(
                              *left_arg.arguments, witness_store))
        right_sufficient = (right_arg.sentence_letter is not None or
                           right_arg.operator.has_sufficient_witnesses(
                               *right_arg.arguments, witness_store))
        return left_sufficient and right_sufficient

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print conjunction."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class UniOrOperator(syntactic.Operator):
    """Unilateral disjunction operator with incremental witness support."""

    name = "\\univee"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Disjunction is true when at least one argument is true."""
        sem = self.semantics
        return z3.Or(
            sem.true_at(leftarg, eval_point),
            sem.true_at(rightarg, eval_point)
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """State verifies disjunction when it verifies either disjunct."""
        return z3.Or(
            self.semantics.extended_verify(state, leftarg, eval_point),
            self.semantics.extended_verify(state, rightarg, eval_point),
        )

    def find_verifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Find verifiers by taking union of component verifiers."""
        Y_V = left_sent_obj.proposition.find_proposition()
        Z_V = right_sent_obj.proposition.find_proposition()
        return Y_V.union(Z_V)

    def compute_verifiers(self, left_arg, right_arg, witness_store, truth_cache):
        """Compute verifiers incrementally by taking union of component verifiers."""
        left_verifiers = truth_cache.get_verifiers(left_arg, witness_store)
        right_verifiers = truth_cache.get_verifiers(right_arg, witness_store)
        return left_verifiers.union(right_verifiers)
    
    def evaluate_with_witnesses(self, left_arg, right_arg, eval_point, witness_store, truth_cache):
        """Evaluate disjunction truth incrementally using witnesses."""
        verifiers = self.compute_verifiers(left_arg, right_arg, witness_store, truth_cache)
        eval_world = eval_point['world']
        return any(self.semantics.is_part_of(v, eval_world) for v in verifiers)
    
    def has_sufficient_witnesses(self, left_arg, right_arg, witness_store):
        """Check if arguments have sufficient witnesses for incremental evaluation."""
        # For disjunction, we need witnesses for at least one disjunct
        left_sufficient = (left_arg.sentence_letter is not None or 
                          left_arg.operator.has_sufficient_witnesses(
                              *left_arg.arguments, witness_store))
        right_sufficient = (right_arg.sentence_letter is not None or
                           right_arg.operator.has_sufficient_witnesses(
                               *right_arg.arguments, witness_store))
        return left_sufficient or right_sufficient

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print disjunction."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class UniIdentityOperator(syntactic.Operator):
    """Unilateral identity/biconditional operator with incremental witness support."""

    name = "\\uniequiv"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Identity is true when both arguments have same truth value."""
        sem = self.semantics
        left_true = sem.true_at(leftarg, eval_point)
        right_true = sem.true_at(rightarg, eval_point)
        return z3.Or(
            z3.And(left_true, right_true),
            z3.And(z3.Not(left_true), z3.Not(right_true))
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """State verifies identity in complex way."""
        # This is a simplified version - full implementation would be more complex
        return z3.Or(
            z3.And(
                self.semantics.extended_verify(state, leftarg, eval_point),
                self.semantics.extended_verify(state, rightarg, eval_point)
            ),
            z3.And(
                z3.Not(self.semantics.extended_verify(state, leftarg, eval_point)),
                z3.Not(self.semantics.extended_verify(state, rightarg, eval_point))
            )
        )

    def find_verifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Find verifiers for identity."""
        # Placeholder implementation
        return set()

    def compute_verifiers(self, left_arg, right_arg, witness_store, truth_cache):
        """Compute verifiers for identity incrementally."""
        # This would need a more complex implementation
        return set()
    
    def evaluate_with_witnesses(self, left_arg, right_arg, eval_point, witness_store, truth_cache):
        """Evaluate identity truth incrementally using witnesses."""
        # Simplified for Phase 1
        return False
    
    def has_sufficient_witnesses(self, left_arg, right_arg, witness_store):
        """Check if arguments have sufficient witnesses for incremental evaluation."""
        return True  # Simplified for Phase 1

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print identity."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class ExclusionOperator(syntactic.Operator):
    """Exclusion operator with incremental witness tracking support."""

    name = "\\exclude"
    arity = 1

    def true_at(self, argument, eval_point):
        """
        Implements the three-condition exclusion semantics using Skolem functions.
        For Phase 1, this uses the standard approach.
        Phase 2 will integrate incremental witness tracking.
        """
        sem = self.semantics
        
        # Generate unique Skolem function names
        h_sk_name = f"h_sk_{sem.counter}"
        y_sk_name = f"y_sk_{sem.counter}"
        sem.counter += 1
        
        # Create Skolem functions
        h_sk = z3.Function(h_sk_name, z3.BitVecSort(sem.N), z3.BitVecSort(sem.N))
        y_sk = z3.Function(y_sk_name, z3.BitVecSort(sem.N), z3.BitVecSort(sem.N))
        
        # Variables for quantification
        x = z3.BitVec(f"x_ex_{sem.counter}", sem.N)
        s = z3.BitVec(f"s_ex_{sem.counter}", sem.N)
        sem.counter += 1
        
        # Build the three conditions
        
        # Condition 1: For all x in Ver(φ), y_sk(x) is part of x and h_sk(x) excludes y_sk(x)
        condition1 = ForAll([x], 
            z3.Implies(
                sem.extended_verify(x, argument, eval_point),
                z3.And(
                    sem.is_part_of(y_sk(x), x),
                    sem.exclusion(h_sk(x), y_sk(x))
                )
            )
        )
        
        # Condition 2: For all x in Ver(φ), h_sk(x) is part of eval_point["world"]
        condition2 = ForAll([x],
            z3.Implies(
                sem.extended_verify(x, argument, eval_point),
                sem.is_part_of(h_sk(x), eval_point["world"])
            )
        )
        
        # Condition 3: eval_point["world"] is minimal (fusion of all h_sk(x))
        # First, collect all h_sk(x) values for x in Ver(φ)
        h_values = z3.BitVec(f"h_values_{sem.counter}", sem.N)
        sem.counter += 1
        
        # The fusion of all h_sk(x) equals eval_point["world"]
        condition3_setup = ForAll([h_values],
            z3.Implies(
                Exists([x], z3.And(
                    sem.extended_verify(x, argument, eval_point),
                    h_values == h_sk(x)
                )),
                sem.is_part_of(h_values, eval_point["world"])
            )
        )
        
        # And eval_point["world"] is the fusion of these values
        condition3_minimal = ForAll([s],
            z3.Implies(
                z3.And(
                    ForAll([x], z3.Implies(
                        sem.extended_verify(x, argument, eval_point),
                        sem.is_part_of(h_sk(x), s)
                    )),
                    s != eval_point["world"]
                ),
                z3.Not(sem.is_part_of(s, eval_point["world"]))
            )
        )
        
        condition3 = z3.And(condition3_setup, condition3_minimal)
        
        # Combine all conditions
        return z3.And(condition1, condition2, condition3)

    def extended_verify(self, state, argument, eval_point):
        """
        State verifies exclusion when it satisfies the three conditions.
        """
        # For Phase 1, we use a simplified version
        # Phase 2 will add witness registration
        return self.true_at(argument, {"world": state})

    def find_verifiers(self, sent_obj, eval_point):
        """Find verifiers for exclusion using three conditions."""
        # Placeholder for Phase 1
        return set()

    def compute_verifiers(self, argument, witness_store, truth_cache):
        """Compute verifiers incrementally using witness mappings."""
        # Get witness mappings for this exclusion instance
        h_mapping = witness_store.get_witness_mapping(f"h_sk_{id(self)}")
        y_mapping = witness_store.get_witness_mapping(f"y_sk_{id(self)}")
        
        # Get verifiers of the argument
        arg_verifiers = truth_cache.get_verifiers(argument, witness_store)
        
        # Find states satisfying three conditions
        verifiers = set()
        all_states = list(self.semantics.get_all_bitvectors())
        
        for state in all_states:
            if self.satisfies_three_conditions(state, arg_verifiers, h_mapping, y_mapping):
                verifiers.add(state)
        
        return verifiers
    
    def satisfies_three_conditions(self, state, arg_verifiers, h_mapping, y_mapping):
        """Check three-condition exclusion semantics incrementally with actual witness mappings."""
        # For Phase 1, return False as placeholder
        # Phase 2 will implement full checking
        return False
    
    def register_witnesses(self, argument, witness_store):
        """Register witness functions for this exclusion instance."""
        h_func_name = f"h_sk_{id(self)}"
        y_func_name = f"y_sk_{id(self)}"
        
        witness_store.register_skolem_function(
            h_func_name, 
            z3.BitVecSort(self.semantics.N), 
            z3.BitVecSort(self.semantics.N)
        )
        witness_store.register_skolem_function(
            y_func_name,
            z3.BitVecSort(self.semantics.N),
            z3.BitVecSort(self.semantics.N)
        )
        
        return h_func_name, y_func_name

    def evaluate_with_witnesses(self, argument, eval_point, witness_store, truth_cache):
        """Evaluate exclusion truth incrementally using witnesses."""
        verifiers = self.compute_verifiers(argument, witness_store, truth_cache)
        eval_world = eval_point['world']
        return any(self.semantics.is_part_of(v, eval_world) for v in verifiers)
    
    def has_sufficient_witnesses(self, argument, witness_store):
        """Check if we have complete witness mappings for incremental evaluation."""
        h_name = f"h_sk_{id(self)}"
        y_name = f"y_sk_{id(self)}"
        return (witness_store.is_witness_complete(h_name) and 
                witness_store.is_witness_complete(y_name))

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print exclusion."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


# Create the operator collection
def create_exclusion_operators():
    """Create operator collection for incremental exclusion semantics."""
    return syntactic.OperatorCollection(
        ExclusionOperator,
        UniAndOperator,
        UniOrOperator,
        UniIdentityOperator,
    )

# Export the operator collection
exclusion_operators = create_exclusion_operators()