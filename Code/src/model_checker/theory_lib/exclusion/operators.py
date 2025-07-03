"""
Simplified exclusion operators module with single Skolemized (SK) strategy.
This replaces the multi-strategy approach with a focused implementation.
"""

import z3
import itertools
from model_checker.utils import ForAll, Exists
from model_checker import syntactic


class UniAndOperator(syntactic.Operator):
    """Unilateral conjunction operator."""

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

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print conjunction."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class UniOrOperator(syntactic.Operator):
    """Unilateral disjunction operator."""

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
        """State verifies disjunction when it verifies at least one disjunct."""
        return z3.Or(
            self.semantics.extended_verify(state, leftarg, eval_point),
            self.semantics.extended_verify(state, rightarg, eval_point)
        )

    def find_verifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Find verifiers by taking union of component verifiers."""
        Y_V = left_sent_obj.proposition.find_proposition()
        Z_V = right_sent_obj.proposition.find_proposition()
        return Y_V.union(Z_V)

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print disjunction."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class UniIdentityOperator(syntactic.Operator):
    """Unilateral identity operator."""

    name = "\\uniequiv"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Identity holds when arguments have same verifiers."""
        N = self.semantics.N
        sem = self.semantics
        x = z3.BitVec("t_id_x", N)
        return z3.And(
            ForAll(
                x,
                z3.Implies(
                    sem.extended_verify(x, leftarg, eval_point),
                    sem.extended_verify(x, rightarg, eval_point)
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_verify(x, rightarg, eval_point),
                    sem.extended_verify(x, leftarg, eval_point)
                ),
            ),
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """Only null state verifies identity."""
        return z3.And(
            state == self.semantics.null_state,
            self.true_at(leftarg, rightarg, eval_point)
        )

    def find_verifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Find verifiers - null state if arguments are identical."""
        Y_V = left_sent_obj.proposition.find_proposition()
        Z_V = right_sent_obj.proposition.find_proposition()
        return {self.semantics.null_state} if Y_V == Z_V else set()
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print identity."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class ExclusionOperator(syntactic.Operator):
    """
    Skolemized exclusion operator - single strategy implementation.
    
    This implementation uses Skolem functions to eliminate existential quantifiers,
    providing more predictable behavior and better alignment between constraint
    generation and truth evaluation.
    """

    name = "\\exclude"
    arity = 1

    def true_at(self, arg, eval_point):
        """Exclusion is true when there's a verifier in the evaluation world."""
        # Use custom quantifier for predictability
        x = z3.BitVec(f"ver_{self.semantics.counter}", self.semantics.N)
        self.semantics.counter += 1
        
        return Exists(
            [x],
            z3.And(
                self.extended_verify(x, arg, eval_point),
                self.semantics.is_part_of(x, eval_point["world"])
            )
        )

    def extended_verify(self, state, argument, eval_point):
        """
        Implement three-condition exclusion semantics with Skolem functions.
        
        Uses custom quantifiers (ForAll/Exists from utils) for predictable behavior.
        Creates unique Skolem functions h_sk and y_sk for each instance.
        """
        # Abbreviations
        sem = self.semantics
        N = sem.N
        extended_verify = sem.extended_verify
        excludes = sem.excludes
        is_part_of = sem.is_part_of
        
        # Create unique Skolem functions for this exclusion instance
        sem.counter += 1
        counter = sem.counter
        
        # Main exclusion function: maps verifiers to their exclusion states
        h_sk = z3.Function(f"h_sk_{counter}", z3.BitVecSort(N), z3.BitVecSort(N))
        
        # Witness function for condition 1: maps verifiers to witness parts
        y_sk = z3.Function(f"y_sk_{counter}", z3.BitVecSort(N), z3.BitVecSort(N))
        
        # Variables
        x = z3.BitVec(f"sk_x_{counter}", N)
        z = z3.BitVec(f"sk_z_{counter}", N)

        return z3.And(
            # Condition 1: For every verifier x of argument, 
            # y_sk(x) is part of x and h_sk(x) excludes y_sk(x)
            ForAll([x], z3.Implies(
                extended_verify(x, argument, eval_point), 
                z3.And(
                    is_part_of(y_sk(x), x), 
                    excludes(h_sk(x), y_sk(x))
                )
            )),
            
            # Condition 2 (Upper Bound): For every verifier x of argument, 
            # h_sk(x) is part of state
            ForAll([x], z3.Implies(
                extended_verify(x, argument, eval_point), 
                is_part_of(h_sk(x), state)
            )),
            
            # Condition 3 (Least Upper Bound): state is the smallest state 
            # satisfying the UB condition
            ForAll([z], z3.Implies(
                ForAll([x], z3.Implies(
                    extended_verify(x, argument, eval_point), 
                    is_part_of(h_sk(x), z)
                )), 
                is_part_of(state, z)
            ))
        )

    def find_verifiers(self, argument, eval_point):
        """
        Find verifiers for the exclusion operator.
        
        Since we cannot reconstruct the Skolem functions used during constraint
        generation, we need to delegate to find_verifying_states. However, this
        creates new Skolem functions, which is the root cause of the mismatch.
        
        For now, we accept this limitation and return the result of find_verifying_states.
        A proper fix would require restructuring how verifiers are computed.
        """
        # This is problematic because it creates new Skolem functions,
        # but it's the best we can do without major restructuring
        model_structure = argument.proposition.model_structure
        exclusion_sentence = syntactic.Sentence(self, argument)
        return model_structure.find_verifying_states(exclusion_sentence, eval_point)

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print exclusion."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


# Create the simplified operator collection
def create_simplified_operators():
    """Create operator collection with single exclusion strategy."""
    return syntactic.OperatorCollection(
        UniAndOperator,
        UniOrOperator, 
        ExclusionOperator,  # Single strategy
        UniIdentityOperator,
    )

# Export the simplified collection
exclusion_operators = create_simplified_operators()