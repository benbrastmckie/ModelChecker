"""
Witness Array Exclusion Operators

This module implements exclusion operators using Z3 arrays instead of Skolem functions
to make witness mappings accessible during Phase 2 truth evaluation.

Key Innovation:
- ExclusionOperator uses create_witness_arrays() to store h and y mappings
- Arrays become part of the model and can be queried after solving  
- find_verifiers() can extract array values to reconstruct witnesses
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
            self.semantics.extended_verify(state, rightarg, eval_point),
        )

    def find_verifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Find verifiers by taking union of component verifiers."""
        Y_V = left_sent_obj.proposition.find_proposition()
        Z_V = right_sent_obj.proposition.find_proposition()
        return Y_V.union(Z_V)

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print disjunction."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class WitnessArrayExclusionOperator(syntactic.Operator):
    """
    Witness Array exclusion operator.
    
    This implementation uses Z3 arrays to store the exclusion function h(x) and 
    witness function y(x), making them accessible during Phase 2 truth evaluation.
    
    Key features:
    - Creates h_array and y_array during constraint generation
    - Stores array references for later retrieval
    - find_verifiers() can extract actual array values from the model
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
        Implement three-condition exclusion semantics with witness arrays.
        
        Creates Z3 arrays h_array and y_array to store witness mappings.
        These arrays become part of the model and can be queried during Phase 2.
        """
        # Abbreviations
        sem = self.semantics
        N = sem.N
        extended_verify = sem.extended_verify
        excludes = sem.excludes
        is_part_of = sem.is_part_of
        
        # Create unique arrays for this exclusion instance
        sem.array_counter += 1
        array_id = sem.array_counter
        
        # Create witness arrays
        h_array, y_array = sem.create_witness_arrays(array_id)
        
        # Store array information for Phase 2 retrieval
        sem.store_witness_arrays(array_id, h_array, y_array, argument, state)
        
        # Variables for quantifiers
        x = z3.BitVec(f"wa_x_{array_id}", N)
        z = z3.BitVec(f"wa_z_{array_id}", N)

        return z3.And(
            # Condition 1: For every verifier x of argument, 
            # y_array[x] is part of x and h_array[x] excludes y_array[x]
            ForAll([x], z3.Implies(
                extended_verify(x, argument, eval_point), 
                z3.And(
                    is_part_of(y_array[x], x), 
                    excludes(h_array[x], y_array[x])
                )
            )),
            
            # Condition 2 (Upper Bound): For every verifier x of argument, 
            # h_array[x] is part of state
            ForAll([x], z3.Implies(
                extended_verify(x, argument, eval_point), 
                is_part_of(h_array[x], state)
            )),
            
            # Condition 3 (Least Upper Bound): state is the smallest state 
            # satisfying the UB condition
            ForAll([z], z3.Implies(
                ForAll([x], z3.Implies(
                    extended_verify(x, argument, eval_point), 
                    is_part_of(h_array[x], z)
                )), 
                is_part_of(state, z)
            ))
        )

    def find_verifiers(self, argument, eval_point):
        """
        Find verifiers for the exclusion operator using witness arrays.
        
        This is where the witness array approach attempts to solve the problem:
        - Extract array values from the model
        - Use actual h and y mappings to verify exclusion conditions
        - Return correct verifier set based on reconstructed witnesses
        
        Note: This still faces the challenge of correlating exclusion instances
        between constraint generation and verification phases.
        """
        # Get the model structure - this is where the model is stored
        model_structure = argument.proposition.model_structure
        
        # For now, we still need to delegate to find_verifying_states
        # because we need access to the Z3 model to extract array values.
        # The fundamental issue remains: we need to know which array_id
        # corresponds to this specific exclusion evaluation.
        
        # TODO: Implement array value extraction once we have model access
        # This would involve:
        # 1. Identify which array_id corresponds to this exclusion
        # 2. Extract h_array and y_array values from the model  
        # 3. Compute verifiers using extracted mappings
        # 4. Verify three conditions using actual array values
        
        exclusion_sentence = syntactic.Sentence(self, argument)
        return model_structure.find_verifying_states(exclusion_sentence, eval_point)

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print exclusion with array information if available."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)
        
        # TODO: Add printing of witness array information
        # if hasattr(self.semantics, 'witness_arrays'):
        #     print(f"{'  ' * indent_num}  Witness arrays: {len(self.semantics.witness_arrays)}")


# Create the operator collection
class WitnessArrayOperatorCollection(syntactic.OperatorCollection):
    """Collection of operators for witness array exclusion theory."""
    
    def __init__(self, semantics):
        super().__init__()  # Don't pass semantics to parent
        self.operators = {
            "\\uniwedge": UniAndOperator(semantics),
            "\\univee": UniOrOperator(semantics),
            "\\exclude": WitnessArrayExclusionOperator(semantics),
        }


# Convenience function for creating the collection
def create_operators(semantics):
    """Create and return the witness array operator collection."""
    return WitnessArrayOperatorCollection(semantics)

# Export a collection that can be used without semantics (for validation)
witness_array_operators = syntactic.OperatorCollection(
    UniAndOperator,
    UniOrOperator,
    WitnessArrayExclusionOperator,
)