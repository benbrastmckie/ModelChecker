##########################
### DEFINE THE IMPORTS ###
##########################

import z3
from model_checker.utils import ForAll, Exists
from model_checker import syntactic


class ExclusionOperator(syntactic.Operator):
    """Exclusion operator with correct recursive semantics."""
    
    name = "\\exclude"
    arity = 1
    
    def __init__(self, semantics):
        super().__init__(semantics)
        self._counter = 0
    
    def get_unique_id(self):
        """Get unique ID for variable naming."""
        self._counter += 1
        return self._counter
    
    def true_at(self, argument, eval_point):
        """
        Exclusion is true at a point iff there exists a verifier for ¬A that is part of the world.
        
        This correctly reduces to: exists s. extended_verify(s, A) AND s part_of world
        """
        s = z3.BitVec(f"excl_ver_{self.get_unique_id()}", self.semantics.N)
        return Exists([s], z3.And(
            self.semantics.is_part_of(s, eval_point["world"]),
            self.extended_verify(s, argument, eval_point)
        ))
    
    def extended_verify(self, state, argument, eval_point):
        """
        Extended verification for exclusion using Skolem functions.
        
        A state verifies ¬A iff it satisfies the three conditions:
        1. For every verifier x of A, there's a part y_sk(x) of x where h_sk(x) excludes y_sk(x)
        2. For every verifier x of A, h_sk(x) is part of state
        3. State is minimal with respect to condition 2
        """
        sem = self.semantics
        N = sem.N
        sk_id = self.get_unique_id()
        
        # Skolem functions with unique names
        h_sk = z3.Function(f"h_sk_{sk_id}", z3.BitVecSort(N), z3.BitVecSort(N))
        y_sk = z3.Function(f"y_sk_{sk_id}", z3.BitVecSort(N), z3.BitVecSort(N))
        
        # Variables
        x = z3.BitVec(f"x_{sk_id}", N)
        z = z3.BitVec(f"z_{sk_id}", N)
        
        return z3.And(
            # Condition 1: For every verifier x of argument, y_sk(x) is part of x and h_sk(x) excludes y_sk(x)
            ForAll([x], z3.Implies(
                sem.extended_verify(x, argument, eval_point),
                z3.And(
                    sem.is_part_of(y_sk(x), x),
                    sem.excludes(h_sk(x), y_sk(x))
                )
            )),
            
            # Condition 2: For every verifier x of argument, h_sk(x) is part of state
            ForAll([x], z3.Implies(
                sem.extended_verify(x, argument, eval_point),
                sem.is_part_of(h_sk(x), state)
            )),
            
            # Condition 3: State is minimal
            ForAll([z], z3.Implies(
                ForAll([x], z3.Implies(
                    sem.extended_verify(x, argument, eval_point),
                    sem.is_part_of(h_sk(x), z)
                )),
                sem.is_part_of(state, z)
            ))
        )
    
    def find_verifiers(self, argument, eval_point):
        """Find the set of verifiers for the exclusion formula."""
        all_states = self.semantics.all_states
        z3_model = argument.proposition.model_structure.z3_model
        
        # Find verifiers by evaluating the formula for each state
        result = set()
        for state in all_states:
            # Check if this state verifies the exclusion formula
            formula = self.extended_verify(state, argument, eval_point)
            if z3.is_true(z3_model.evaluate(formula)):
                result.add(state)
                
        return result
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print method for exclusion operator."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class UniAndOperator(syntactic.Operator):
    """Unilateral conjunction operator."""
    
    name = "\\uniwedge"
    arity = 2
    
    def __init__(self, semantics):
        super().__init__(semantics)
        self._counter = 0
    
    def get_unique_id(self):
        """Get unique ID for variable naming."""
        self._counter += 1
        return self._counter
    
    def true_at(self, leftarg, rightarg, eval_point):
        """
        Conjunction is true at a point iff both arguments are true at that point.
        
        This correctly recurses on both arguments.
        """
        sem = self.semantics
        return z3.And(
            sem.true_at(leftarg, eval_point),
            sem.true_at(rightarg, eval_point)
        )
    
    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """
        A state verifies A ∧ B iff it can be decomposed as x ⊔ y where
        x verifies A and y verifies B.
        """
        x = z3.BitVec(f"conj_x_{self.get_unique_id()}", self.semantics.N)
        y = z3.BitVec(f"conj_y_{self.get_unique_id()}", self.semantics.N)
        return Exists([x, y], z3.And(
            (x | y) == state,  # fusion is bitwise OR
            self.semantics.extended_verify(x, leftarg, eval_point),
            self.semantics.extended_verify(y, rightarg, eval_point)
        ))
    
    def find_verifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Find verifiers for conjunction."""
        # For conjunction, verifiers are the product (pairwise fusion) of component verifiers
        Y_V = left_sent_obj.proposition.find_proposition()
        Z_V = right_sent_obj.proposition.find_proposition()
        return self.semantics.product(Y_V, Z_V)
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print method for conjunction."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class UniOrOperator(syntactic.Operator):
    """Unilateral disjunction operator."""
    
    name = "\\univee"
    arity = 2
    
    def __init__(self, semantics):
        super().__init__(semantics)
        self._counter = 0
    
    def get_unique_id(self):
        """Get unique ID for variable naming."""
        self._counter += 1
        return self._counter
    
    def true_at(self, leftarg, rightarg, eval_point):
        """
        Disjunction is true at a point iff at least one argument is true at that point.
        
        This correctly recurses on both arguments.
        """
        sem = self.semantics
        return z3.Or(
            sem.true_at(leftarg, eval_point),
            sem.true_at(rightarg, eval_point)
        )
    
    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """
        A state verifies A ∨ B iff it verifies A or it verifies B.
        """
        return z3.Or(
            self.semantics.extended_verify(state, leftarg, eval_point),
            self.semantics.extended_verify(state, rightarg, eval_point)
        )
    
    def find_verifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Find verifiers for disjunction."""
        # For disjunction, verifiers are the union of component verifiers
        Y_V = left_sent_obj.proposition.find_proposition()
        Z_V = right_sent_obj.proposition.find_proposition()
        return Y_V.union(Z_V)
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print method for disjunction."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class UniIdentityOperator(syntactic.Operator):
    """Unilateral identity/equivalence operator."""
    
    name = "\\uniequiv"
    arity = 2
    
    def true_at(self, leftarg, rightarg, eval_point):
        """
        Identity is true at a point iff the arguments have the same verifiers.
        
        This is encoded as: for all x, x verifies A iff x verifies B.
        """
        sem = self.semantics
        N = sem.N
        x = z3.BitVec("identity_x", N)
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
        """
        Only the null state verifies an identity statement A ≡ B,
        and only when A and B have the same verifiers.
        """
        return z3.And(
            state == self.semantics.null_state,
            self.true_at(leftarg, rightarg, eval_point)
        )
    
    def find_verifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Find verifiers for identity."""
        # For identity, only null verifies when arguments have same verifiers
        Y_V = left_sent_obj.proposition.find_proposition()
        Z_V = right_sent_obj.proposition.find_proposition()
        return {self.semantics.null_state} if Y_V == Z_V else set()
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print method for identity."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)

# Create the operator collection
exclusion_operators = syntactic.OperatorCollection(
    UniAndOperator,
    UniOrOperator, 
    ExclusionOperator,
    UniIdentityOperator,
)
