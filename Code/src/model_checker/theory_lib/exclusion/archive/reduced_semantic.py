##########################
### DEFINE THE IMPORTS ###
##########################

import z3
from model_checker.utils import ForAll, Exists
from model_checker import model
from model_checker import syntactic


class ReducedExclusionSemantics(model.SemanticDefaults):
    """
    Reduced semantics for exclusion theory with clean primitive separation.
    
    Only two Z3 primitives are declared:
    - verify(state, atom): whether a state verifies an atomic sentence
    - excludes(state1, state2): whether two states exclude each other
    
    All other relations are derived from these primitives and bitwise operations.
    """
    
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 3,
        'possible': False,
        'contingent': False,
        'non_empty': False,
        'non_null': False,
        'disjoint': False,
        'fusion_closure': False,
        'iterate': 1,
        'iteration_timeout': 1.0,
        'iteration_attempts': 5,
        'max_time': 1,
        'expectation': None,
    }
    
    DEFAULT_GENERAL_SETTINGS = {
        "print_impossible": False,
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,
        "maximize": False,
    }

    def __init__(self, combined_settings):
        # Initialize the superclass to set defaults
        super().__init__(combined_settings)
        
        # Counter for unique IDs (for Skolem functions)
        self._unique_id_counter = 0

        # Define the two Z3 primitives
        self.verify = z3.Function(
            "verify",
            z3.BitVecSort(self.N),     # state
            syntactic.AtomSort,         # atomic sentence
            z3.BoolSort(),             # boolean result
        )
        
        self.excludes = z3.Function(
            "excludes",
            z3.BitVecSort(self.N),     # state 1
            z3.BitVecSort(self.N),     # state 2
            z3.BoolSort(),             # boolean result
        )
        
        # Main evaluation world
        self.main_world = z3.BitVec("w", self.N)
        self.main_point = {"world": self.main_world}

        # Define frame constraints
        x, y = z3.BitVecs("frame_x frame_y", self.N)
        
        # Basic constraints
        actuality = self.is_world(self.main_world)
        
        # Exclusion is symmetric
        exclusion_symmetry = ForAll(
            [x, y],
            z3.Implies(
                self.excludes(x, y),
                self.excludes(y, x)
            )
        )
        
        # Null state excludes nothing
        null_excludes_nothing = ForAll(
            x,
            z3.Not(self.excludes(self.null_state, x))
        )
        
        # Set frame constraints
        self.frame_constraints = [
            actuality,
            exclusion_symmetry,
            null_excludes_nothing,
        ]
        
        # Define premise and conclusion behaviors
        self.premise_behavior = lambda premise: self.true_at(premise, self.main_point)
        self.conclusion_behavior = lambda conclusion: self.false_at(conclusion, self.main_point)

    def get_unique_id(self):
        """Get a unique ID for naming Skolem functions."""
        self._unique_id_counter += 1
        return self._unique_id_counter

    # Derived relations (not Z3 primitives)
    
    def fusion(self, x, y):
        """Fusion is just bitwise OR."""
        return x | y
    
    def is_part_of(self, x, y):
        """x is part of y iff fusion(x, y) = y."""
        return self.fusion(x, y) == y
    
    def is_proper_part_of(self, x, y):
        """x is a proper part of y iff x is part of y and x != y."""
        return z3.And(self.is_part_of(x, y), x != y)
    
    # Derived semantic relations
    
    def conflicts(self, e1, e2):
        """Two states conflict if they have parts that exclude each other."""
        f1, f2 = z3.BitVecs(f"conflict_f1_{self.get_unique_id()} conflict_f2_{self.get_unique_id()}", self.N)
        return Exists(
            [f1, f2],
            z3.And(
                self.is_part_of(f1, e1),
                self.is_part_of(f2, e2),
                self.excludes(f1, f2)
            )
        )
    
    def coheres(self, e1, e2):
        """Two states cohere if they don't conflict."""
        return z3.Not(self.conflicts(e1, e2))
    
    def possible(self, e):
        """A state is possible if it coheres with itself."""
        return self.coheres(e, e)
    
    def compossible(self, e1, e2):
        """Two states are compossible if their fusion is possible."""
        return self.possible(self.fusion(e1, e2))
    
    def is_world(self, s):
        """A state is a world if it's possible and maximal."""
        m = z3.BitVec(f"world_m_{self.get_unique_id()}", self.N)
        return z3.And(
            self.possible(s),
            z3.Not(
                Exists(
                    m,
                    z3.And(
                        self.is_proper_part_of(s, m),
                        self.possible(m)
                    )
                )
            )
        )
    
    # Core semantic evaluation methods
    
    def true_at(self, sentence, eval_point):
        """
        Evaluate whether a sentence is true at an evaluation point.
        
        Base case (atomic): exists v. verify(v, sentence) AND v part_of world
        Recursive case (complex): delegate to operator.true_at
        """
        if sentence.sentence_letter is not None:
            # Atomic case: reduce to verifier existence
            v = z3.BitVec(f"v_atom_{id(sentence)}_{self.get_unique_id()}", self.N)
            return Exists([v], z3.And(
                self.verify(v, sentence.sentence_letter),
                self.is_part_of(v, eval_point["world"])
            ))
        else:
            # Complex case: delegate to operator
            return sentence.operator.true_at(*sentence.arguments, eval_point)
    
    def false_at(self, sentence, eval_point):
        """A sentence is false at a point iff it's not true at that point."""
        return z3.Not(self.true_at(sentence, eval_point))
    
    def extended_verify(self, state, sentence, eval_point):
        """
        Check whether a state verifies a sentence.
        
        Base case (atomic): verify(state, sentence)
        Recursive case (complex): delegate to operator.extended_verify
        """
        if sentence.sentence_letter is not None:
            # Atomic case
            return self.verify(state, sentence.sentence_letter)
        else:
            # Complex case: delegate to operator
            return sentence.operator.extended_verify(state, *sentence.arguments, eval_point)
    
    def z3_set(self, py_set, N):
        """Convert a Python set of states to a Z3 characteristic function."""
        # Create a function that returns True for states in the set
        x = z3.BitVec("set_member", N)
        if not py_set:
            # Empty set
            return z3.Function("empty_set", z3.BitVecSort(N), z3.BoolSort())
        
        # Build OR of all states in the set
        conditions = []
        for state in py_set:
            conditions.append(x == state)
        
        # Return a lambda-like function
        return lambda y: z3.Or(*[y == s for s in py_set]) if py_set else z3.BoolVal(False)
    
    def precludes(self, state, z3_set):
        """
        Determines if a state precludes a set of states.
        
        This implements the three conditions for preclusion using Skolem functions.
        """
        h = z3.Function(
            f"h_precl_{self.get_unique_id()}", 
            z3.BitVecSort(self.N),  # argument type: bitvector
            z3.BitVecSort(self.N)   # return type: bitvector
        )

        x, y, z, u, v = z3.BitVecs("precl_x precl_y precl_z precl_u precl_v", self.N)
        return z3.And(
            ForAll( # 1. for every state x in the set, there is some part y of x where h(x) excludes y
                x,
                z3.Implies(
                    z3_set(x),
                    Exists(
                        y,
                        z3.And(
                            self.is_part_of(y, x),
                            self.excludes(h(x), y)
                        )
                    )
                )
            ),
            ForAll( # 2. h(z) is a part of the state for all z in the set
                z,
                z3.Implies(
                    z3_set(z),
                    self.is_part_of(h(z), state),
                )
            ),
            ForAll( # 3. the state is the smallest state to satisfy condition 2
                u,
                z3.Implies(
                    ForAll(
                        v,
                        z3.Implies(
                            z3_set(v),
                            self.is_part_of(h(v), u)
                        )
                    ),
                    self.is_part_of(state, u)
                )
            )
        )
    
    def product(self, set_A, set_B):
        """Compute the set of all pairwise fusions between elements of two sets."""
        result = set()
        for a in set_A:
            for b in set_B:
                result.add(self.fusion(a, b))
        return result


class UnilateralProposition(model.PropositionDefaults):
    """Unilateral proposition for exclusion semantics."""
    
    def __init__(self, sentence_obj, model_structure, eval_world='main'):
        """Initialize unilateral proposition."""
        super().__init__(sentence_obj, model_structure)
        self.eval_world = eval_world
        
        # Find verifiers if model exists
        if self.model_structure.z3_model:
            self.verifiers = self.find_proposition()
            self.precluders = self.find_precluders(self.verifiers)
        else:
            self.verifiers = set()
            self.precluders = set()
    
    @classmethod
    def proposition_constraints(cls, model_constraints, sentence_letter):
        """Generate constraints for atomic propositions.
        
        For unilateral semantics, we don't need additional constraints
        beyond what's in the semantic model. The verify relation is
        already constrained by the frame constraints.
        """
        return []  # No additional constraints needed
    
    def find_proposition(self):
        """Find the set of verifiers for this proposition."""
        # This is Z3 model evaluation, not constraint generation
        if not self.model_structure.z3_model:
            return set()
            
        all_states = self.model_structure.all_states
        model = self.model_structure.z3_model
        semantics = self.semantics
        operator = self.operator
        arguments = self.arguments or ()
        sentence_letter = self.sentence_letter
        
        if sentence_letter is not None:
            # For atomic sentences, find states that verify it
            V = {
                bit for bit in all_states
                if model.evaluate(semantics.verify(bit, sentence_letter))
            }
            return V
        
        if operator is not None:
            # For complex sentences, delegate to operator
            return operator.find_verifiers(*arguments, self.eval_world)
            
        raise ValueError(f"No proposition for {self.name}.")
    
    def truth_value_at(self, eval_point):
        """Check if there is a verifier in the world at eval_point."""
        semantics = self.model_structure.semantics
        z3_model = self.model_structure.z3_model
        
        # Extract world from eval_point
        if isinstance(eval_point, dict):
            eval_world = eval_point.get("world")
        else:
            eval_world = eval_point
            
        # Check if any verifier is part of the evaluation world
        for ver_bit in self.verifiers:
            if z3_model.evaluate(semantics.is_part_of(ver_bit, eval_world)):
                return True
        return False
    
    def find_precluders(self, py_verifier_set):
        """Find states that preclude the given set of verifiers."""
        # Convert Python set to Z3 set
        z3_verifier_set = self.semantics.z3_set(py_verifier_set, self.N)
        precludes = self.semantics.precludes
        all_states = self.semantics.all_states
        result = set()
        
        for state in all_states:
            preclude_formula = precludes(state, z3_verifier_set)
            preclude_result = self.model_structure.z3_model.evaluate(preclude_formula)
            # Check if the evaluated result is True
            if preclude_result == True:
                result.add(state)
        return result


class ExclusionStructure(model.ModelDefaults):
    """Model structure for exclusion semantics."""
    pass