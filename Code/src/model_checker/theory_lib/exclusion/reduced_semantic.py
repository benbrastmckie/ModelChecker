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


class UnilateralProposition(model.PropositionDefaults):
    """Unilateral proposition for exclusion semantics."""
    
    def find_proposition(self):
        """Find the set of verifiers for this proposition."""
        # This is Z3 model evaluation, not constraint generation
        if self.model_structure.z3_model:
            return super().find_proposition()
        else:
            return set()


class ExclusionStructure(model.ModelDefaults):
    """Model structure for exclusion semantics."""
    pass