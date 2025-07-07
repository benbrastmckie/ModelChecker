"""
Witness predicate semantics implementation.

This module implements the core semantics that includes witness functions as
model predicates. It extends the standard exclusion semantics by registering
witness predicates for all exclusion formulas and generating constraints
that define their behavior.
"""

import z3
from typing import List, Dict, Set, Optional, Tuple
from model_checker.model import ModelDefaults, SemanticDefaults, PropositionDefaults
from model_checker.utils import ForAll, Exists, bitvec_to_substates, pretty_set_print, int_to_binary
from model_checker import syntactic
from .witness_model import WitnessAwareModel, WitnessPredicateRegistry
from .witness_constraints import WitnessConstraintGenerator


class WitnessPredicateSemantics(SemanticDefaults):
    """
    Semantics that includes witness functions as model predicates.
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
    
    # Default general settings for the exclusion theory
    DEFAULT_GENERAL_SETTINGS = {
        "print_impossible": False,
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,
        "maximize": False,
    }
    
    def __init__(self, settings):
        super().__init__(settings)
        self.witness_registry = WitnessPredicateRegistry(self.N)
        self.constraint_generator = WitnessConstraintGenerator(self)
        self._processed_formulas = set()
        self._formula_ast_mapping = {}  # Store formula string -> AST mapping
        
        # Define Z3 primitives needed for exclusion semantics
        self.verify = z3.Function(
            "verify",
            z3.BitVecSort(self.N),
            syntactic.AtomSort,
            z3.BoolSort(),
        )
        
        self.excludes = z3.Function(
            "excludes",
            z3.BitVecSort(self.N),
            z3.BitVecSort(self.N),
            z3.BoolSort(),
        )
        
        self.main_world = z3.BitVec("w", self.N)
        self.main_point = {"world": self.main_world}
        
        # Simple counter for unique naming
        self.counter = 0
        
        # Override premise and conclusion behavior attributes
        self.premise_behavior = self._premise_behavior_method
        self.conclusion_behavior = self._conclusion_behavior_method
        
        # Define additional semantic relations
        self._define_semantic_relations()
        
        # Define frame constraints
        self._setup_frame_constraints()
        
    def _define_semantic_relations(self):
        """Define additional semantic relations needed for exclusion logic."""
        N = self.N
        
        # Possible relation - states that could exist
        self.possible = z3.Function(
            "possible",
            z3.BitVecSort(N),
            z3.BoolSort()
        )
        
        # Coherence relation - states that don't exclude each other
        self.coheres = z3.Function(
            "coheres",
            z3.BitVecSort(N),
            z3.BitVecSort(N),
            z3.BoolSort()
        )
        
        # Compossible relation - states that can coexist
        self.compossible = z3.Function(
            "compossible",
            z3.BitVecSort(N),
            z3.BitVecSort(N),
            z3.BoolSort()
        )
        
    def is_world(self, bit_s):
        """
        Determines if a state is a world by checking if it is possible and maximal.
        A state is maximal if it has no proper extension that is possible.
        """
        m = z3.BitVec("m", self.N)
        return z3.And(
            self.possible(bit_s),
            z3.Not(
                Exists(
                    [m],
                    z3.And(
                        self.is_proper_part_of(bit_s, m),
                        self.possible(m)
                    )
                )
            )
        )
        
    def build_model(self, eval_point):
        """
        Build model with witness predicates included.
        """
        # Clear previous state
        self.witness_registry.clear()
        self._processed_formulas.clear()
        self._formula_ast_mapping.clear()
        
        # Create solver
        solver = z3.Solver()
        
        # Add frame constraints
        for constraint in self._get_frame_constraints():
            solver.add(constraint)
            
        # Process premises and conclusions
        premises = eval_point.get("premises", [])
        conclusions = eval_point.get("conclusions", [])
        
        # First pass: identify all exclusion formulas and create witness predicates
        all_formulas = premises + conclusions
        for formula in all_formulas:
            self._register_witness_predicates_recursive(formula)
            
        # Add witness predicate constraints
        witness_constraints = self._generate_all_witness_constraints(eval_point)
        for constraint in witness_constraints:
            solver.add(constraint)
            
        # Add premise constraints
        world = eval_point["world"]
        for premise in premises:
            solver.add(self.extended_verify(world, premise, eval_point))
            
        # Add conclusion constraints (negated)
        for conclusion in conclusions:
            solver.add(z3.Not(self.extended_verify(world, conclusion, eval_point)))
            
        # Check satisfiability
        if solver.check() == z3.sat:
            z3_model = solver.model()
            return WitnessAwareModel(
                z3_model,
                self,
                self.witness_registry.get_all_predicates()
            )
        else:
            return None
            
    def _register_witness_predicates_recursive(self, formula):
        """
        Recursively register witness predicates for all exclusion
        subformulas in the formula.
        """
        if self._is_processed(formula):
            return
            
        if hasattr(formula, 'operator') and formula.operator.name == "\\exclude":
            # Register witness predicates for this exclusion
            formula_str = self._formula_to_string(formula)
            self.witness_registry.register_witness_predicates(formula_str)
            self._processed_formulas.add(formula_str)
            self._formula_ast_mapping[formula_str] = formula
            
        # Recurse on arguments if they exist
        if hasattr(formula, 'arguments'):
            for arg in formula.arguments:
                self._register_witness_predicates_recursive(arg)
                
    def _is_processed(self, formula) -> bool:
        """Check if formula already has witness predicates."""
        formula_str = self._formula_to_string(formula)
        return formula_str in self._processed_formulas
        
    def _formula_to_string(self, formula) -> str:
        """Convert formula to unique string representation."""
        if hasattr(formula, 'proposition'):
            return formula.proposition
        elif hasattr(formula, 'operator'):
            args_str = ",".join(self._formula_to_string(arg) for arg in formula.arguments)
            return f"{formula.operator.name}({args_str})"
        else:
            return str(formula)
            
    def _generate_all_witness_constraints(self, eval_point) -> List[z3.BoolRef]:
        """
        Generate constraints for all registered witness predicates.
        """
        constraints = []
        
        for formula_str in self._processed_formulas:
            # Get the formula AST
            formula_ast = self._formula_ast_mapping.get(formula_str)
            if formula_ast and hasattr(formula_ast, 'operator') and formula_ast.operator.name == "\\exclude":
                h_pred, y_pred = self._get_witness_predicates(formula_str)
                
                formula_constraints = self.constraint_generator.generate_witness_constraints(
                    formula_str, formula_ast, h_pred, y_pred, eval_point
                )
                constraints.extend(formula_constraints)
                
        return constraints
        
    def _get_witness_predicates(self, formula_str: str) -> Tuple[z3.FuncDeclRef, z3.FuncDeclRef]:
        """Get witness predicates for a formula."""
        h_pred = self.witness_registry.predicates.get(f"{formula_str}_h")
        y_pred = self.witness_registry.predicates.get(f"{formula_str}_y")
        return h_pred, y_pred
        
    def extended_verify(self, state, sentence, eval_point):
        """
        Extended verification with proper recursive reduction.
        
        For atomic sentences: direct verification
        For complex sentences: delegates to operator's extended_verify method
        """
        if sentence.sentence_letter is not None:
            # Atomic case: verify(state, atom)
            return self.verify(state, sentence.sentence_letter)
        else:
            # Complex case: delegate to operator
            return sentence.operator.extended_verify(state, *sentence.arguments, eval_point)
            
    def extended_compute_verifiers(self, sentence, model, eval_point):
        """Compute verifiers for a sentence using the model."""
        if sentence.sentence_letter is not None:
            # Atomic case: find all states that verify this atom
            verifiers = []
            for state in range(2**self.N):
                state_bv = z3.BitVecVal(state, self.N)
                if z3.is_true(model.eval(self.verify(state_bv, sentence.sentence_letter))):
                    verifiers.append(state)
            return verifiers
        else:
            # Complex case: delegate to operator
            return sentence.operator.compute_verifiers(*sentence.arguments, model=model, eval_point=eval_point)
            
    def true_at(self, sentence, eval_point):
        """Check if sentence is true at evaluation point."""
        if sentence.sentence_letter is not None:
            # Atomic case: check if world verifies the atom
            world = eval_point["world"]
            return self.verify(world, sentence.sentence_letter)
        else:
            # Complex case: delegate to operator
            return sentence.operator.true_at(*sentence.arguments, eval_point)
            
    def _setup_frame_constraints(self):
        """Setup basic frame constraints for the exclusion semantics."""
        x, y, z, u = z3.BitVecs("frame_x frame_y frame_z frame_u", self.N)
        
        # Actuality constraint
        actuality = self.is_world(self.main_world)
        
        # Basic exclusion properties
        exclusion_symmetry = ForAll(
            [x, y],
            z3.Implies(
                self.excludes(x, y),
                self.excludes(y, x)
            )
        )
        
        # Null state excludes nothing
        null_state = ForAll(x, z3.Not(self.excludes(self.null_state, x)))
        
        # Store frame constraints
        self.basic_constraints = [
            actuality,
            exclusion_symmetry,
            null_state
        ]
        
        # Set frame_constraints attribute required by ModelConstraints
        self.frame_constraints = self.basic_constraints
        
    def _get_frame_constraints(self):
        """Get all frame constraints for the model."""
        constraints = []
        constraints.extend(self.basic_constraints)
        
        # Add standard semantic constraints
        if hasattr(self, 'semantic_constraints'):
            constraints.extend(self.semantic_constraints)
            
        return constraints
        
    def _exclusion_verify_constraint(self, state, argument, eval_point):
        """Generate basic exclusion verification constraint."""
        # This is a placeholder - the actual constraint is generated
        # by the witness constraint generator
        return z3.BoolVal(True)  # Will be overridden by witness constraints
        
    def atom_constraints(self, letter_id, sentence_letters, settings):
        """
        Return constraints for an atomic sentence.
        """
        N = self.N
        verify = self.verify
        
        # Get settings from provided dict
        contingent = settings.get('contingent', False)
        non_empty = settings.get('non_empty', False)
        non_null = settings.get('non_null', False)
        disjoint = settings.get('disjoint', False)
        
        atom_constraints = []
        
        # Non-empty constraint
        if non_empty:
            state = z3.BitVec("state", N)
            atom_constraints.append(Exists([state], verify(state, letter_id)))
        
        # Non-null constraint
        if non_null:
            atom_constraints.append(z3.Not(verify(self.null_state, letter_id)))
        
        # Contingent constraint (both satisfied and unsatisfied)
        if contingent:
            state = z3.BitVec("state", N)
            atom_constraints.extend([
                Exists([state], verify(state, letter_id)),
                Exists([state], z3.Not(verify(state, letter_id)))
            ])
        
        # Disjoint constraint
        if disjoint:
            for other_letter in sentence_letters:
                if other_letter != letter_id:
                    state = z3.BitVec("state", N)
                    atom_constraints.append(
                        ForAll([state], 
                            z3.Not(z3.And(
                                verify(state, letter_id),
                                verify(state, other_letter)
                            ))
                        )
                    )
        
        return atom_constraints
        
    def _premise_behavior_method(self, premise):
        """Premise must be true at main evaluation point."""
        return self.true_at(premise, self.main_point)

    def _conclusion_behavior_method(self, conclusion):
        """Conclusion must be false at main evaluation point."""
        return z3.Not(self.true_at(conclusion, self.main_point))


class PredicateModelAdapter(ModelDefaults):
    """
    Adapter to make witness predicate semantics compatible with ModelChecker.
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
    
    # Default general settings for the exclusion theory
    DEFAULT_GENERAL_SETTINGS = {
        "print_impossible": False,
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,
        "maximize": False,
    }
    
    def __init__(self, settings):
        super().__init__(settings)
        self.semantics = WitnessPredicateSemantics(settings)
        self.settings = settings
        
    def build_model(self, eval_point):
        """Build model using witness predicate approach."""
        return self.semantics.build_model(eval_point)
        
    def extended_verify(self, state, sentence, eval_point):
        """Delegate to semantics."""
        return self.semantics.extended_verify(state, sentence, eval_point)
        
    def extended_compute_verifiers(self, sentence, model, eval_point):
        """Delegate to semantics."""
        return self.semantics.extended_compute_verifiers(sentence, model, eval_point)


class WitnessPredicateProposition(PropositionDefaults):
    """Proposition class for witness predicate semantics."""
    
    def __init__(self, sentence, model_structure):
        super().__init__(sentence, model_structure)
        self.z3_model = model_structure.z3_model
        self.verifiers = self.find_proposition()
    
    @classmethod
    def proposition_constraints(cls, model_constraints, letter_id):
        """Generate constraints for atomic propositions."""
        return model_constraints.semantics.atom_constraints(
            letter_id,
            model_constraints.sentence_letters,
            model_constraints.settings
        )

    def find_proposition(self):
        """Find the set of verifiers for this sentence."""
        result = set()
        semantics = self.model_structure.semantics
        eval_point = semantics.main_point
        
        # Check each state to see if it verifies the sentence
        for state in range(2**semantics.N):
            constraint = semantics.extended_verify(state, self.sentence, eval_point)
            if z3.is_true(self.z3_model.evaluate(constraint)):
                result.add(state)
        return result
        
    def truth_value_at(self, eval_point):
        """Evaluate truth value at a point."""
        return self.model_structure.semantics.true_at(self.sentence, eval_point)
        
    def print_method(self, eval_point, indent_num, use_colors):
        """Print the proposition."""
        self.print_proposition(eval_point, indent_num, use_colors)
        
    def print_proposition(self, eval_point, indent_num, use_colors):
        """Print the proposition with its truth value at the evaluation point."""
        from model_checker.utils import bitvec_to_substates
        
        N = self.model_structure.semantics.N
        z3_formula = self.truth_value_at(eval_point)
        truth_value = z3.is_true(self.model_structure.z3_model.evaluate(z3_formula))
        world_state = bitvec_to_substates(eval_point["world"], N)
        RESET, FULL, PART = self.set_colors(self.name, indent_num, truth_value, world_state, use_colors)
        print(
            f"{'  ' * indent_num}{FULL}|{self.name}| = {self}{RESET}"
            f"  {PART}({truth_value} in {world_state}){RESET}"
        )