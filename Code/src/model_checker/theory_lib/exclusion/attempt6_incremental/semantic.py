"""
Incremental exclusion semantics implementation.

This module implements exclusion semantics with incremental model checking,
maintaining persistent computational context across the three levels of
programmatic semantics: Syntax → Truth-Conditions → Extensions.

The key innovation is preserving witness information throughout verification,
enabling correct evaluation of exclusion formulas that require existential
quantification over mappings.
"""

import z3
import sys
import time
from typing import Dict, Set, List, Optional, Tuple, Any

from model_checker.utils import (
    ForAll,
    Exists,
    bitvec_to_substates,
    pretty_set_print,
    int_to_binary,
)
from model_checker import model
from model_checker import syntactic


class WitnessStore:
    """Maintains accessible witness mappings throughout verification."""
    
    def __init__(self):
        self.skolem_witnesses = {}      # h_sk -> actual function mapping
        self.existential_witnesses = {} # ∃x -> specific witness value  
        self.witness_dependencies = {}  # track which witnesses depend on others
        self.counter = 0
        
    def register_skolem_function(self, func_name: str, domain_type, codomain_type):
        """Register a Skolem function for later witness extraction."""
        self.skolem_witnesses[func_name] = {
            'type': (domain_type, codomain_type),
            'values': {},  # Will be populated incrementally
            'constraints': []  # Track constraints involving this function
        }
        
    def update_witness_values(self, model, semantics):
        """Extract witness values from current model state."""
        for func_name, witness_info in self.skolem_witnesses.items():
            domain_type, codomain_type = witness_info['type']
            
            # Get the function declaration from the model
            func_decl = self._find_function_in_model(model, func_name)
            if func_decl is None:
                continue
                
            # Extract all function mappings
            # For bit-vector functions, we need to check all possible inputs
            if str(domain_type) == f'BitVec({semantics.N})':
                for i in range(2 ** semantics.N):
                    input_val = z3.BitVecVal(i, semantics.N)
                    try:
                        # Apply the function to get output
                        output_val = model.evaluate(func_decl(input_val))
                        if output_val is not None:
                            witness_info['values'][i] = output_val.as_long() if hasattr(output_val, 'as_long') else output_val
                    except:
                        # Some inputs might not have defined outputs
                        pass
                        
    def _find_function_in_model(self, model, func_name):
        """Find a function declaration in the Z3 model by name."""
        # Z3 models contain declarations - search for our function
        for decl in model.decls():
            if decl.name() == func_name:
                return decl
        return None
                
    def get_witness_mapping(self, func_name: str) -> Dict:
        """Retrieve complete witness mapping for a Skolem function."""
        if func_name in self.skolem_witnesses:
            return self.skolem_witnesses[func_name]['values']
        return {}
        
    def is_witness_complete(self, func_name: str) -> bool:
        """Check if witness mapping is sufficiently determined."""
        if func_name not in self.skolem_witnesses:
            return False
        witness_info = self.skolem_witnesses[func_name]
        # For now, assume complete if we have any values
        return len(witness_info['values']) > 0


class TruthCache:
    """Maintains partial truth evaluations during incremental solving."""
    
    def __init__(self, semantics):
        self.semantics = semantics
        self.partial_truths = {}      # formula -> current truth status
        self.verifier_cache = {}      # formula -> current verifier set
        self.dependency_graph = {}    # track formula dependencies
        
    def update_verifiers(self, sentence, witness_store):
        """Recompute verifiers using current witness information."""
        if sentence.sentence_letter is not None:
            # Base case: atomic sentence
            return self.compute_atomic_verifiers(sentence, witness_store)
        else:
            # Recursive case: delegate to operator if it supports incremental verification
            if hasattr(sentence.operator, 'compute_verifiers'):
                verifiers = sentence.operator.compute_verifiers(
                    *sentence.arguments, witness_store, self
                )
                self.verifier_cache[sentence] = verifiers
                return verifiers
            else:
                # Fallback for operators without incremental support
                return set()
    
    def compute_atomic_verifiers(self, sentence, witness_store):
        """Compute verifiers for atomic sentences."""
        verifiers = set()
        
        # Check each possible state to see if it verifies the atom
        if hasattr(self.semantics, 'z3_model') and self.semantics.z3_model is not None:
            model = self.semantics.z3_model
            verify_func = self.semantics.verify
            
            # Check all possible states
            for i in range(2 ** self.semantics.N):
                state = z3.BitVecVal(i, self.semantics.N)
                # Check if this state verifies the sentence letter
                verify_constraint = verify_func(state, sentence.sentence_letter)
                try:
                    if z3.is_true(model.evaluate(verify_constraint)):
                        verifiers.add(i)
                except:
                    pass
                    
        return verifiers
        
    def get_verifiers(self, sentence, witness_store):
        """Get cached verifiers or compute them."""
        if sentence in self.verifier_cache:
            return self.verifier_cache[sentence]
        return self.update_verifiers(sentence, witness_store)


class IncrementalVerifier:
    """Unified constraint generation and truth evaluation with persistent state."""
    
    def __init__(self, semantics):
        self.semantics = semantics
        self.solver = z3.Solver()
        self.witness_store = WitnessStore()
        self.truth_cache = TruthCache(semantics)
        self.constraint_count = 0
        
    def verify_incrementally(self, sentence, eval_point):
        """Build constraints and evaluate truth incrementally with persistent state."""
        # Register witnesses for this sentence
        self._register_sentence_witnesses(sentence)
        
        # Build constraints incrementally
        constraints_added = []
        try:
            # Add constraints in stages, checking satisfiability at each step
            for constraint in self._generate_incremental_constraints(sentence, eval_point):
                self.solver.push()  # Create a backtrack point
                self.solver.add(constraint)
                constraints_added.append(constraint)
                
                # Check satisfiability after each constraint
                result = self.solver.check()
                if result == z3.sat:
                    # Extract model and update witnesses
                    model = self.solver.model()
                    self.witness_store.update_witness_values(model, self.semantics)
                    
                    # Update truth cache with current information
                    self.truth_cache.update_verifiers(sentence, self.witness_store)
                    
                    # Check if we have sufficient witnesses to evaluate
                    if self._has_sufficient_witnesses(sentence):
                        # Try to evaluate with current witnesses
                        truth_val = self._evaluate_with_witnesses(sentence, eval_point)
                        if truth_val is not None:
                            return truth_val
                elif result == z3.unsat:
                    # Backtrack and try alternative
                    self.solver.pop()
                    constraints_added.pop()
                    # In a full implementation, we might try alternative constraints
                    return False
                    
            # Final evaluation with all constraints
            final_result = self.solver.check()
            if final_result == z3.sat:
                model = self.solver.model()
                self.witness_store.update_witness_values(model, self.semantics)
                return True
            else:
                return False
                
        except Exception as e:
            # Cleanup on error
            for _ in constraints_added:
                if len(self.solver.assertions()) > 0:
                    self.solver.pop()
            raise e
            
    def _register_sentence_witnesses(self, sentence):
        """Register all witnesses needed for a sentence."""
        if sentence.sentence_letter is not None:
            # Atomic sentences don't need witnesses
            return
        elif hasattr(sentence.operator, 'register_witnesses'):
            # Let the operator register its witnesses
            sentence.operator.register_witnesses(*sentence.arguments, self.witness_store)
            
    def _generate_incremental_constraints(self, sentence, eval_point):
        """Generate constraints incrementally for a sentence."""
        # For now, just yield the standard constraint
        # Phase 2 will expand this to truly incremental generation
        yield self.semantics.true_at(sentence, eval_point)
        
    def _has_sufficient_witnesses(self, sentence):
        """Check if we have enough witness information to evaluate."""
        if sentence.sentence_letter is not None:
            return True
        elif hasattr(sentence.operator, 'has_sufficient_witnesses'):
            return sentence.operator.has_sufficient_witnesses(*sentence.arguments, self.witness_store)
        return False
        
    def _evaluate_with_witnesses(self, sentence, eval_point):
        """Try to evaluate sentence using current witness information."""
        if sentence.sentence_letter is not None:
            # Use standard evaluation for atomic sentences
            return None  # Let standard evaluation handle it
        elif hasattr(sentence.operator, 'evaluate_with_witnesses'):
            try:
                return sentence.operator.evaluate_with_witnesses(
                    *sentence.arguments, eval_point, self.witness_store, self.truth_cache
                )
            except:
                return None
        return None


class ExclusionSemantics(model.SemanticDefaults):
    """
    Incremental exclusion semantics with witness tracking.
    
    This implementation maintains persistent computational context across
    the three levels of programmatic semantics, enabling correct evaluation
    of exclusion formulas with existential quantification.
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
        "itermax": 100,
        "store_constraints": False,
        "timeout": 0,
    }

    proposition_class_name = "UnilateralProposition"
    
    def __init__(self, settings):
        super().__init__(settings)
        
        # Initialize relation_symbols list if not present
        if not hasattr(self, 'relation_symbols'):
            self.relation_symbols = []
        
        # Core components for incremental verification
        self.verifier = IncrementalVerifier(self)
        self.witness_store = self.verifier.witness_store
        self.truth_cache = self.verifier.truth_cache
        
        # Initialize verify relation
        self.verify = z3.Function(
            "verify",
            z3.BitVecSort(self.N),
            syntactic.AtomSort,
            z3.BoolSort(),
        )
        
        # Initialize exclusion relation
        if getattr(self, "exclusion", None) is None:
            exclusion_name = "Exclusion"
            exclusion_arity = self.N * self.N
            self.exclusion = z3.Function(
                exclusion_name, *([z3.BitVecSort(self.N)] * 2), z3.BoolSort()
            )
            self.relation_symbols.append(self.exclusion)
        
        # Set bitvector elements
        self.bitvec_elements = list(self.get_all_bitvectors())
        
        # Counter for unique variable names
        self.counter = 0
        
        # Set premise and conclusion behavior methods
        self.premise_behavior = self._premise_behavior_method
        self.conclusion_behavior = self._conclusion_behavior_method
        
        # Initialize main point
        self.main_point = {"world": z3.BitVec("main_world", self.N)}
        
        # Initialize frame constraints
        self.frame_constraints = self._get_frame_constraints()

    def setup_exclusion_constraints(self):
        """
        Set up basic exclusion relation constraints.
        """
        constraints = []
        
        # Basic properties of exclusion
        x = z3.BitVec("ex_setup_x", self.N)
        y = z3.BitVec("ex_setup_y", self.N)
        z = z3.BitVec("ex_setup_z", self.N)
        
        # Exclusion is symmetric
        symmetric = ForAll(
            [x, y],
            self.exclusion(x, y) == self.exclusion(y, x)
        )
        constraints.append(symmetric)
        
        # Exclusion respects parthood
        parthood_respect = ForAll(
            [x, y, z],
            z3.Implies(
                z3.And(
                    self.is_part_of(x, y),
                    self.exclusion(y, z)
                ),
                self.exclusion(x, z)
            )
        )
        constraints.append(parthood_respect)
        
        return constraints
    
    def conflicts(self, bit_e1, bit_e2):
        """Check if two states contain parts that exclude each other."""
        f1, f2 = z3.BitVecs("f1 f2", self.N)
        return Exists(
            [f1, f2],
            z3.And(
                self.is_part_of(f1, bit_e1),
                self.is_part_of(f2, bit_e2),
                self.exclusion(f1, f2),
            ),
        )
    
    def coheres(self, bit_e1, bit_e2):
        """Check if two states cohere (don't conflict)."""
        return z3.Not(self.conflicts(bit_e1, bit_e2))
    
    def possible(self, bit_e):
        """Check if a state is possible (self-coherent)."""
        return self.coheres(bit_e, bit_e)
    
    def is_world(self, bit_s):
        """Check if a state is a world (possible and maximal)."""
        m = z3.BitVec("m", self.N)
        return z3.And(
            self.possible(bit_s),
            z3.Not(
                Exists(
                    m,
                    z3.And(
                        self.is_proper_part_of(bit_s, m),
                        self.possible(m)
                    )
                )
            )
        )
    
    def atom_constraints(self, letter_id, sentence_letters, settings):
        """
        Return constraints for an atomic sentence.
        Simplified version for incremental approach.
        """
        N = self.N
        verify = self.verify
        
        # Get settings from provided dict
        contingent = settings.get('contingent', False)
        non_empty = settings.get('non_empty', False)
        non_null = settings.get('non_null', False)
        possible = settings.get('possible', True)
        
        # Variable for existential constraint
        v = z3.BitVec(f"atom_v_{letter_id}", N)
        
        # Build constraints list
        constraints = []
        
        # Verify relation constraints
        if contingent:
            # Contingent: some world verifies, some doesn't
            constraints.append(
                ("contingent_positive", Exists([v], verify(v, letter_id)))
            )
            constraints.append(
                ("contingent_negative", Exists([v], z3.Not(verify(v, letter_id))))
            )
        elif possible:
            # Possible: at least one world verifies
            constraints.append(
                ("possible", Exists([v], verify(v, letter_id)))
            )
        
        # Non-empty: verifier set is non-empty
        if non_empty:
            constraints.append(
                ("non_empty", Exists([v], verify(v, letter_id)))
            )
        
        # Non-null: no null state verifies
        if non_null:
            constraints.append(
                ("non_null", z3.Not(verify(self.null_state, letter_id)))
            )
        
        return constraints

    def get_all_bitvectors(self):
        """Get all possible bitvector values for the current N."""
        for i in range(2 ** self.N):
            yield z3.BitVecVal(i, self.N)

    def verify_formula(self, sentence, eval_point):
        """Main entry point for incremental verification with witness tracking."""
        # Use incremental verifier
        return self.verifier.verify_incrementally(sentence, eval_point)
        
    def set_z3_model(self, model):
        """Set the Z3 model for use in verifier computation."""
        self.z3_model = model
        # Update truth cache to use new model
        if hasattr(self, 'truth_cache'):
            self.truth_cache.model = model
    
    def true_at(self, sentence, eval_point):
        """
        Maintain compatibility with existing semantic interface.
        For Phase 1, this delegates to standard implementation.
        Phase 2 will integrate incremental evaluation.
        """
        if sentence.sentence_letter is not None:
            # Base case: atomic sentence
            v = z3.BitVec(f"v_atom_{id(sentence)}_{self.counter}", self.N)
            self.counter += 1
            return z3.Exists([v], z3.And(
                self.verify(v, sentence.sentence_letter),
                self.is_part_of(v, eval_point["world"])
            ))
        else:
            # Recursive case: delegate to operator
            return sentence.operator.true_at(*sentence.arguments, eval_point)
    
    def extended_verify(self, state, sentence, eval_point):
        """
        Maintain compatibility with existing semantic interface.
        Operators can register witnesses during extended_verify.
        """
        if sentence.sentence_letter is not None:
            # Base case: atomic sentence
            return self.verify(state, sentence.sentence_letter)
        else:
            # Recursive case: delegate to operator
            # In Phase 2, operators will register witnesses here
            return sentence.operator.extended_verify(state, *sentence.arguments, eval_point)
    
    def _premise_behavior_method(self, premise):
        """Premise must be true at main evaluation point."""
        return self.true_at(premise, self.main_point)

    def _conclusion_behavior_method(self, conclusion):
        """Conclusion must be false at main evaluation point."""
        return z3.Not(self.true_at(conclusion, self.main_point))
    
    def _get_frame_constraints(self):
        """Get frame constraints for exclusion semantics."""
        constraints = []
        
        # Add exclusion relation constraints
        constraints.extend(self.setup_exclusion_constraints())
        
        # Add fusion closure if requested
        if hasattr(self, 'settings') and self.settings.get('fusion_closure', False):
            # Fusion closure constraint
            x = z3.BitVec("fc_x", self.N)
            y = z3.BitVec("fc_y", self.N)
            z = z3.BitVec("fc_z", self.N)
            fusion_closure = ForAll(
                [x, y, z],
                z3.Implies(
                    z3.And(
                        self.is_part_of(x, z),
                        self.is_part_of(y, z)
                    ),
                    self.is_part_of(self.fusion(x, y), z)
                )
            )
            constraints.append(fusion_closure)
        
        return constraints


class UnilateralProposition(model.PropositionDefaults):
    """
    Proposition class for unilateral semantics.
    Uses only verifiers, no falsifiers.
    """
    
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
        model = self.model_structure.z3_model
        semantics = self.model_structure.semantics
        eval_world = self.model_structure.main_point["world"]
        
        if self.sentence.sentence_letter is not None:
            # Atomic sentence - find verifiers directly
            V = {
                state for state in self.model_structure.all_states
                if model.evaluate(semantics.verify(state, self.sentence.sentence_letter))
            }
            return V
        elif self.sentence.operator is not None:
            # Complex sentence - delegate to operator
            return self.sentence.operator.find_verifiers(
                *self.sentence.arguments, self.model_structure.main_point
            )
        else:
            raise ValueError(f"No proposition for {self.sentence}")

    def truth_value_at(self, eval_world):
        """Check if there is a verifier in world."""
        semantics = self.model_structure.semantics
        z3_model = self.model_structure.z3_model
        for ver_bit in self.verifiers:
            if z3_model.evaluate(semantics.is_part_of(ver_bit, eval_world)):
                return True
        return False

    def print_proposition(self, evaluation_point, indent_num, use_colors):
        """Print proposition details for unilateral semantics."""
        # In unilateral semantics, we only print verifiers
        if use_colors:
            CYAN, RESET = '\033[36m', '\033[0m'
        else:
            CYAN, RESET = '', ''
            
        prefix = " " * indent_num
        print(f"{prefix}Verifiers: {pretty_set_print(self.verifiers)}")