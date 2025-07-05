"""
Incremental Model Structure for Exclusion Theory

This module provides an IncrementalModelStructure that extends the default
ModelStructure to support incremental constraint building and witness tracking.
The key innovation is intercepting the solve() process to maintain persistent
solver state and extract witness values during constraint generation.
"""

import z3
import time
from typing import Dict, Set, List, Optional, Tuple, Any

from model_checker.model import ModelDefaults
from model_checker.theory_lib.default import ModelStructure


class IncrementalModelStructure(ModelStructure):
    """
    ModelStructure that uses incremental solving with witness tracking.
    
    This class overrides the solve() method to implement incremental constraint
    building while maintaining full backward compatibility with the standard
    ModelChecker interface.
    """
    
    def __init__(self, model_constraints, settings):
        """Initialize with incremental solving capabilities."""
        # Initialize parent class attributes without calling solve
        # (We'll override the solve process)
        
        # Copy initialization from ModelDefaults but skip solve()
        self.COLORS = {
            "default": "\033[37m",  # WHITE
            "world": "\033[34m",    # BLUE
            "possible": "\033[36m", # CYAN
            "impossible": "\033[35m", # MAGENTA
            "initial": "\033[33m",  # YELLOW
        }
        self.RESET = "\033[0m"
        self.WHITE = self.COLORS["default"]

        # Dictionary for tracking constraints for unsat_core
        self.constraint_dict = {}

        # Store arguments - but we'll bypass model_constraints for constraint generation
        self.settings = settings
        self.max_time = self.settings["max_time"]
        self.expectation = self.settings["expectation"]

        # Extract what we need directly from model_constraints
        self.semantics = model_constraints.semantics
        self.syntax = model_constraints.syntax
        self.sentence_letters = model_constraints.sentence_letters
        self.proposition_class = model_constraints.proposition_class
        
        # Store direct references
        self.main_point = self.semantics.main_point
        self.all_states = self.semantics.all_states
        self.N = self.semantics.N
        self.start_time = self.syntax.start_time
        self.premises = self.syntax.premises
        self.conclusions = self.syntax.conclusions
        
        # Initialize incremental components
        self.witness_store = WitnessStore()
        self.incremental_solver = IncrementalSolver(self.semantics)
        
        # Connect witness store to semantics for operator access
        self.semantics.witness_store = self.witness_store
        
        # Generate and solve constraints using pure incremental approach
        solver_results = self.solve_incrementally_pure(self.max_time)
        self.z3_model_timeout, self.z3_model, self.z3_model_status, self.z3_model_runtime = solver_results
        
        # Store model data for framework compatibility
        self.unsat_core = None if self.z3_model_status else self.z3_model
        
        # Continue with default ModelStructure initialization if we have a model
        if self.z3_model_status and self.z3_model is not None:
            # Get main_world from main_point
            self.main_world = self.main_point["world"]
            self.z3_main_world = self.z3_model[self.main_world]
            self.main_point["world"] = self.z3_main_world
            self.z3_possible_states = [
                bit for bit in self.all_states
                if bool(self.z3_model.evaluate(self.semantics.possible(bit)))
            ]
            self.z3_world_states = [
                state for state in self.z3_possible_states
                if bool(self.z3_model.evaluate(self.semantics.is_world(state)))
            ]
            
            # Initialize attributes for difference tracking
            self.model_differences = None
            self.previous_model = None
    
    def solve_incrementally(self, model_constraints, max_time):
        """
        Solve constraints incrementally with witness tracking.
        
        This method replaces the standard batch solving approach with
        incremental constraint addition, allowing witness extraction
        at each step.
        """
        try:
            start_time = time.time()
            
            # Set up incremental solver
            self.incremental_solver.reset()
            self.incremental_solver.set_timeout(max_time)
            
            # Add frame constraints first (these rarely cause issues)
            for constraint in model_constraints.frame_constraints:
                result = self.incremental_solver.add_constraint_incrementally(
                    constraint, "frame", self.witness_store
                )
                if not result:
                    return self._create_result(False, None, False, start_time)
            
            # Add model constraints (atomic proposition constraints)
            for i, constraint in enumerate(model_constraints.model_constraints):
                result = self.incremental_solver.add_constraint_incrementally(
                    constraint, f"model{i+1}", self.witness_store
                )
                if not result:
                    return self._create_result(False, None, False, start_time)
            
            # USE INCREMENTAL VERIFICATION FOR PREMISE/CONCLUSION CONSTRAINTS
            # This is where the key difference lies - instead of using standard
            # constraint generation, we use the incremental verifier with witness tracking
            
            # Add premise constraints using standard approach for now
            for i, constraint in enumerate(model_constraints.premise_constraints):
                result = self.incremental_solver.add_constraint_incrementally(
                    constraint, f"premise{i+1}", self.witness_store
                )
                if not result:
                    return self._create_result(False, None, False, start_time)
            
            # Add conclusion constraints using standard approach for now  
            for i, constraint in enumerate(model_constraints.conclusion_constraints):
                result = self.incremental_solver.add_constraint_incrementally(
                    constraint, f"conclusion{i+1}", self.witness_store
                )
                if not result:
                    return self._create_result(False, None, False, start_time)
            
            # Final check and extract complete model
            final_result = self.incremental_solver.check()
            if final_result == z3.sat:
                model = self.incremental_solver.model()
                # Final witness extraction
                self.witness_store.update_witness_values(model, self.semantics)
                return self._create_result(False, model, True, start_time)
            else:
                return self._create_result(False, None, False, start_time)
                
        except Exception as e:
            print(f"Error in incremental solving: {e}")
            import traceback
            traceback.print_exc()
            return self._create_result(False, None, False, start_time)
    
    def solve_incrementally_pure(self, max_time):
        """
        Pure incremental solving that bypasses ModelConstraints entirely.
        
        This method generates constraints on-demand with witness tracking,
        implementing the true streaming constraint model needed for exclusion theory.
        """
        try:
            start_time = time.time()
            
            # Set up incremental solver
            self.incremental_solver.reset()
            self.incremental_solver.set_timeout(max_time)
            
            # Phase 1: Add frame constraints (semantic structure)
            if not self._add_frame_constraints():
                return self._create_result(False, None, False, start_time)
            
            # Phase 2: Add atomic proposition constraints  
            if not self._add_atomic_constraints():
                return self._create_result(False, None, False, start_time)
            
            # Phase 3: Add premise constraints with incremental evaluation
            if not self._add_premise_constraints_incremental():
                return self._create_result(False, None, False, start_time)
            
            # Phase 4: Add conclusion constraints for countermodel search
            if not self._add_conclusion_constraints_incremental():
                return self._create_result(False, None, False, start_time)
            
            # Final check and extract complete model
            final_result = self.incremental_solver.check()
            if final_result == z3.sat:
                model = self.incremental_solver.model()
                # Final witness extraction
                self.witness_store.update_witness_values(model, self.semantics)
                return self._create_result(False, model, True, start_time)
            else:
                return self._create_result(False, None, False, start_time)
                
        except Exception as e:
            print(f"Error in pure incremental solving: {e}")
            import traceback
            traceback.print_exc()
            return self._create_result(False, None, False, start_time)
    
    def _add_frame_constraints(self):
        """Add frame constraints (semantic structure)."""
        # Use the frame constraints from semantics
        frame_constraints = self.semantics._get_frame_constraints()
        
        for i, constraint in enumerate(frame_constraints):
            result = self.incremental_solver.add_constraint_incrementally(
                constraint, f"frame_{i}", self.witness_store
            )
            if not result:
                return False
        return True
    
    def _add_atomic_constraints(self):
        """Add constraints for atomic propositions."""
        # Generate atomic constraints for each sentence letter
        for letter_id in self.sentence_letters:
            constraints = self.semantics.atom_constraints(
                letter_id, self.sentence_letters, self.settings
            )
            
            # Extract Z3 constraints from labeled tuples
            for label, constraint in constraints:
                result = self.incremental_solver.add_constraint_incrementally(
                    constraint, f"atom_{letter_id}_{label}", self.witness_store
                )
                if not result:
                    return False
        return True
    
    def _add_premise_constraints_incremental(self):
        """Add premise constraints using incremental evaluation with witness tracking."""
        for i, premise in enumerate(self.premises):
            # Generate constraint using incremental approach
            constraint = self._generate_incremental_constraint(
                premise, self.main_point, constraint_type="premise"
            )
            
            result = self.incremental_solver.add_constraint_incrementally(
                constraint, f"premise_{i}", self.witness_store
            )
            if not result:
                return False
        return True
    
    def _add_conclusion_constraints_incremental(self):
        """Add conclusion constraints using incremental evaluation for countermodel search."""
        for i, conclusion in enumerate(self.conclusions):
            # Generate negated constraint for countermodel search
            positive_constraint = self._generate_incremental_constraint(
                conclusion, self.main_point, constraint_type="conclusion"
            )
            # Negate for countermodel search
            constraint = z3.Not(positive_constraint)
            
            result = self.incremental_solver.add_constraint_incrementally(
                constraint, f"conclusion_{i}", self.witness_store
            )
            if not result:
                return False
        return True
    
    def _generate_incremental_constraint(self, sentence, eval_point, constraint_type="premise"):
        """
        Generate constraint for a sentence using incremental approach with witness tracking.
        
        This is the core method that implements incremental constraint generation,
        calling operators that can register and access witness functions.
        """
        # Pre-register witnesses for this sentence
        self._register_witnesses_for_sentence(sentence)
        
        # Generate constraint with witness tracking enabled
        if sentence.sentence_letter is not None:
            # Atomic sentence - use standard evaluation
            v = z3.BitVec(f"v_{constraint_type}_{id(sentence)}", self.N)
            return z3.Exists([v], z3.And(
                self.semantics.verify(v, sentence.sentence_letter),
                self.semantics.is_part_of(v, eval_point["world"])
            ))
        else:
            # Complex sentence - use operator with witness access
            # The key difference: operators can now access witness_store during constraint generation
            return sentence.operator.true_at(*sentence.arguments, eval_point)
    
    def _register_witnesses_for_sentence(self, sentence):
        """Recursively register witnesses for a sentence and its subsentences."""
        if sentence.sentence_letter is not None:
            # Atomic sentence - no witnesses needed
            return
        elif hasattr(sentence.operator, 'register_witnesses'):
            # Register witnesses for this operator
            sentence.operator.register_witnesses(*sentence.arguments, self.witness_store)
        
        # Recursively register for arguments
        if sentence.arguments:
            for arg in sentence.arguments:
                self._register_witnesses_for_sentence(arg)
    
    def _create_result(self, is_timeout, model_or_core, is_satisfiable, start_time):
        """Create standardized result tuple."""
        runtime = round(time.time() - start_time, 4)
        return is_timeout, model_or_core, is_satisfiable, runtime


class IncrementalSolver:
    """
    Wrapper around Z3 solver that supports incremental constraint addition
    with witness extraction at each step.
    """
    
    def __init__(self, semantics):
        self.semantics = semantics
        self.solver = z3.Solver()
        self.constraint_stack = []
        
    def reset(self):
        """Reset solver state for new problem."""
        self.solver = z3.Solver()
        self.constraint_stack = []
    
    def set_timeout(self, max_time):
        """Set solver timeout."""
        self.solver.set("timeout", int(max_time * 1000))
    
    def add_constraint_incrementally(self, constraint, constraint_id, witness_store):
        """
        Add constraint incrementally with immediate satisfiability check and witness extraction.
        
        Returns True if constraint is satisfiable, False otherwise.
        """
        # Create checkpoint for backtracking
        self.solver.push()
        
        try:
            # Add constraint
            self.solver.add(constraint)
            self.constraint_stack.append((constraint, constraint_id))
            
            # Check satisfiability
            result = self.solver.check()
            
            if result == z3.sat:
                # Extract witness information from current model
                model = self.solver.model()
                witness_store.update_witness_values(model, self.semantics)
                return True
            elif result == z3.unsat:
                # Backtrack - this constraint makes the system unsatisfiable
                self.solver.pop()
                self.constraint_stack.pop()
                return False
            else:
                # Unknown - treat as satisfiable for now
                return True
                
        except Exception as e:
            print(f"  ❌ Error adding constraint {constraint_id}: {e}")
            # Backtrack on error
            self.solver.pop()
            if self.constraint_stack and self.constraint_stack[-1][1] == constraint_id:
                self.constraint_stack.pop()
            return False
    
    def check(self):
        """Perform final satisfiability check."""
        return self.solver.check()
    
    def model(self):
        """Get current model."""
        return self.solver.model()


class WitnessStore:
    """
    Stores and manages witness values extracted from Z3 models during
    incremental solving. This enables accessing Skolem function interpretations
    throughout the verification process.
    """
    
    def __init__(self):
        self.skolem_witnesses = {}      # func_name -> witness data
        self.existential_witnesses = {} # witness_name -> value
        self.witness_dependencies = {}  # dependency tracking
        self.counter = 0
        
    def register_skolem_function(self, func_name: str, domain_type, codomain_type):
        """Register a Skolem function for witness tracking."""
        self.skolem_witnesses[func_name] = {
            'type': (domain_type, codomain_type),
            'values': {},  # domain_val -> codomain_val
            'constraints': [],
            'complete': False
        }
        
    def update_witness_values(self, model, semantics):
        """Extract witness values from current Z3 model."""
        for func_name, witness_info in self.skolem_witnesses.items():
            domain_type, codomain_type = witness_info['type']
            
            # Find the function in the model
            func_decl = self._find_function_in_model(model, func_name)
            if func_decl is None:
                continue
                
            # Extract function mappings for bit-vector domains
            if str(domain_type) == f'BitVec({semantics.N})':
                for i in range(2 ** semantics.N):
                    input_val = z3.BitVecVal(i, semantics.N)
                    try:
                        output_val = model.evaluate(func_decl(input_val))
                        if output_val is not None:
                            witness_info['values'][i] = (
                                output_val.as_long() if hasattr(output_val, 'as_long') 
                                else output_val
                            )
                    except:
                        pass
                        
                # Mark as complete if we have reasonable coverage
                if len(witness_info['values']) > 0:
                    witness_info['complete'] = True
    
    def _find_function_in_model(self, model, func_name):
        """Find function declaration in Z3 model by name."""
        for decl in model.decls():
            if decl.name() == func_name:
                return decl
        return None
    
    def get_witness_mapping(self, func_name: str) -> Dict:
        """Get complete witness mapping for a function."""
        if func_name in self.skolem_witnesses:
            return self.skolem_witnesses[func_name]['values']
        return {}
    
    def is_witness_complete(self, func_name: str) -> bool:
        """Check if witness function has sufficient information."""
        if func_name not in self.skolem_witnesses:
            return False
        return self.skolem_witnesses[func_name]['complete']
    
    def register_existential_witness(self, witness_name: str, value):
        """Register an existential witness value."""
        self.existential_witnesses[witness_name] = value
    
    def get_existential_witness(self, witness_name: str):
        """Get existential witness value."""
        return self.existential_witnesses.get(witness_name)
    
    def has_witnesses_for(self, func_names: List[str]) -> bool:
        """Check if we have complete witnesses for all given functions."""
        return all(self.is_witness_complete(name) for name in func_names)
    
    def clear(self):
        """Clear all witness information."""
        self.skolem_witnesses.clear()
        self.existential_witnesses.clear()
        self.witness_dependencies.clear()