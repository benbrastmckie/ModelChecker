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
try:
    from .truth_cache import TruthCache
except ImportError:
    from truth_cache import TruthCache


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
        
        # Store model_constraints for framework compatibility
        self.model_constraints = model_constraints

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
        self.truth_cache = TruthCache(self.semantics)
        self.incremental_solver = IncrementalSolver(self.semantics)
        
        # Phase 3: Create IncrementalVerifier for full integration
        self.incremental_verifier = IncrementalVerifier(
            self.semantics, 
            self.incremental_solver.solver,
            self.witness_store,
            self.truth_cache
        )
        
        # Connect components to semantics for operator access
        self.semantics.witness_store = self.witness_store
        self.semantics.truth_cache = self.truth_cache
        self.semantics.incremental_verifier = self.incremental_verifier
        
        # Generate and solve constraints using pure incremental approach
        solver_results = self.solve_incrementally_pure(self.max_time)
        self.z3_model_timeout, self.z3_model, self.z3_model_status, self.z3_model_runtime = solver_results
        
        # Store model data for framework compatibility
        self.unsat_core = None if self.z3_model_status else self.z3_model
        
        # Store solver reference for framework compatibility
        self.solver = self.incremental_solver.solver
        self.stored_solver = self.solver
        
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
            # Phase 3: Check if we can use IncrementalVerifier for early termination
            if self._should_use_incremental_verification(premise):
                # Use IncrementalVerifier for complex formulas with witnesses
                result = self.incremental_verifier.verify_incrementally(premise, self.main_point)
                if result is False:  # Definitely false
                    return False
                elif result is True:  # Definitely true, add simplified constraint
                    constraint = z3.BoolVal(True)
                else:  # Need full constraint
                    constraint = self._generate_incremental_constraint(
                        premise, self.main_point, constraint_type="premise"
                    )
            else:
                # Use standard constraint generation for simple formulas
                constraint = self._generate_incremental_constraint(
                    premise, self.main_point, constraint_type="premise"
                )
            
            result = self.incremental_solver.add_constraint_incrementally(
                constraint, f"premise_{i}", self.witness_store
            )
            if not result:
                return False
        return True
    
    def _should_use_incremental_verification(self, sentence):
        """Determine if a sentence would benefit from incremental verification."""
        # Use incremental verification for complex formulas with exclusion
        if sentence.sentence_letter is not None:
            return False  # Atomic sentences don't benefit
        
        # Check if sentence contains exclusion operators
        def has_exclusion(sent):
            if sent.sentence_letter is not None:
                return False
            if sent.operator.name == "\\exclude":
                return True
            return any(has_exclusion(arg) for arg in sent.arguments)
        
        return has_exclusion(sentence)
    
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
    
    Phase 2 enhancements:
    - Dependency tracking between witnesses
    - Caching of witness values with smart invalidation
    - History tracking for debugging and optimization
    """
    
    def __init__(self):
        self.skolem_witnesses = {}      # func_name -> witness data
        self.existential_witnesses = {} # witness_name -> value
        self.witness_dependencies = {}  # func_name -> set of dependent func_names
        self.witness_cache = {}         # (func_name, args) -> cached result
        self.witness_history = []       # list of (timestamp, func_name, event)
        self.invalidation_queue = []    # functions pending invalidation
        self.counter = 0
        self.cache_hits = 0
        self.cache_misses = 0
        
    def register_skolem_function(self, func_name: str, domain_type, codomain_type):
        """Register a Skolem function for witness tracking."""
        self.skolem_witnesses[func_name] = {
            'type': (domain_type, codomain_type),
            'values': {},  # domain_val -> codomain_val
            'constraints': [],
            'complete': False
        }
        # Record in history
        self.witness_history.append((time.time(), func_name, "registered"))
        
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
        self.witness_cache.clear()
        self.witness_history.clear()
        self.invalidation_queue.clear()
        self.cache_hits = 0
        self.cache_misses = 0
    
    # Phase 2 methods: Dependency tracking
    
    def register_dependent_witnesses(self, parent_func: str, child_funcs: List[str]):
        """Track witness dependencies for incremental updates."""
        if parent_func not in self.witness_dependencies:
            self.witness_dependencies[parent_func] = set()
        self.witness_dependencies[parent_func].update(child_funcs)
        
        # Record in history
        self.witness_history.append((time.time(), parent_func, f"registered_deps: {child_funcs}"))
    
    def invalidate_dependent_witnesses(self, func_name: str):
        """Invalidate witnesses that depend on changed values."""
        # Add to invalidation queue
        if func_name not in self.invalidation_queue:
            self.invalidation_queue.append(func_name)
        
        # Process invalidation queue
        while self.invalidation_queue:
            current_func = self.invalidation_queue.pop(0)
            
            # Mark as incomplete
            if current_func in self.skolem_witnesses:
                self.skolem_witnesses[current_func]['complete'] = False
            
            # Clear cached values for this function
            keys_to_remove = [key for key in self.witness_cache if key[0] == current_func]
            for key in keys_to_remove:
                del self.witness_cache[key]
            
            # Find and invalidate dependent witnesses
            for parent, children in self.witness_dependencies.items():
                if current_func in children and parent not in self.invalidation_queue:
                    self.invalidation_queue.append(parent)
            
            # Record in history
            self.witness_history.append((time.time(), current_func, "invalidated"))
    
    def get_witness_interpretation(self, func_name: str, model):
        """Get complete function interpretation from model with caching."""
        cache_key = (func_name, id(model))
        
        # Check cache first
        if cache_key in self.witness_cache:
            self.cache_hits += 1
            return self.witness_cache[cache_key]
        
        self.cache_misses += 1
        
        # Extract interpretation
        if func_name not in self.skolem_witnesses:
            return None
            
        witness_info = self.skolem_witnesses[func_name]
        domain_type, codomain_type = witness_info['type']
        
        # Find function in model
        func_decl = self._find_function_in_model(model, func_name)
        if func_decl is None:
            return None
        
        # Build complete interpretation
        interpretation = {}
        if str(domain_type).startswith('BitVec'):
            n = int(str(domain_type).split('(')[1].split(')')[0])
            for i in range(2 ** n):
                input_val = z3.BitVecVal(i, n)
                try:
                    output_val = model.evaluate(func_decl(input_val))
                    if output_val is not None:
                        interpretation[i] = (
                            output_val.as_long() if hasattr(output_val, 'as_long')
                            else output_val
                        )
                except:
                    pass
        
        # Cache the result
        if interpretation:
            self.witness_cache[cache_key] = interpretation
        
        return interpretation
    
    # Phase 2 methods: Smart caching
    
    def get_cached_witness(self, func_name: str, args: Tuple) -> Optional[Any]:
        """Get cached witness value if available."""
        cache_key = (func_name, args)
        if cache_key in self.witness_cache:
            self.cache_hits += 1
            return self.witness_cache[cache_key]
        self.cache_misses += 1
        return None
    
    def cache_witness_value(self, func_name: str, args: Tuple, value: Any):
        """Cache a witness value."""
        cache_key = (func_name, args)
        self.witness_cache[cache_key] = value
    
    def get_cache_statistics(self) -> Dict[str, Any]:
        """Get cache performance statistics."""
        total_requests = self.cache_hits + self.cache_misses
        hit_rate = self.cache_hits / total_requests if total_requests > 0 else 0
        return {
            'cache_hits': self.cache_hits,
            'cache_misses': self.cache_misses,
            'hit_rate': hit_rate,
            'cache_size': len(self.witness_cache),
            'total_witnesses': len(self.skolem_witnesses)
        }
    
    def prune_witness_history(self, max_entries: int = 1000):
        """Prune witness history to prevent unbounded growth."""
        if len(self.witness_history) > max_entries:
            self.witness_history = self.witness_history[-max_entries:]
    
    def get_witness_dependencies(self, func_name: str) -> Set[str]:
        """Get all functions that depend on the given function."""
        dependents = set()
        for parent, children in self.witness_dependencies.items():
            if func_name in children:
                dependents.add(parent)
                # Recursively add dependencies
                dependents.update(self.get_witness_dependencies(parent))
        return dependents


class IncrementalVerifier:
    """
    Unified constraint generation and truth evaluation for incremental solving.
    
    This class orchestrates the incremental verification process, managing
    the interplay between constraint generation, witness extraction, and
    truth evaluation.
    """
    
    def __init__(self, semantics, solver, witness_store, truth_cache):
        self.semantics = semantics
        self.solver = solver
        self.witness_store = witness_store
        self.truth_cache = truth_cache
        self.verification_depth = 0
        self.max_verification_depth = 10
        
    def verify_incrementally(self, sentence, eval_point):
        """
        Full incremental verification with witness tracking.
        
        This method implements the core incremental algorithm:
        1. Register witnesses for the sentence tree
        2. Generate constraints incrementally
        3. Extract witnesses as constraints are added
        4. Evaluate truth as soon as sufficient information is available
        """
        # Phase 1: Register all witnesses for sentence tree
        self._register_sentence_witnesses(sentence)
        
        # Phase 2: Build constraints incrementally
        constraint_gen = self._constraint_generator(sentence, eval_point)
        
        # Phase 3: Interleave constraint addition with witness extraction
        for constraint_batch in constraint_gen:
            self.solver.push()
            
            for constraint_info in constraint_batch:
                constraint, label = constraint_info
                self.solver.add(constraint)
            
            if self.solver.check() == z3.sat:
                model = self.solver.model()
                self.witness_store.update_witness_values(model, self.semantics)
                
                # Check if we have enough information to evaluate
                if self._can_evaluate(sentence):
                    return self._evaluate_with_witnesses(sentence, eval_point)
            else:
                # Unsatisfiable - backtrack
                self.solver.pop()
                return False
        
        # If we've exhausted constraints, do final evaluation
        return self._evaluate_with_witnesses(sentence, eval_point)
    
    def _register_sentence_witnesses(self, sentence):
        """Recursively register witnesses for a sentence tree."""
        if sentence.sentence_letter is not None:
            # Atomic sentence - no witnesses needed
            return
        
        # Register witnesses for this operator
        if hasattr(sentence.operator, 'register_witnesses'):
            # ExclusionOperator has only one argument
            if len(sentence.arguments) == 1:
                sentence.operator.register_witnesses(
                    sentence.arguments[0], self.witness_store
                )
            else:
                # For binary operators that might have register_witnesses
                sentence.operator.register_witnesses(
                    *sentence.arguments, self.witness_store
                )
        
        # Recursively register for arguments
        for arg in sentence.arguments:
            self._register_sentence_witnesses(arg)
    
    def _constraint_generator(self, sentence, eval_point):
        """
        Generate constraints in batches for incremental addition.
        
        This generator yields constraint batches based on the sentence
        structure and current witness availability.
        """
        # Start with basic structural constraints
        yield self._generate_structural_constraints(sentence, eval_point)
        
        # Generate witness-dependent constraints
        depth = 0
        while depth < self.max_verification_depth and not self._can_evaluate(sentence):
            constraints = self._generate_witness_constraints(sentence, eval_point, depth)
            if constraints:
                yield constraints
            depth += 1
    
    def _generate_structural_constraints(self, sentence, eval_point):
        """Generate basic structural constraints for a sentence."""
        constraints = []
        
        if sentence.sentence_letter is not None:
            # Atomic sentence constraint
            v = z3.BitVec(f"v_struct_{id(sentence)}", self.semantics.N)
            constraint = z3.Exists([v], z3.And(
                self.semantics.verify(v, sentence.sentence_letter),
                self.semantics.is_part_of(v, eval_point["world"])
            ))
            constraints.append((constraint, f"atomic_{sentence.sentence_letter}"))
        else:
            # Complex sentence - use operator
            constraint = sentence.operator.true_at(*sentence.arguments, eval_point)
            constraints.append((constraint, f"operator_{sentence.operator.name}"))
        
        return constraints
    
    def _generate_witness_constraints(self, sentence, eval_point, depth):
        """Generate constraints based on current witness information."""
        constraints = []
        
        # Phase 3: Enhanced witness-based constraint generation
        if sentence.sentence_letter is not None:
            # No witness constraints for atomic sentences
            return constraints
        
        # Check if operator can generate witness-specific constraints
        if hasattr(sentence.operator, 'generate_witness_constraints'):
            new_constraints = sentence.operator.generate_witness_constraints(
                *sentence.arguments, eval_point, self.witness_store, depth
            )
            for c in new_constraints:
                constraints.append((c, f"witness_depth_{depth}"))
        else:
            # For operators without specific witness constraint generation,
            # try to refine based on current witness information
            if sentence.operator.name == "\\exclude":
                # Get witness names for this exclusion instance
                h_name = f"h_sk_{id(sentence.operator)}"
                y_name = f"y_sk_{id(sentence.operator)}"
                
                if self.witness_store.has_witnesses_for([h_name, y_name]):
                    # We have complete witnesses - can generate targeted constraints
                    h_mapping = self.witness_store.get_witness_mapping(h_name)
                    y_mapping = self.witness_store.get_witness_mapping(y_name)
                    
                    # Add constraints that pin down the witness values
                    for x_val, h_val in h_mapping.items():
                        c = z3.Function(h_name, z3.BitVecSort(self.semantics.N), 
                                      z3.BitVecSort(self.semantics.N))(x_val) == h_val
                        constraints.append((c, f"witness_pin_{h_name}_{x_val}"))
                    
                    for x_val, y_val in y_mapping.items():
                        c = z3.Function(y_name, z3.BitVecSort(self.semantics.N),
                                      z3.BitVecSort(self.semantics.N))(x_val) == y_val
                        constraints.append((c, f"witness_pin_{y_name}_{x_val}"))
        
        return constraints
    
    def _can_evaluate(self, sentence):
        """Check if we have sufficient information to evaluate the sentence."""
        return self.truth_cache.has_sufficient_witnesses(sentence, self.witness_store)
    
    def _evaluate_with_witnesses(self, sentence, eval_point):
        """Evaluate sentence truth using current witness information."""
        return self.truth_cache.evaluate_incrementally(sentence, eval_point, self.witness_store)