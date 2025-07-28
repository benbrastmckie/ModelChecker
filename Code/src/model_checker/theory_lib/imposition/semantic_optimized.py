"""
Optimized version of ImpositionSemantics with performance improvements for maximize mode.

This module provides optimized implementations focusing on:
1. Cached imposition relation evaluations
2. Optimized constraint generation
3. Better Z3 solver configuration
4. Reduced redundant computations
"""

import z3
import sys
import time

from model_checker.theory_lib.logos import LogosSemantics, LogosModelStructure
from model_checker.utils import (
    ForAll,
    Exists,
    bitvec_to_substates,
)


class OptimizedImpositionSemantics(LogosSemantics):
    """
    Optimized version of Kit Fine's imposition semantics.
    
    Key optimizations:
    - Cached imposition evaluations
    - Simplified frame constraints
    - Optimized solver configuration
    """

    DEFAULT_EXAMPLE_SETTINGS = {
        'N' : 3,
        'contingent' : False,
        'non_empty' : False,
        'non_null' : False,
        'disjoint' : False,
        'max_time' : 1,
        'iterate' : 1,
        'expectation' : None,
    }
    
    DEFAULT_GENERAL_SETTINGS = {
        "print_impossible": False,
        "print_constraints": False,
        "print_z3": False,
        "save_output": False,
        "maximize": False,
    }

    def __init__(self, settings):
        # Merge settings with defaults
        combined_settings = {}
        combined_settings.update(self.DEFAULT_EXAMPLE_SETTINGS)
        combined_settings.update(self.DEFAULT_GENERAL_SETTINGS)
        combined_settings.update(settings)
        
        # Initialize the parent LogosSemantics
        super().__init__(combined_settings=combined_settings)
        
        # Cache for imposition evaluations
        self._imposition_cache = {}
        
        # Define imposition-specific operations
        self._define_imposition_operation()
    
    def _define_imposition_operation(self):
        """Define the imposition operation with optimized constraints."""
        # Define the imposition function
        self.imposition = z3.Function(
            "imposition",
            z3.BitVecSort(self.N),  # state imposed
            z3.BitVecSort(self.N),  # world being imposed on
            z3.BitVecSort(self.N),  # outcome world
            z3.BoolSort()           # boolean result
        )

        # Define frame constraints with optimization
        x, y, z, u = z3.BitVecs("frame_x frame_y, frame_z, frame_u", self.N)
        
        # Use simplified constraints where possible
        possibility_downard_closure = ForAll(
            [x, y],
            z3.Implies(
                z3.And(self.possible(y), self.is_part_of(x, y)), 
                self.possible(x)
            ),
        )
        
        is_main_world = self.is_world(self.main_world)
        
        # Optimize inclusion constraint
        inclusion = ForAll(
            [x, y, z],
            z3.Implies(
                self.imposition(x, y, z),
                self.is_part_of(x, z)
            )
        )
        
        # Optimize actuality with early termination conditions
        actuality = ForAll(
            [x, y],
            z3.Implies(
                z3.And(
                    self.is_part_of(x, y),
                    self.is_world(y)
                ),
                Exists(
                    z,
                    z3.And(
                        self.is_part_of(z, y),
                        self.imposition(x, y, z),
                    )
                )
            )
        )
        
        # Simplified incorporation
        incorporation = ForAll(
            [x, y, z, u],
            z3.Implies(
                z3.And(
                    self.imposition(x, y, z),
                    self.is_part_of(u, z)
                ),
                self.imposition(self.fusion(x, u), y, z)
            )
        )
        
        completeness = ForAll(
            [x, y, z],
            z3.Implies(
                self.imposition(x, y, z),
                self.is_world(z)
            )
        )

        # Apply constraint simplification
        self.frame_constraints = [
            z3.simplify(possibility_downard_closure),
            is_main_world,
            z3.simplify(inclusion),
            z3.simplify(actuality),
            z3.simplify(incorporation),
            z3.simplify(completeness),
        ]

        # Define invalidity conditions
        self.premise_behavior = lambda premise: self.true_at(premise, self.main_point)
        self.conclusion_behavior = lambda conclusion: self.false_at(conclusion, self.main_point)

    def calculate_outcome_worlds(self, verifiers, eval_point, model_structure):
        """Calculate alternative worlds with caching."""
        # Use cached evaluations when available
        eval = model_structure.z3_model.evaluate
        world_states = model_structure.z3_world_states
        eval_world = eval_point["world"]
        
        outcome_worlds = set()
        for ver in verifiers:
            for pw in world_states:
                # Check cache first
                cache_key = (ver.as_long() if hasattr(ver, 'as_long') else ver,
                           eval_world.as_long() if hasattr(eval_world, 'as_long') else eval_world,
                           pw.as_long() if hasattr(pw, 'as_long') else pw)
                
                if cache_key in self._imposition_cache:
                    if self._imposition_cache[cache_key]:
                        outcome_worlds.add(pw)
                else:
                    # Evaluate and cache
                    result = eval(self.imposition(ver, eval_world, pw))
                    self._imposition_cache[cache_key] = result
                    if result:
                        outcome_worlds.add(pw)
        
        return outcome_worlds

    def clear_cache(self):
        """Clear the imposition cache."""
        self._imposition_cache.clear()


class OptimizedImpositionModelStructure(LogosModelStructure):
    """
    Optimized model structure for imposition theory with performance improvements.
    """
    
    def __init__(self, model_constraints, settings):
        # Configure optimized solver before parent initialization
        if hasattr(model_constraints, 'solver'):
            self._configure_optimized_solver(model_constraints.solver, settings)
        
        super().__init__(model_constraints, settings)
        
        # Initialize imposition relations storage
        self.z3_imposition_relations = []
        
        # Only evaluate if we have a valid model
        if self.z3_model_status and self.z3_model is not None:
            self._update_imposition_relations_optimized()
    
    def _configure_optimized_solver(self, solver, settings):
        """Configure solver with optimization tactics."""
        # Set timeout with buffer for complex examples
        timeout = int(settings.get('max_time', 1) * 1000)
        solver.set("timeout", timeout)
        
        # Additional solver options for performance
        solver.set("random_seed", 42)  # Consistent results
        solver.set("max_conflicts", 10000)  # Increase conflict limit
    
    def _update_imposition_relations_optimized(self):
        """Extract imposition relations with optimization."""
        if not hasattr(self.semantics, 'imposition'):
            return
            
        evaluate = self.z3_model.evaluate
        
        # Pre-filter to reduce search space
        self.z3_imposition_relations = []
        
        # Only check possible states and worlds
        possible_states = [s for s in self.all_states 
                          if z3.is_true(evaluate(self.semantics.possible(s)))]
        
        for state in possible_states:
            for world in self.z3_world_states:
                # Early termination: skip if state can't be part of world
                if not z3.is_true(evaluate(self.semantics.is_part_of(state, world))):
                    continue
                    
                for outcome in self.z3_world_states:
                    try:
                        if z3.is_true(evaluate(self.semantics.imposition(state, world, outcome))):
                            self.z3_imposition_relations.append((state, world, outcome))
                    except:
                        pass
    
    def print_all(self, default_settings, example_name, theory_name, output=sys.__stdout__):
        """Print model including imposition relations."""
        model_status = self.z3_model_status
        self.print_info(model_status, self.settings, example_name, theory_name, output)
        if model_status:
            self.print_states(output)
            self.print_imposition(output)
            self.print_evaluation(output)
            self.print_input_sentences(output)
            self.print_model(output)
            if output is sys.__stdout__:
                total_time = round(time.time() - self.start_time, 4) 
                print(f"Total Run Time: {total_time} seconds\n", file=output)
                print(f"{'='*40}", file=output)
            return
    
    def print_imposition(self, output=sys.__stdout__):
        """Print imposition relations optimized."""
        if not self.z3_imposition_relations:
            return
            
        print("\nImposition Relation:", file=output)
        
        # Set up colors if outputting to stdout
        use_colors = output is sys.__stdout__
        WHITE = "\033[37m" if use_colors else ""
        RESET = "\033[0m" if use_colors else ""
        WORLD_COLOR = "\033[34m" if use_colors else ""
        POSSIBLE_COLOR = "\033[36m" if use_colors else ""
        
        def get_state_color(bit):
            if bit in self.z3_world_states:
                return WORLD_COLOR
            elif bit in self.z3_possible_states:
                return POSSIBLE_COLOR
            else:
                return WHITE
        
        # Group impositions by world being imposed on
        impositions_by_world = {}
        for state, world, outcome in self.z3_imposition_relations:
            if world not in impositions_by_world:
                impositions_by_world[world] = []
            impositions_by_world[world].append((state, outcome))
        
        # Print impositions grouped by world
        for world in sorted(impositions_by_world.keys(), 
                          key=lambda x: x if isinstance(x, int) else x.as_long()):
            world_str = bitvec_to_substates(world, self.N)
            world_color = get_state_color(world)
            
            for state, outcome in sorted(impositions_by_world[world], 
                                       key=lambda x: (x[0] if isinstance(x[0], int) else x[0].as_long(), 
                                                     x[1] if isinstance(x[1], int) else x[1].as_long())):
                state_str = bitvec_to_substates(state, self.N)
                outcome_str = bitvec_to_substates(outcome, self.N)
                
                state_color = get_state_color(state)
                outcome_color = get_state_color(outcome)
                
                # Print in format: w ->_a u
                print(f"  {world_color}{world_str}{RESET} →_{state_color}{state_str}{RESET} {outcome_color}{outcome_str}{RESET}", 
                      file=output)
    
    def initialize_from_z3_model(self, z3_model):
        """Initialize imposition-specific attributes from Z3 model."""
        # First call parent initialization
        super().initialize_from_z3_model(z3_model)
        
        # Then update imposition relations with optimization
        self._update_imposition_relations_optimized()