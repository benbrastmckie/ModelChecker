"""
Shared semantic framework for the logos theory.

This module implements the core semantic foundation for all logos subtheories,
providing unified classes for semantics, propositions, and model structures.
"""

import z3
import sys
import time

from model_checker.model import (
    PropositionDefaults,
    SemanticDefaults,
    ModelDefaults,
    ModelConstraints,
)
from model_checker.utils import (
    ForAll,
    Exists,
    bitvec_to_substates,
    pretty_set_print,
    int_to_binary,
)
from model_checker import syntactic


class LogosSemantics(SemanticDefaults):
    """
    Shared semantic framework for all logos subtheories.
    
    This class provides the foundation for hyperintensional truthmaker semantics
    with support for modular operator loading and subtheory coordination.
    """
    
    DEFAULT_EXAMPLE_SETTINGS = {
        'N': 16,
        'contingent': True,
        'non_empty': True,
        'non_null': True,
        'disjoint': True,
        'max_time': 10000,
        'iterate': False,
        'iteration_timeout': 1.0,
        'iteration_attempts': 5,
        'expectation': None,
    }
    
    def __init__(self, combined_settings=None, operator_registry=None, **kwargs):
        # Ensure we have default settings
        if combined_settings is None:
            combined_settings = self.DEFAULT_EXAMPLE_SETTINGS.copy()
            combined_settings.update(kwargs)
        
        super().__init__(combined_settings)
        self.operator_registry = operator_registry
        
        # Define the Z3 primitives following default theory pattern
        self.verify = z3.Function("verify", z3.BitVecSort(self.N), syntactic.AtomSort, z3.BoolSort())
        self.falsify = z3.Function("falsify", z3.BitVecSort(self.N), syntactic.AtomSort, z3.BoolSort())
        self.possible = z3.Function("possible", z3.BitVecSort(self.N), z3.BoolSort())
        self.main_world = z3.BitVec("w", self.N)
        self.main_point = {
            "world": self.main_world
        }

        # Define the frame constraints
        x, y = z3.BitVecs("frame_x frame_y", self.N)
        possibility_downward_closure = ForAll(
            [x, y],
            z3.Implies(
                z3.And(
                    self.possible(y),
                    self.is_part_of(x, y)
                ),
                self.possible(x)
            ),
        )

        # Set frame constraints
        self.frame_constraints = [
            possibility_downward_closure,
            self.is_world(self.main_world),
        ]

        # Define invalidity conditions
        self.premise_behavior = lambda premise: self.true_at(premise, self.main_point["world"])
        self.conclusion_behavior = lambda conclusion: self.false_at(conclusion, self.main_point["world"])
    
    def load_subtheories(self, subtheories=None):
        """Load specified subtheories."""
        if subtheories is None:
            subtheories = ['extensional', 'modal', 'constitutive', 'counterfactual']
        if self.operator_registry:
            return self.operator_registry.load_subtheories(subtheories)
        return []

    def compatible(self, state_x, state_y):
        """Determines if the fusion of two states is possible."""
        return self.possible(self.fusion(state_x, state_y))

    def maximal(self, state_w):
        """Determines if a state is maximal with respect to compatibility."""
        x = z3.BitVec("max_x", self.N)
        return ForAll(
            x,
            z3.Implies(
                z3.And(
                    self.possible(x),
                    self.compatible(state_w, x)
                ),
                self.is_part_of(x, state_w),
            ),
        )

    def is_world(self, state_w):
        """Determines if a state represents a possible world in the model."""
        return z3.And(
            self.possible(state_w),
            self.maximal(state_w),
        )


class LogosProposition(PropositionDefaults):
    """
    Proposition class with modular operator support.
    
    Represents propositional content in the logos semantic framework
    with support for all subtheory operators.
    """
    
    def __init__(self, sentence, model_structure, eval_world='main'):
        """Initialize a LogosProposition instance.

        Args:
            sentence (Sentence): The sentence whose proposition is being represented
            model_structure (ModelStructure): The model structure containing semantic definitions
            eval_world (str|BitVecRef, optional): The world at which to evaluate the proposition.
                If 'main', uses the model's main world. Defaults to 'main'.
        """
        super().__init__(sentence, model_structure)
        self.eval_world = model_structure.main_point["world"] if eval_world == 'main' else eval_world
        self.verifiers, self.falsifiers = self.find_proposition()
    
    def proposition_constraints(self, sentence_letter):
        """Generates Z3 constraints for a sentence letter based on semantic settings.

        This method generates constraints that govern the behavior of atomic propositions
        in the model following the default theory pattern.
        
        Args:
            sentence_letter: The atomic sentence letter to generate constraints for
            
        Returns:
            list: List of Z3 constraints for the sentence letter
        """
        semantics = self.semantics
        
        def get_classical_constraints():
            """Generate classical constraints following default theory pattern."""
            x, y = z3.BitVecs("cl_prop_x cl_prop_y", semantics.N)
            
            verifier_fusion_closure = ForAll(
                [x, y],
                z3.Implies(
                    z3.And(
                        semantics.verify(x, sentence_letter),
                        semantics.verify(y, sentence_letter)
                    ),
                    semantics.verify(semantics.fusion(x, y), sentence_letter),
                ),
            )
            falsifier_fusion_closure = ForAll(
                [x, y],
                z3.Implies(
                    z3.And(
                        semantics.falsify(x, sentence_letter),
                        semantics.falsify(y, sentence_letter)
                    ),
                    semantics.falsify(semantics.fusion(x, y), sentence_letter),
                ),
            )
            no_glut = ForAll(
                [x],
                z3.Not(z3.And(
                    semantics.verify(x, sentence_letter),
                    semantics.falsify(x, sentence_letter)
                )),
            )
            no_gap = ForAll(
                [x],
                z3.Implies(
                    semantics.possible(x),
                    z3.Or(
                        Exists(
                            [y],
                            z3.And(
                                semantics.verify(y, sentence_letter),
                                semantics.compatible(x, y)
                            ),
                        ),
                        Exists(
                            [y],
                            z3.And(
                                semantics.falsify(y, sentence_letter),
                                semantics.compatible(x, y)
                            ),
                        ),
                    ),
                ),
            )
            return [verifier_fusion_closure, falsifier_fusion_closure, no_glut, no_gap]

        def get_contingent_constraints():
            """Generate contingency constraints."""
            x, y = z3.BitVecs("ct_cont_x ct_cont_y", semantics.N)
            return [
                z3.Exists(
                    [x, y],
                    z3.And(
                        semantics.verify(x, sentence_letter),
                        semantics.falsify(y, sentence_letter)
                    )
                )
            ]

        def get_non_null_constraints():
            """Generate non-null constraints."""
            return [
                z3.Not(semantics.verify(semantics.null_state, sentence_letter)),
                z3.Not(semantics.falsify(semantics.null_state, sentence_letter))
            ]

        def get_disjoint_constraints():
            """Generate disjoint constraints."""
            x = z3.BitVec("dt_disj_x", semantics.N)
            return [
                ForAll(
                    [x],
                    z3.Not(z3.And(
                        semantics.verify(x, sentence_letter),
                        semantics.falsify(x, sentence_letter)
                    )),
                )
            ]

        def get_non_empty_constraints():
            """Generate non-empty constraints."""
            x, y = z3.BitVecs("ct_empty_x ct_empty_y", semantics.N)
            return [
                z3.Exists(
                    [x, y],
                    z3.And(
                        semantics.verify(x, sentence_letter),
                        semantics.falsify(y, sentence_letter)
                    )
                )
            ]

        # Generate constraints following default theory pattern
        constraints = get_classical_constraints()
        if self.settings['contingent']:
            constraints.extend(get_contingent_constraints())
        if self.settings['non_empty'] and not self.settings['contingent']:
            constraints.extend(get_non_empty_constraints())
        if self.settings['disjoint']:
            constraints.extend(get_disjoint_constraints())
            constraints.extend(get_non_null_constraints())
        if self.settings['non_null'] and not self.settings['disjoint']:
            constraints.extend(get_non_null_constraints())
        return constraints


class LogosModelStructure(ModelDefaults):
    """
    Model structure with modular operator support.
    
    Manages the overall semantic model structure for the logos theory
    with support for all subtheories and modular operator loading.
    """
    
    def __init__(self, semantics, proposition_class=None):
        super().__init__(semantics, proposition_class or LogosProposition)
        self.loaded_subtheories = []
    
    def load_subtheories(self, subtheories):
        """Load specified subtheories into the model."""
        self.loaded_subtheories.extend(subtheories)
        if hasattr(self.semantics, 'load_subtheories'):
            self.semantics.load_subtheories(subtheories)
    
    def get_available_operators(self):
        """Get all operators from loaded subtheories."""
        if hasattr(self.semantics, 'operator_registry'):
            return self.semantics.operator_registry.get_operators()
        return {}
    
    def print_model_info(self):
        """Print information about the loaded model."""
        print(f"Logos Theory Model")
        print(f"Loaded subtheories: {', '.join(self.loaded_subtheories)}")
        
        operators = self.get_available_operators()
        if operators:
            print(f"Available operators: {len(operators)}")
            for name, op in operators.items():
                print(f"  - {name}: {op.__class__.__name__}")
        else:
            print("No operators loaded")