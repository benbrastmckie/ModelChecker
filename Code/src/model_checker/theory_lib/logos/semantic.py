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
        'contingent': True,
        'disjoint': True,
        'non_empty': True,
        'non_null': True,
        'N': 16,
        'max_time': 10000,
        'target': 'truth',
        'iterate': False,
    }
    
    def __init__(self, operator_registry=None, **kwargs):
        super().__init__(**kwargs)
        self.operator_registry = operator_registry
    
    def load_subtheories(self, subtheories=None):
        """Load specified subtheories."""
        if subtheories is None:
            subtheories = ['extensional', 'modal', 'constitutive', 'counterfactual', 'relevance']
        if self.operator_registry:
            return self.operator_registry.load_subtheories(subtheories)
        return []
    
    def compatible(self, state1, state2):
        """Two states are compatible if their fusion is defined (no overlap)."""
        return (state1 & state2) == 0
    
    def maximal(self, state):
        """A state is maximal if it cannot be extended without becoming impossible."""
        return z3.ForAll(
            self.state_var('s'),
            z3.Implies(
                z3.And(
                    self.possible(self.state_var('s')),
                    self.compatible(state, self.state_var('s'))
                ),
                self.state_var('s') == 0
            )
        )
    
    def is_world(self, state):
        """A world is a maximal possible state."""
        return z3.And(
            self.possible(state),
            self.maximal(state)
        )
    
    def max_compatible_part(self, state, states):
        """Get the maximal part of state that is compatible with all states."""
        if not states:
            return state
        return z3.BVOr(*[state & ~s for s in states])
    
    def is_alternative(self, world1, world2, antecedent_state):
        """Determine if world2 is an alternative to world1 given antecedent."""
        return z3.And(
            self.is_world(world1),
            self.is_world(world2),
            (antecedent_state & world2) != 0
        )
    
    def true_at(self, sentence, world):
        """Truth conditions for sentences at possible worlds."""
        if hasattr(sentence, 'operator'):
            return sentence.operator.true_at(sentence, world, self)
        else:
            # Atomic proposition
            return z3.ForAll(
                self.state_var('s'),
                z3.Implies(
                    z3.And(
                        self.verify(self.state_var('s'), sentence),
                        (self.state_var('s') & world) != 0
                    ),
                    True
                )
            )
    
    def false_at(self, sentence, world):
        """Falsity conditions for sentences at possible worlds."""
        if hasattr(sentence, 'operator'):
            return sentence.operator.false_at(sentence, world, self)
        else:
            # Atomic proposition
            return z3.ForAll(
                self.state_var('s'),
                z3.Implies(
                    z3.And(
                        self.falsify(self.state_var('s'), sentence),
                        (self.state_var('s') & world) != 0
                    ),
                    True
                )
            )
    
    def extended_verify(self, state, sentence):
        """Extended verification relation for complex formulas."""
        if hasattr(sentence, 'operator'):
            return sentence.operator.extended_verify(sentence, state, self)
        else:
            return self.verify(state, sentence)
    
    def extended_falsify(self, state, sentence):
        """Extended falsification relation for complex formulas."""
        if hasattr(sentence, 'operator'):
            return sentence.operator.extended_falsify(sentence, state, self)
        else:
            return self.falsify(state, sentence)
    
    def calculate_alternative_worlds(self, antecedent, world):
        """Calculate alternative worlds for counterfactual evaluation."""
        # This is specific to counterfactual semantics
        antecedent_states = [
            self.state_var(f'ant_state_{i}') 
            for i in range(8)  # Limit for efficiency
        ]
        
        alternative_worlds = []
        for i, ant_state in enumerate(antecedent_states):
            alt_world = self.state_var(f'alt_world_{i}')
            alternative_worlds.append(alt_world)
        
        return alternative_worlds
    
    def calculate_outcome_worlds(self, alternative_worlds, consequent):
        """Calculate outcome worlds from alternative worlds."""
        outcome_worlds = []
        for i, alt_world in enumerate(alternative_worlds):
            out_world = self.state_var(f'out_world_{i}')
            outcome_worlds.append(out_world)
        
        return outcome_worlds


class LogosProposition(PropositionDefaults):
    """
    Proposition class with modular operator support.
    
    Represents propositional content in the logos semantic framework
    with support for all subtheory operators.
    """
    
    def __init__(self, semantics, operators=None):
        super().__init__(semantics)
        self.operators = operators or {}
    
    def proposition_constraints(self, premise_sentences, conclusion_sentences, settings):
        """Generate semantic constraints for the proposition."""
        constraints = []
        
        # Basic proposition constraints
        for sentence in premise_sentences + conclusion_sentences:
            if not hasattr(sentence, 'operator'):
                # Atomic proposition constraints
                atom_constraints = self.atom_constraints(sentence, settings)
                constraints.extend(atom_constraints)
        
        return constraints
    
    def atom_constraints(self, atom, settings):
        """Generate constraints for atomic propositions."""
        constraints = []
        
        # Contingency: atom is neither necessary nor impossible
        if settings.get('contingent', False):
            constraints.append(self.contingency_constraint(atom))
        
        # Disjointness: verifiers and falsifiers are disjoint
        if settings.get('disjoint', False):
            constraints.append(self.disjointness_constraint(atom))
        
        # Non-emptiness: atom has some verifiers
        if settings.get('non_empty', False):
            constraints.append(self.non_empty_constraint(atom))
        
        # Non-nullity: atom has some falsifiers
        if settings.get('non_null', False):
            constraints.append(self.non_null_constraint(atom))
        
        return constraints
    
    def contingency_constraint(self, atom):
        """Atom is contingent (neither necessary nor impossible)."""
        return z3.And(
            z3.Exists(
                self.semantics.state_var('w'),
                z3.And(
                    self.semantics.is_world(self.semantics.state_var('w')),
                    self.semantics.true_at(atom, self.semantics.state_var('w'))
                )
            ),
            z3.Exists(
                self.semantics.state_var('w'),
                z3.And(
                    self.semantics.is_world(self.semantics.state_var('w')),
                    z3.Not(self.semantics.true_at(atom, self.semantics.state_var('w')))
                )
            )
        )
    
    def disjointness_constraint(self, atom):
        """Verifiers and falsifiers are disjoint."""
        return z3.ForAll(
            self.semantics.state_var('s'),
            z3.Not(z3.And(
                self.semantics.verify(self.semantics.state_var('s'), atom),
                self.semantics.falsify(self.semantics.state_var('s'), atom)
            ))
        )
    
    def non_empty_constraint(self, atom):
        """Atom has some verifiers."""
        return z3.Exists(
            self.semantics.state_var('s'),
            z3.And(
                self.semantics.possible(self.semantics.state_var('s')),
                self.semantics.verify(self.semantics.state_var('s'), atom)
            )
        )
    
    def non_null_constraint(self, atom):
        """Atom has some falsifiers."""
        return z3.Exists(
            self.semantics.state_var('s'),
            z3.And(
                self.semantics.possible(self.semantics.state_var('s')),
                self.semantics.falsify(self.semantics.state_var('s'), atom)
            )
        )


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