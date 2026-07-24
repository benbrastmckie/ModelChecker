"""
Witness predicate proposition implementation.

This module contains WitnessProposition, the proposition class for witness predicate
semantics -- moved here from semantic/__init__.py so that __init__.py can be re-export-only
per docs/THEORY_ARCHITECTURE.md's Theory Contract.
"""

from model_checker.solver import is_true
from model_checker.models.proposition import PropositionDefaults
from model_checker.utils import bitvec_to_substates, pretty_set_print


class WitnessProposition(PropositionDefaults):
    """Proposition class for witness predicate semantics."""

    def __init__(self, sentence, model_structure):
        super().__init__(sentence, model_structure)
        self.z3_model = model_structure.z3_model
        self.verifiers = self.find_proposition()

    def proposition_constraints(model_constraints, sentence_letter):
        """Generate constraints for atomic propositions.

        This is called as a class method (without an instance) from ModelConstraints.
        The first argument is the ModelConstraints instance, not self.

        Args:
            model_constraints: The ModelConstraints instance containing semantics and settings
            sentence_letter: The atomic sentence letter to generate constraints for

        Returns:
            list: List of Z3 constraints for the sentence letter
        """
        return model_constraints.semantics.atom_constraints(
            sentence_letter,
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
            # Use the model structure's _evaluate_z3_boolean method if available
            if hasattr(self.model_structure, '_evaluate_z3_boolean'):
                if self.model_structure._evaluate_z3_boolean(self.z3_model, constraint):
                    result.add(state)
            else:
                if is_true(self.z3_model.evaluate(constraint)):
                    result.add(state)
        return result

    def truth_value_at(self, eval_point):
        """Evaluate truth value at a point."""
        return self.model_structure.semantics.true_at(self.sentence, eval_point)

    def print_method(self, eval_point, indent_num, use_colors):
        """Print the proposition."""
        self.print_proposition(eval_point, indent_num, use_colors)

    def __repr__(self):
        """Return pretty-printed representation of verifiers."""

        N = self.model_structure.semantics.N
        possible = self.model_structure.semantics.possible
        z3_model = self.model_structure.z3_model
        # Use the model structure's _evaluate_z3_boolean method if available
        if hasattr(self.model_structure, '_evaluate_z3_boolean'):
            ver_states = {
                bitvec_to_substates(bit, N)
                for bit in self.verifiers
                if self.model_structure._evaluate_z3_boolean(z3_model, possible(bit)) or self.settings.get('print_impossible', False)
            }
        else:
            ver_states = {
                bitvec_to_substates(bit, N)
                for bit in self.verifiers
                if is_true(z3_model.evaluate(possible(bit))) or self.settings.get('print_impossible', False)
            }
        return pretty_set_print(ver_states)

    def print_proposition(self, eval_point, indent_num, use_colors):
        """Print the proposition with its truth value at the evaluation point."""

        N = self.model_structure.semantics.N
        z3_formula = self.truth_value_at(eval_point)
        # Use the model structure's _evaluate_z3_boolean method if available
        if hasattr(self.model_structure, '_evaluate_z3_boolean'):
            truth_value = self.model_structure._evaluate_z3_boolean(self.model_structure.z3_model, z3_formula)
        else:
            truth_value = is_true(self.model_structure.z3_model.evaluate(z3_formula))
        world_state = bitvec_to_substates(eval_point["world"], N)
        RESET, FULL, PART = self.set_colors(self.name, indent_num, truth_value, world_state, use_colors)
        print(
            f"{'  ' * indent_num}{FULL}|{self.name}| = {self}{RESET}"
            f"  {PART}({truth_value} in {world_state}){RESET}"
        )
