"""
Proposition implementation for the logos theory.

This module contains LogosProposition, the proposition class with modular operator
support, representing propositional content in the logos semantic framework.
"""

from typing import Any, List, Set, TYPE_CHECKING, Tuple, Union, cast

from model_checker import z3_shim as z3

from model_checker.solver import is_true, is_false
from model_checker.models.proposition import PropositionDefaults
from model_checker.utils import ForAll, Exists, bitvec_to_substates, pretty_set_print

if TYPE_CHECKING:
    from ..protocols import EvaluationPoint, StateType, Z3Constraint
    from model_checker.syntactic import Sentence


class LogosProposition(PropositionDefaults):
    """
    Proposition class with modular operator support.

    Represents propositional content in the logos semantic framework
    with support for all subtheory operators.
    """

    def __init__(self, sentence: 'Sentence', model_structure: Any,
                 eval_world: Union[str, 'StateType'] = 'main') -> None:
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

    def proposition_constraints(self, sentence_letter: Any) -> List['Z3Constraint']:
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
            """Generate constraints that enforce classical behavior by ruling out
            truth value gaps and gluts.

            These constraints ensure:
            1. If two states verify a proposition, their fusion also verifies it
            2. If two states falsify a proposition, their fusion also falsifies it
            3. No verifier is compatible with any falsifier (no gluts)
            4. Every possible state must be compatible with either a verifier or falsifier (no gaps)
            """
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
                [x, y],
                z3.Implies(
                    z3.And(
                        semantics.verify(x, sentence_letter),
                        semantics.falsify(y, sentence_letter)
                    ),
                    z3.Not(semantics.compatible(x, y)),
                ),
            )
            no_gap = ForAll(
                x,
                z3.Implies(
                    semantics.possible(x),
                    Exists(
                        y,
                        cast(z3.BoolRef, z3.And(
                            semantics.compatible(x, y),
                            cast(z3.BoolRef, z3.Or(
                                semantics.verify(y, sentence_letter),
                                semantics.falsify(y, sentence_letter)
                            )),
                        )),
                    ),
                ),
            )
            return [
                verifier_fusion_closure,
                falsifier_fusion_closure,
                no_glut,
                no_gap
            ]

        def get_contingent_constraints():
            """The contingent constraints ensure that each atomic proposition has
            at least one possible verifier and one possible falsifier, which implicitly
            guarantees that no null states are verifiers or falsifiers."""
            x, y = z3.BitVecs("ct_cont_x ct_cont_y", semantics.N)
            possible_verifier = Exists(
                x,
                cast(z3.BoolRef, z3.And(semantics.possible(x), semantics.verify(x, sentence_letter)))
            )
            possible_falsifier = Exists(
                y,
                cast(z3.BoolRef, z3.And(semantics.possible(y), semantics.falsify(y, sentence_letter)))
            )
            return [
                possible_verifier,
                possible_falsifier,
            ]

        def get_non_null_constraints():
            """The non_null constraints prevent null states (empty states) from being verifiers
            or falsifiers. These constraints are important to prevent trivial satisfaction of
            the disjoint constraints, though they are already entailed by the contingent constraints
            when those are enabled."""
            return [
                cast(z3.BoolRef, z3.Not(semantics.verify(0, sentence_letter))),
                cast(z3.BoolRef, z3.Not(semantics.falsify(0, sentence_letter))),
            ]

        def get_disjoint_constraints():
            """Generate disjoint constraints."""
            x = z3.BitVec("dt_disj_x", semantics.N)
            return [
                ForAll(
                    [x],
                    cast(z3.BoolRef, z3.Not(cast(z3.BoolRef, z3.And(
                        semantics.verify(x, sentence_letter),
                        semantics.falsify(x, sentence_letter)
                    )))),
                )
            ]

        def get_non_empty_constraints():
            """The non_empty constraints ensure that each atomic proposition has at least one
            verifier and one falsifier. While these constraints are implied by the contingent
            constraints, they are included separately to prevent trivial satisfaction of the
            disjoint constraints when contingent constraints are not enabled."""
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

    def find_proposition(
        self,
    ) -> Tuple[Set['StateType'], Set['StateType']]:
        """Computes the verifier and falsifier sets for this proposition.

        This method determines the sets of states that verify and falsify
        the proposition in the model. For atomic propositions, it uses the
        verify and falsify relations; for complex propositions, it delegates
        to the appropriate operator's implementation.

        Returns:
            tuple: A pair (verifiers, falsifiers) containing the sets of
                 states that verify and falsify the proposition respectively
        """
        model = self.model_structure.z3_model
        if model is None:
            # If no model is available, return empty sets
            # This can happen during iteration when models are being created
            return set(), set()

        # Clean proposition computation without debug output

        semantics = self.semantics
        eval_world = self.eval_world
        operator = self.operator
        arguments = self.arguments or ()
        sentence_letter = self.sentence_letter
        if sentence_letter is not None:
            V = {
                state for state in self.model_structure.all_states
                if self._evaluate_z3_boolean(model, semantics.verify(state, sentence_letter))
            }
            F = {
                state for state in self.model_structure.all_states
                if self._evaluate_z3_boolean(model, semantics.falsify(state, sentence_letter))
            }
            return V, F
        if operator is not None:
            eval_point = {"world": eval_world}
            return operator.find_verifiers_and_falsifiers(*arguments, eval_point)

        raise ValueError(f"There is no proposition for {self}.")

    def _evaluate_z3_boolean(self, z3_model: z3.ModelRef, expression: z3.BoolRef) -> bool:
        """Safely evaluate a Z3 boolean expression to a Python boolean.

        This method handles the case where Z3 returns symbolic expressions
        instead of concrete boolean values.

        Args:
            z3_model: The Z3 model to use for evaluation
            expression: The Z3 boolean expression to evaluate

        Returns:
            bool: True if the expression evaluates to true, False otherwise
        """

        try:
            # Evaluate the expression with model completion
            result = z3_model.evaluate(expression, model_completion=True)

            # Check if result is a boolean constant
            if is_true(result):
                return True
            elif is_false(result):
                return False

            # Try to simplify
            simplified = z3.simplify(result)
            if is_true(simplified):
                return True
            elif is_false(simplified):
                return False

            # Check string representation as last resort
            if str(simplified) == "True":
                return True
            elif str(simplified) == "False":
                return False

            # Conservative default
            return False

        except Exception:
            return False

    def truth_value_at(self, eval_world: 'StateType') -> bool:
        """Determines the truth value of the proposition at a given world.

        Checks if the world contains a verifier for the proposition (making it true)
        or a falsifier (making it false). Also checks for potential inconsistencies
        where a world contains both a verifier and falsifier, which should not occur
        in a well-formed model.

        Args:
            eval_world (BitVecRef): The world at which to evaluate the proposition

        Returns:
            bool: True if the world contains a verifier, False if it contains a falsifier

        Note:
            Prints a warning if an inconsistency is detected where a world contains
            both a verifier and falsifier for the same proposition.
        """
        semantics = self.model_structure.model_constraints.semantics
        z3_model = self.model_structure.z3_model
        ver_witness = None
        fal_witness = None
        exists_verifier = False
        exists_falsifier = False
        for verifier in self.verifiers:
            if z3_model.eval(semantics.is_part_of(verifier, eval_world), model_completion=True):
                ver_witness = verifier
                exists_verifier = True
                break
        for falsifier in self.falsifiers:
            if z3_model.eval(semantics.is_part_of(falsifier, eval_world), model_completion=True):
                fal_witness = falsifier
                exists_falsifier = True
                break
        if exists_verifier == exists_falsifier:
            print( # NOTE: a warning is preferable to raising an error
                f"WARNING: the world {bitvec_to_substates(eval_world, self.N)} contains both:\n "
                f"  The verifier {bitvec_to_substates(ver_witness, self.N)}; and"
                f"  The falsifier {bitvec_to_substates(fal_witness, self.N)}."
            )
        return exists_verifier

    def print_proposition(self, eval_point: 'EvaluationPoint',
                         indent_num: int, use_colors: bool) -> None:
        """Print the proposition with its truth value at the given evaluation point.

        Prints the proposition name, its verifiers and falsifiers, and its truth value
        at the specified evaluation world. The output is formatted with optional
        indentation and color coding.

        Args:
            eval_point (dict): Dictionary containing evaluation context, including the 'world' key
            indent_num (int): Number of indentation levels to use
            use_colors (bool): Whether to use ANSI color codes in the output

        Returns:
            None
        """
        N = self.model_structure.model_constraints.semantics.N
        eval_world = eval_point["world"]
        truth_value = self.truth_value_at(eval_world)
        world_state = bitvec_to_substates(eval_world, N)
        RESET, FULL, PART = self.set_colors(self.name, indent_num, truth_value, world_state, use_colors)
        print(
            f"{'  ' * indent_num}{FULL}|{self.name}| = {self}{RESET}"
            f"  {PART}({truth_value} in {world_state}){RESET}"
        )

    def __repr__(self) -> str:
        """Return a string representation of the proposition.

        Returns a string showing the verifiers and falsifiers of the proposition
        in set notation. Only includes possible states unless print_impossible
        setting is enabled.

        Returns:
            str: A string of the form "< {verifiers}, {falsifiers} >" where each
                set contains the binary representations of the states
        """
        # Guard against missing verifiers/falsifiers attribute (e.g., during error handling)
        if not hasattr(self, 'verifiers') or not hasattr(self, 'falsifiers'):
            sentence_name = getattr(self, 'sentence', None)
            if sentence_name is not None:
                sentence_name = getattr(sentence_name, 'name', str(sentence_name))
            return f"<LogosProposition: {sentence_name} (uninitialized)>"

        N = self.model_structure.model_constraints.semantics.N
        possible = self.model_structure.model_constraints.semantics.possible
        z3_model = self.model_structure.z3_model
        ver_states = {
            bitvec_to_substates(bit, N)
            for bit in self.verifiers
            if z3_model.evaluate(possible(bit)) or self.settings['print_impossible']
        }
        fal_states = {
            bitvec_to_substates(bit, N)
            for bit in self.falsifiers
            if z3_model.evaluate(possible(bit)) or self.settings['print_impossible']
        }
        return f"< {pretty_set_print(ver_states)}, {pretty_set_print(fal_states)} >"
