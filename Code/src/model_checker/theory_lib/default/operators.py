"""Implements the default operators for the model checker's logical language.

This module provides implementations of various logical operators used in the model checker,
including both primitive and defined operators. The operators are organized into several
categories based on their semantic role:

Extensional Operators:
    - NegationOperator (¬): Logical negation
    - AndOperator (∧): Logical conjunction 
    - OrOperator (∨): Logical disjunction
    - ConditionalOperator (→): Material implication (defined)
    - BiconditionalOperator (↔): Material biconditional (defined)

Extremal Operators:
    - TopOperator (⊤): Logical tautology/truth
    - BotOperator (⊥): Logical contradiction/falsity

Constitutive Operators:
    - IdentityOperator (≡): Content identity between propositions
    - GroundOperator (≤): Grounding/entailment relation
    - EssenceOperator (⊑): Essence relation between propositions
    - RelevanceOperator (≼): Content relevance between propositions

Counterfactual Operators:
    - CounterfactualOperator (□→): Counterfactual conditional
    - ImpositionOperator (\\imposition): Kit Fine's imposition semantics
    - MightCounterfactualOperator (◇→): Might counterfactual (defined)
    - MightImpositionOperator (\\could): Might imposition (defined)

Intensional Operators:
    - NecessityOperator (□): Modal necessity
    - PossibilityOperator (◇): Modal possibility (defined)

Each operator implements appropriate semantic conditions for:
- Truth and falsity at evaluation points
- Extended verification and falsification conditions
- Finding verifiers and falsifiers
- Pretty printing

The semantics combines:
- Classical truth conditions
- Exact/truthmaker semantics with verifiers and falsifiers
- Possible worlds semantics for modal and counterfactual operators

The module exports a default collection of all operators via default_operators.

Dependencies:
    - z3: For logical expressions and constraint solving
    - model_checker.utils: Core utilities like ForAll, Exists
    - model_checker.syntactic: Base operator classes and collections
"""

import z3

# Try local imports first (for development)
try:
    from src.model_checker.utils import (
        ForAll,
        Exists,
    )
    from src.model_checker import syntactic
except ImportError:
    # Fall back to installed package imports
    from model_checker.utils import (
        ForAll,
        Exists,
    )
    from model_checker import syntactic



##############################################################################
############################ EXTENSIONAL OPERATORS ###########################
##############################################################################

class NegationOperator(syntactic.Operator):
    """Implementation of logical negation (¬).
    
    This operator implements both intensional truth/falsity conditions and
    hyperintensional verifier/falsifier semantics for logical negation. 
    It flips the truth value of its argument: if A is true, ¬A is false, 
    and if A is false, ¬A is true.
    
    In the hyperintensional semantics, the verifiers of ¬A are the falsifiers of A,
    and the falsifiers of ¬A are the verifiers of A.
    
    Class Attributes:
        name (str): Symbol representing negation ("\\neg")
        arity (int): Number of arguments (1)
    """

    name = "\\neg"
    arity = 1

    def true_at(self, argument, eval_point):
        """Defines truth conditions for negation at an evaluation point.
        
        A negation ¬A is true at an evaluation point if and only if
        A is false at that evaluation point.
        
        Args:
            argument (Sentence): The sentence being negated
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the truth condition
        """
        return self.semantics.false_at(argument, eval_point)

    def false_at(self, argument, eval_point):
        """Defines falsity conditions for negation at an evaluation point.
        
        A negation ¬A is false at an evaluation point if and only if
        A is true at that evaluation point.
        
        Args:
            argument (Sentence): The sentence being negated
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the falsity condition
        """
        return self.semantics.true_at(argument, eval_point)

    def extended_verify(self, state, arg, eval_point):
        """Defines verification conditions for negation in the extended semantics.
        
        In the extended semantics, a state verifies ¬A if and only if it falsifies A.
        This implements the hyperintensional semantics where the verifiers of a negation
        are the falsifiers of its argument.
        
        Args:
            state (BitVecRef): The state being evaluated as a verifier
            arg (Sentence): The sentence being negated
            eval_point (dict): The point of evaluation (typically a world_state)
            
        Returns:
            BoolRef: Z3 expression representing the verification condition
        """
        return self.semantics.extended_falsify(state, arg, eval_point)
    
    def extended_falsify(self, state, arg, eval_point):
        """Defines falsification conditions for negation in the extended semantics.
        
        In the extended semantics, a state falsifies ¬A if and only if it verifies A.
        This implements the hyperintensional semantics where the falsifiers of a negation
        are the verifiers of its argument.
        
        Args:
            state (BitVecRef): The state being evaluated as a falsifier
            arg (Sentence): The sentence being negated
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the falsification condition
        """
        return self.semantics.extended_verify(state, arg, eval_point)

    def find_verifiers_and_falsifiers(self, argument, eval_point):
        """Finds the verifiers and falsifiers for a negation of a proposition.
        
        For negation, the verifiers are the falsifiers of the argument, and
        the falsifiers are the verifiers of the argument. This implements the
        hyperintensional semantics where negation swaps the verifiers and falsifiers.
        
        Args:
            argument (Sentence): The sentence being negated
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            tuple: A pair (verifiers, falsifiers) where:
                - verifiers (set): The set of states that verify the negation
                - falsifiers (set): The set of states that falsify the negation
        """
        Y_V, Y_F = argument.proposition.find_proposition()
        return Y_F, Y_V

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its argument with proper indentation.
        
        Args:
            sentence_obj (Sentence): The sentence object containing the proposition
            eval_point (dict): The point of evaluation (typically a world)
            indent_num (int): The current indentation level
            use_colors (bool): Whether to use colored output
        """
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class AndOperator(syntactic.Operator):
    """Implementation of logical conjunction (∧).
    
    This operator implements both intensional truth/falsity conditions and
    hyperintensional verifier/falsifier semantics for conjunction. A conjunction
    A ∧ B is true when both A and B are true, and false when either A or B is false.
    
    In the hyperintensional semantics, the verifiers of A ∧ B are the fusions of verifiers
    of A with verifiers of B. The falsifiers include the falsifiers of either conjunct
    as well as fusions of falsifiers.
    
    Class Attributes:
        name (str): Symbol representing conjunction ("\\wedge")
        arity (int): Number of arguments (2)
    """

    name = "\\wedge"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Defines truth conditions for conjunction at an evaluation point.
        
        A conjunction A ∧ B is true at an evaluation point if and only if
        both A is true and B is true at that evaluation point.
        
        Args:
            leftarg (Sentence): The left conjunct (A)
            rightarg (Sentence): The right conjunct (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the truth condition
        """
        sem = self.semantics
        return z3.And(
            sem.true_at(leftarg, eval_point),
            sem.true_at(rightarg, eval_point)
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Defines falsity conditions for conjunction at an evaluation point.
        
        A conjunction A ∧ B is false at an evaluation point if and only if
        either A is false or B is false at that evaluation point.
        
        Args:
            leftarg (Sentence): The left conjunct (A)
            rightarg (Sentence): The right conjunct (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the falsity condition
        """
        sem = self.semantics
        return z3.Or(sem.false_at(leftarg, eval_point), sem.false_at(rightarg, eval_point))

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """Defines verification conditions for conjunction in the extended semantics.
        
        In the extended semantics, a state verifies A ∧ B if and only if it is the fusion
        of a state that verifies A with a state that verifies B. This implements the 
        hyperintensional semantics where verifiers of a conjunction are built from the
        verifiers of its conjuncts.
        
        Args:
            state (BitVecRef): The state being evaluated as a verifier
            leftarg (Sentence): The left conjunct (A)
            rightarg (Sentence): The right conjunct (B) 
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the verification condition
        """
        x = z3.BitVec("ex_and_ver_x", self.semantics.N)
        y = z3.BitVec("ex_and_ver_y", self.semantics.N)
        return Exists(
            [x, y],
            z3.And(
                self.semantics.fusion(x, y) == state,
                self.semantics.extended_verify(x, leftarg, eval_point),
                self.semantics.extended_verify(y, rightarg, eval_point),
            )
        )
    
    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        """Defines falsification conditions for conjunction in the extended semantics.
        
        In the extended semantics, a state falsifies A ∧ B if either:
        1. It falsifies A, or
        2. It falsifies B, or
        3. It is the fusion of states that falsify A and B respectively
        
        This implements the hyperintensional semantics where falsifiers of a conjunction
        can come from falsifiers of either conjunct or combinations thereof.
        
        Args:
            state (BitVecRef): The state being evaluated as a falsifier
            leftarg (Sentence): The left conjunct (A)
            rightarg (Sentence): The right conjunct (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the falsification condition
        """
        x = z3.BitVec("ex_and_fal_x", self.semantics.N)
        y = z3.BitVec("ex_and_fal_y", self.semantics.N)
        return z3.Or(
            self.semantics.extended_falsify(state, leftarg, eval_point),
            self.semantics.extended_falsify(state, rightarg, eval_point),
            Exists(
                [x, y],
                z3.And(
                    state == self.semantics.fusion(x, y),
                    self.semantics.extended_falsify(x, leftarg, eval_point),
                    self.semantics.extended_falsify(y, rightarg, eval_point),
                ),
            )
        )

    def find_verifiers_and_falsifiers(self, leftarg, rightarg, eval_point):
        """Finds the verifiers and falsifiers for a conjunction of two propositions.
        
        Takes two sentence objects as arguments, computes their individual verifiers and
        falsifiers, and returns the verifiers and falsifiers for their conjunction.
        For conjunction, the verifiers are the fusion products of the verifiers of each
        conjunct, while the falsifiers are the coproduct of the falsifiers of each conjunct.
        
        Args:
            leftarg (Sentence): The left conjunct sentence object
            rightarg (Sentence): The right conjunct sentence object
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            tuple: A pair (verifiers, falsifiers) where:
                - verifiers (set): The set of states that verify the conjunction
                - falsifiers (set): The set of states that falsify the conjunction
        """
        sem = self.semantics
        Y_V, Y_F = leftarg.proposition.find_proposition()
        Z_V, Z_F = rightarg.proposition.find_proposition()
        return sem.product(Y_V, Z_V), sem.coproduct(Y_F, Z_F)
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj with proper indentation and formatting.
        
        Args:
            sentence_obj (Sentence): The sentence object containing the proposition
            eval_point (dict): The point of evaluation (typically a world)
            indent_num (int): The current indentation level
            use_colors (bool): Whether to use colored output for formatting
        """
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class OrOperator(syntactic.Operator):
    """Implementation of logical disjunction (∨).
    
    This operator implements both intensional truth/falsity conditions and
    hyperintensional verifier/falsifier semantics for disjunction. A disjunction
    A ∨ B is true when either A or B (or both) are true, and false when both A and B are false.
    
    In the hyperintensional semantics, the verifiers of A ∨ B include the verifiers of 
    either disjunct as well as fusions of verifiers. The falsifiers are the fusions of 
    falsifiers of A with falsifiers of B.
    
    Class Attributes:
        name (str): Symbol representing disjunction ("\\vee")
        arity (int): Number of arguments (2)
    """

    name = "\\vee"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Defines truth conditions for disjunction at an evaluation point.
        
        A disjunction A ∨ B is true at an evaluation point if and only if
        either A is true or B is true (or both) at that evaluation point.
        
        Args:
            leftarg (Sentence): The left disjunct (A)
            rightarg (Sentence): The right disjunct (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the truth condition
        """
        sem = self.semantics
        return z3.Or(sem.true_at(leftarg, eval_point), sem.true_at(rightarg, eval_point))
        sem = self.semantics
        return z3.Or(sem.true_at(leftarg, eval_point), sem.true_at(rightarg, eval_point))

    def false_at(self, leftarg, rightarg, eval_point):
        """Defines falsity conditions for disjunction at an evaluation point.
        
        A disjunction A ∨ B is false at an evaluation point if and only if
        both A is false and B is false at that evaluation point.
        
        Args:
            leftarg (Sentence): The left disjunct (A)
            rightarg (Sentence): The right disjunct (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the falsity condition
        """
        sem = self.semantics
        return z3.And(sem.false_at(leftarg, eval_point), sem.false_at(rightarg, eval_point))

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """Defines verification conditions for disjunction in the extended semantics.
        
        In the extended semantics, a state verifies A ∨ B if either:
        1. It verifies A, or
        2. It verifies B, or
        3. It is the fusion of states that verify A and B respectively
        
        This implements the hyperintensional semantics where verifiers of a disjunction
        can come from verifiers of either disjunct or combinations thereof.
        
        Args:
            state (BitVecRef): The state being evaluated as a verifier
            leftarg (Sentence): The left disjunct (A)
            rightarg (Sentence): The right disjunct (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the verification condition
        """
        x = z3.BitVec("ex_or_ver_x", self.semantics.N)
        y = z3.BitVec("ex_or_ver_y", self.semantics.N)
        return z3.Or(
            self.semantics.extended_verify(state, leftarg, eval_point),
            self.semantics.extended_verify(state, rightarg, eval_point),
            Exists(
                [x, y],
                z3.And(
                    self.semantics.fusion(x, y) == state,
                    self.semantics.extended_verify(x, leftarg, eval_point),
                    self.semantics.extended_verify(y, rightarg, eval_point),
                )
            )
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        """Defines falsification conditions for disjunction in the extended semantics.
        
        In the extended semantics, a state falsifies A ∨ B if and only if it is the fusion
        of states that falsify A and B respectively. This implements the hyperintensional
        semantics where falsifiers of a disjunction are built from the falsifiers of its
        disjuncts.
        
        Args:
            state (BitVecRef): The state being evaluated as a falsifier
            leftarg (Sentence): The left disjunct (A)
            rightarg (Sentence): The right disjunct (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the falsification condition
        """
        x = z3.BitVec("ex_fal_x", self.semantics.N)
        y = z3.BitVec("ex_fal_y", self.semantics.N)
        return Exists(
            [x, y],
            z3.And(
                state == self.semantics.fusion(x, y),
                self.semantics.extended_falsify(x, leftarg, eval_point),
                self.semantics.extended_falsify(y, rightarg, eval_point),
            ),
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Finds the verifiers and falsifiers for a relevance relation between propositions.
        
        Takes two sentence objects as arguments and returns the verifiers and falsifiers
        for their relevance relation. For relevance A ≼ B, the relation is verified by
        the null state if both verifiers and falsifiers of A combine with those of B to
        yield B's verifiers and falsifiers respectively. Otherwise it is falsified by
        the null state.
        
        Args:
            left_sent_obj (Sentence): The left argument sentence object (A)
            right_sent_obj (Sentence): The right argument sentence object (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            tuple: A pair (verifiers, falsifiers) where:
                - verifiers (set): The set of states that verify the relevance relation
                - falsifiers (set): The set of states that falsify the relevance relation
        """
        semantics = self.semantics
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        return semantics.coproduct(Y_V, Z_V), semantics.product(Y_F, Z_F)
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj with proper indentation and formatting.
        
        Args:
            sentence_obj (Sentence): The sentence object containing the proposition
            eval_point (dict): The point of evaluation (typically a world)
            indent_num (int): The current indentation level
            use_colors (bool): Whether to use colored output for formatting
        """
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


##############################################################################
############################## EXTREMAL OPERATORS ############################
##############################################################################

class TopOperator(syntactic.Operator):
    """Implementation of the tautology or top element (⊤).
    
    This operator represents the logical tautology or 'top' element of the
    propositional lattice. It is always true regardless of the evaluation point.
    
    In the hyperintensional semantics, ⊤ is verified by every state and falsified
    by none, representing the most general or least discriminating proposition.
    
    Class Attributes:
        name (str): Symbol representing top ("\\top")
        arity (int): Number of arguments (0)
    """

    name = "\\top"
    arity = 0

    def true_at(self, eval_point):
        """Defines truth conditions for the top element at an evaluation point.
        
        The top element ⊤ is always true at every evaluation point.
        
        Args:
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            bool: Always returns True (represented as 1 == 1)
        """
        return 1 == 1

    def false_at(self, eval_point):
        """Defines falsity conditions for the top element at an evaluation point.
        
        The top element ⊤ is never false at any evaluation point.
        
        Args:
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            bool: Always returns False (represented as 1 != 1)
        """
        return 1 != 1

    def extended_verify(self, state, eval_point):
        """Defines verification conditions for top in the extended semantics.
        
        In the extended semantics, every state verifies ⊤, representing that
        it is the most general or least discriminating proposition.
        
        Args:
            state (BitVecRef): The state being evaluated as a verifier
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression that is always true for any state
        """
        return state == state

    def extended_falsify(self, state, eval_point):
        """Defines falsification conditions for top in the extended semantics.
        
        In the extended semantics, only the (most impossible) full state
        falsifies ⊤ on account of being the top element with respect to parthood.
        
        Args:
            state (BitVecRef): The state being evaluated as a falsifier
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression requiring state to be the full state
        """
        return state == self.semantics.full_state

    def find_verifiers_and_falsifiers(self, eval_point):
        """Finds the verifiers and falsifiers for the top element.
        
        For ⊤, every state is a verifier and only the full state is a falsifier.
        
        Args:
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            tuple: A pair (verifiers, falsifiers) where:
                - verifiers (set): The set of all possible states
                - falsifiers (set): A singleton set containing only the full state
        """
        return set(self.semantics.all_states), {self.semantics.full_state}

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the top element with proper indentation and formatting.
        
        Args:
            sentence_obj (Sentence): The sentence object containing the proposition
            eval_point (dict): The point of evaluation (typically a world)
            indent_num (int): The current indentation level
            use_colors (bool): Whether to use colored output for formatting
        """
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class BotOperator(syntactic.Operator):
    """Implementation of the contradiction or bottom element (⊥).
    
    This operator represents logical contradiction or the 'bottom' element of the
    propositional lattice. It is always false regardless of the evaluation point.
    
    In the hyperintensional semantics, ⊥ is verified by no state and falsified by
    every state, representing the most specific or most discriminating proposition.
    
    Class Attributes:
        name (str): Symbol representing bottom ("\\bot")
        arity (int): Number of arguments (0)

    The bottom element of the space of propositions with respect to ground is
    verified by nothing and falsified by the null state."""

    name = "\\bot"
    arity = 0

    def true_at(self, eval_point):
        """Defines truth conditions for the bottom element at an evaluation point.
        
        The bottom element ⊥ is never true at any evaluation point.
        
        Args:
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            bool: Always returns False (represented as 1 != 1)
        """
        return 1 != 1

    def false_at(self, eval_point):
        """Defines falsity conditions for the bottom element at an evaluation point.
        
        The bottom element ⊥ is always false at every evaluation point.
        
        Args:
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            bool: Always returns True (represented as 1 == 1)
        """
        return 1 == 1

    def extended_verify(self, state, eval_point):
        """Defines verification conditions for bottom in the extended semantics.
        
        In the extended semantics, no state verifies ⊥, representing that
        it is the most specific or most discriminating proposition.
        
        Args:
            state (BitVecRef): The state being evaluated as a verifier
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression that is never satisfied by any state
        """
        return state != state

    def extended_falsify(self, state, eval_point):
        """Defines falsification conditions for bottom in the extended semantics.
        
        In the extended semantics, only the (most possible) null state falsifies
        ⊥ on account of being the bottom state with respect to parthood.
        
        Args:
            state (BitVecRef): The state being evaluated as a falsifier
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression requiring state to be the null state
        """
        return state == self.semantics.null_state

    def find_verifiers_and_falsifiers(self, eval_point):
        """Finds the verifiers and falsifiers for the bottom element.
        
        For ⊥, no state is a verifier and only the null state is a falsifier.
        
        Args:
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            tuple: A pair (verifiers, falsifiers) where:
                - verifiers (set): Empty set since nothing verifies ⊥
                - falsifiers (set): Singleton set containing only the null state
        """
        return set(), {self.semantics.null_state}

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the bottom element with proper indentation and formatting.
        
        Args:
            sentence_obj (Sentence): The sentence object containing the proposition
            eval_point (dict): The point of evaluation (typically a world)
            indent_num (int): The current indentation level
            use_colors (bool): Whether to use colored output for formatting
        """
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


##############################################################################
########################### CONSTITUTIVE OPERATORS ###########################
##############################################################################

class IdentityOperator(syntactic.Operator):
    """Implementation of the identity operator (≡).
    
    This operator represents the identity relation between propositions, where
    A ≡ B means that A and B have exactly the same content. Two propositions
    are identical when they have the same verifiers and the same falsifiers.
    
    The truth conditions check if the verifiers of A are exactly the verifiers of B
    and if the falsifiers of A are exactly the falsifiers of B.
    
    Class Attributes:
        name (str): Symbol representing the identity relation ("\\equiv")
        arity (int): Number of arguments (2)
    """

    name = "\\equiv"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Defines truth conditions for identity at an evaluation point.
        
        The identity relation A ≡ B is true at an evaluation point if and only
        if A and B have exactly the same verifiers and falsifiers.
        
        This implements the exact content identity between propositions where they
        must have precisely the same verifiers and falsifiers.
        
        Args:
            leftarg (Sentence): The left argument of the identity relation (A)
            rightarg (Sentence): The right argument of the identity relation (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the truth condition
        """
        N = self.semantics.N
        sem = self.semantics
        x = z3.BitVec("t_id_x", N)
        return z3.And(
            ForAll(
                x,
                z3.Implies(
                    sem.extended_verify(x, leftarg, eval_point),
                    sem.extended_verify(x, rightarg, eval_point)
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_falsify(x, leftarg, eval_point),
                    sem.extended_falsify(x, rightarg, eval_point)
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_verify(x, rightarg, eval_point),
                    sem.extended_verify(x, leftarg, eval_point)
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_falsify(x, rightarg, eval_point),
                    sem.extended_falsify(x, leftarg, eval_point)
                ),
            )
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Defines falsity conditions for identity at an evaluation point.
        
        The identity relation A ≡ B is false at an evaluation point if and only
        if A and B do not have exactly the same verifiers and falsifiers.
        
        This implements exact content identity where propositions must have
        precisely the same verifiers and falsifiers.
        
        Args:
            leftarg (Sentence): The left argument of the identity relation (A)
            rightarg (Sentence): The right argument of the identity relation (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the falsity condition
        """
        sem = self.semantics
        N = self.semantics.N
        x = z3.BitVec("f_id_x", N)
        return z3.Or(
            Exists(
                x,
                z3.And(
                    sem.extended_verify(x, leftarg, eval_point),
                    z3.Not(sem.extended_verify(x, rightarg, eval_point))
                ),
            ),
            Exists(
                x,
                z3.And(
                    sem.extended_falsify(x, leftarg, eval_point),
                    z3.Not(sem.extended_falsify(x, rightarg, eval_point))
                ),
            ),
            Exists(
                x,
                z3.And(
                    sem.extended_verify(x, rightarg, eval_point),
                    z3.Not(sem.extended_verify(x, leftarg, eval_point))
                ),
            ),
            Exists(
                x,
                z3.And(
                    sem.extended_falsify(x, rightarg, eval_point),
                    z3.Not(sem.extended_falsify(x, leftarg, eval_point))
                ),
            )
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """Defines verification conditions for identity in the extended semantics.
        
        In the extended semantics, a state verifies A ≡ B if and only if:
        1. It is the null state, and
        2. A and B have exactly the same verifiers and falsifiers
        
        This implements the idea that identity statements, when true, are verified
        by the null state since they express a purely logical relationship.
        
        Args:
            state (BitVecRef): The state being evaluated as a verifier
            leftarg (Sentence): The left argument of the identity relation (A)
            rightarg (Sentence): The right argument of the identity relation (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the verification condition
        """
        return z3.And(
            state == self.semantics.null_state,
            self.true_at(leftarg, rightarg, eval_point)
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        """Defines falsification conditions for identity in the extended semantics.
        
        In the extended semantics, a state falsifies A ≡ B if and only if:
        1. It is the null state, and
        2. A and B do not have exactly the same verifiers and falsifiers
        
        This implements the idea that identity statements, when false, are falsified
        by the null state since they express a purely logical relationship.
        
        Args:
            state (BitVecRef): The state being evaluated as a falsifier
            leftarg (Sentence): The left argument of the identity relation (A)
            rightarg (Sentence): The right argument of the identity relation (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the falsification condition
        """
        return z3.And(
            state == self.semantics.null_state,
            self.false_at(leftarg, rightarg, eval_point)
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Finds the verifiers and falsifiers for an identity relation between propositions.
        
        For identity A ≡ B, the relation is verified by the null state if A and B have
        exactly the same verifiers and falsifiers. Otherwise it is falsified by the null state.
        This implements the idea that identity statements, when true, are verified by the
        null state since they express a purely logical relationship.
        
        Args:
            left_sent_obj (Sentence): The left argument sentence object (A)
            right_sent_obj (Sentence): The right argument sentence object (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            tuple: A pair (verifiers, falsifiers) where:
                - verifiers (set): Contains null_state if A and B are identical, empty otherwise
                - falsifiers (set): Contains null_state if A and B differ, empty otherwise
        """
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        if Y_V == Z_V and Y_F == Z_F:
            return {self.semantics.null_state}, set()
        return set(), {self.semantics.null_state}
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the bottom element with proper indentation and formatting.
        
        Args:
            sentence_obj (Sentence): The sentence object containing the proposition
            eval_point (dict): The point of evaluation (typically a world)
            indent_num (int): The current indentation level
            use_colors (bool): Whether to use colored output for formatting
        """
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class GroundOperator(syntactic.Operator):
    """Implementation of the ground/entailment operator (≤).
    
    This operator represents the grounding relation between propositions, where
    A ≤ B means that A grounds B or A entails B. The relation captures when the
    content of one proposition serves as the ground or basis for another.
    
    The truth conditions involve several requirements:
    1. Every verifier of A must also be a verifier of B
    2. Falsifiers of A and B must combine to falsify B
    3. Every falsifier of B must have a part that falsifies A
    
    Class Attributes:
        name (str): Symbol representing the ground relation ("\\leq")
        arity (int): Number of arguments (2)
    """

    name = "\\leq"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Defines truth conditions for the ground relation at an evaluation point.
        
        The ground relation A ≤ B is true at an evaluation point when:
        1. Every verifier of A is also a verifier of B
        2. Falsifiers of A and B combine to falsify B
        3. Every falsifier of B has a part that falsifies A
        
        Args:
            leftarg (Sentence): The ground proposition (A)
            rightarg (Sentence): The grounded proposition (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the truth condition
        """
        N = self.semantics.N
        sem = self.semantics
        x = z3.BitVec("t_seq_x", N)
        y = z3.BitVec("t_seq_y", N)
        return z3.And(
            ForAll(
                x,
                z3.Implies(
                    sem.extended_verify(x, leftarg, eval_point),
                    sem.extended_verify(x, rightarg, eval_point)
                )
            ),
            ForAll(
                [x, y],
                z3.Implies(
                    z3.And(
                        sem.extended_falsify(x, leftarg, eval_point),
                        sem.extended_falsify(y, rightarg, eval_point)
                    ),
                    sem.extended_falsify(sem.fusion(x, y), rightarg, eval_point)
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_falsify(x, rightarg, eval_point),
                    Exists(
                        y,
                        z3.And(
                            sem.extended_falsify(y, leftarg, eval_point),
                            sem.is_part_of(y, x),
                        )
                    )
                ),
            ),
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Defines falsity conditions for the ground relation at an evaluation point.
        
        The ground relation A ≤ B is false at an evaluation point if any of these hold:
        1. There exists a verifier of A that is not a verifier of B
        2. There exist falsifiers of A and B whose fusion does not falsify B
        3. There exists a falsifier of B that has no part falsifying A
        
        Args:
            leftarg (Sentence): The ground proposition (A)
            rightarg (Sentence): The grounded proposition (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the falsity condition
        """
        sem = self.semantics
        N = self.semantics.N
        x = z3.BitVec("f_seq_x", N)
        y = z3.BitVec("f_seq_y", N)
        return z3.Or(
            Exists(
                x,
                z3.And(
                    sem.extended_verify(x, leftarg, eval_point),
                    z3.Not(sem.extended_verify(x, rightarg, eval_point))
                )
            ),
            Exists(
                [x, y],
                z3.And(
                    sem.extended_falsify(x, leftarg, eval_point),
                    sem.extended_falsify(y, rightarg, eval_point),
                    z3.Not(sem.extended_falsify(sem.fusion(x, y), rightarg, eval_point))
                ),
            ),
            Exists(
                x,
                z3.And(
                    sem.extended_falsify(x, rightarg, eval_point),
                    ForAll(
                        y,
                        z3.Implies(
                            sem.extended_falsify(y, leftarg, eval_point),
                            z3.Not(sem.is_part_of(y, x)),
                        )
                    )
                ),
            ),
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """Defines verification conditions for ground relation in the extended semantics.
        
        In the extended semantics, a state verifies A ≤ B if and only if:
        1. It is the null state, and
        2. The ground relation holds between A and B
        
        This implements the idea that ground statements, when true, are verified
        by the null state since they express a purely logical relationship.
        
        Args:
            state (BitVecRef): The state being evaluated as a verifier
            leftarg (Sentence): The ground proposition (A)
            rightarg (Sentence): The grounded proposition (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the verification condition
        """
        return z3.And(
            state == self.semantics.null_state,
            self.true_at(leftarg, rightarg, eval_point)
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        """Defines falsification conditions for ground relation in the extended semantics.
        
        In the extended semantics, a state falsifies A ≤ B if and only if:
        1. It is the null state, and
        2. The ground relation fails to hold between A and B
        
        This implements the idea that ground statements, when false, are falsified
        by the null state since they express a purely logical relationship.
        
        Args:
            state (BitVecRef): The state being evaluated as a falsifier
            leftarg (Sentence): The ground proposition (A)
            rightarg (Sentence): The grounded proposition (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the falsification condition
        """
        return z3.And(
            state == self.semantics.null_state,
            self.false_at(leftarg, rightarg, eval_point)
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Finds the verifiers and falsifiers for a ground relation between propositions.
        
        Takes two sentence objects as arguments and returns the verifiers and falsifiers
        for their ground relation. For ground A ≤ B, the relation is verified by the
        null state if the verifiers of A combine with verifiers of B to yield B's verifiers
        and the falsifiers of A combine with falsifiers of B to yield B's falsifiers.
        Otherwise it is falsified by the null state.
        
        Args:
            left_sent_obj (Sentence): The ground proposition sentence object (A)
            right_sent_obj (Sentence): The grounded proposition sentence object (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            tuple: A pair (verifiers, falsifiers) where:
                - verifiers (set): Contains null_state if A grounds B, empty otherwise
                - falsifiers (set): Contains null_state if A doesn't ground B, empty otherwise
        """
        product = self.semantics.product
        coproduct = self.semantics.coproduct
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        if coproduct(Y_V, Z_V) == Z_V and product(Y_F, Z_F) == Z_F:
            return {self.semantics.null_state}, set()
        return set(), {self.semantics.null_state}

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors ):
        """Prints the bottom element with proper indentation and formatting.
        
        Args:
            sentence_obj (Sentence): The sentence object containing the proposition
            eval_point (dict): The point of evaluation (typically a world)
            indent_num (int): The current indentation level
            use_colors (bool): Whether to use colored output for formatting
        """
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class EssenceOperator(syntactic.Operator):
    """Implementation of the essence operator (⊑).
    
    This operator represents the essence relation between propositions, where
    A ⊑ B means that A is the essence of B. This captures the notion that the
    content of A is essential to the content of B, a stronger relation than grounding.
    
    The truth conditions involve three requirements:
    1. Verifiers of A and B must combine to always verify B
    2. Every verifier of B must have a part that verifies A
    3. Every falsifier of A must also be a falsifier of B
    
    Class Attributes:
        name (str): Symbol representing the essence relation ("\\sqsubseteq")
        arity (int): Number of arguments (2)
    """

    name = "\\sqsubseteq"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Defines truth conditions for essence relation at an evaluation point.
        
        The essence relation A ⊑ B is true at an evaluation point if and only if:
        1. Verifiers of A and B must combine to verify B
        2. Every verifier of B must have a part that verifies A
        3. Every falsifier of A must also be a falsifier of B
        
        This implements the idea that A is essential to B when A's content is an
        indispensable part of B's content, a stronger relation than grounding.
        
        Args:
            leftarg (Sentence): The essential proposition (A)
            rightarg (Sentence): The proposition containing the essence (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the truth condition
        """
        N = self.semantics.N
        sem = self.semantics
        x = z3.BitVec("t_seq_x", N)
        y = z3.BitVec("t_seq_y", N)
        return z3.And(
            ForAll(
                [x, y],
                z3.Implies(
                    z3.And(
                        sem.extended_verify(x, leftarg, eval_point),
                        sem.extended_verify(y, rightarg, eval_point)
                    ),
                    sem.extended_verify(sem.fusion(x, y), rightarg, eval_point)
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_verify(x, rightarg, eval_point),
                    Exists(
                        y,
                        z3.And(
                            sem.extended_verify(y, leftarg, eval_point),
                            sem.is_part_of(y, x),
                        )
                    )
                ),
            ),
            ForAll(
                x,
                z3.Implies(
                    sem.extended_falsify(x, leftarg, eval_point),
                    sem.extended_falsify(x, rightarg, eval_point)
                )
            )
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Defines falsity conditions for essence relation at an evaluation point.
        
        The essence relation A ⊑ B is false at an evaluation point if any of these hold:
        1. There exist verifiers of A and B whose fusion does not verify B
        2. There exists a verifier of B that has no part verifying A
        3. There exists a falsifier of A that is not a falsifier of B
        
        This implements the negation of the essence relation, where A fails to be
        essential to B if any of the three requirements for essence fails.
        
        Args:
            leftarg (Sentence): The essential proposition (A)
            rightarg (Sentence): The proposition containing the essence (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the falsity condition
        """
        sem = self.semantics
        N = self.semantics.N
        x = z3.BitVec("f_seq_x", N)
        y = z3.BitVec("f_seq_y", N)
        return z3.Or(
            Exists(
                [x, y],
                z3.And(
                    sem.extended_verify(x, leftarg, eval_point),
                    sem.extended_verify(y, rightarg, eval_point),
                    z3.Not(sem.extended_verify(sem.fusion(x, y), rightarg, eval_point))
                ),
            ),
            Exists(
                x,
                z3.And(
                    sem.extended_verify(x, rightarg, eval_point),
                    ForAll(
                        y,
                        z3.Implies(
                            sem.extended_verify(y, leftarg, eval_point),
                            z3.Not(sem.is_part_of(y, x)),
                        )
                    )
                ),
            ),
            Exists(
                x,
                z3.And(
                    sem.extended_falsify(x, leftarg, eval_point),
                    z3.Not(sem.extended_falsify(x, rightarg, eval_point))
                )
            )
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """Defines verification conditions for essence relation in the extended semantics.
        
        In the extended semantics, a state verifies A ⊑ B if and only if:
        1. It is the null state, and
        2. The essence relation holds between A and B
        
        This implements the idea that essence statements, when true, are verified
        by the null state since they express a purely logical relationship.
        
        Args:
            state (BitVecRef): The state being evaluated as a verifier
            leftarg (Sentence): The essential proposition (A)
            rightarg (Sentence): The proposition containing the essence (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the verification condition
        """
        return z3.And(
            state == self.semantics.null_state,
            self.true_at(leftarg, rightarg, eval_point)
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        """Defines falsification conditions for essence relation in the extended semantics.
        
        In the extended semantics, a state falsifies A ⊑ B if and only if:
        1. It is the null state, and
        2. The essence relation fails to hold between A and B
        
        This implements the idea that essence statements, when false, are falsified
        by the null state since they express a purely logical relationship.
        
        Args:
            state (BitVecRef): The state being evaluated as a falsifier
            leftarg (Sentence): The essential proposition (A)
            rightarg (Sentence): The proposition containing the essence (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the falsification condition
        """
        return z3.And(
            state == self.semantics.null_state,
            self.false_at(leftarg, rightarg, eval_point)
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Finds the verifiers and falsifiers for an essence relation between propositions.
        
        Takes two sentence objects as arguments and returns the verifiers and falsifiers
        for their essence relation. For essence A ⊑ B, the relation is verified by the
        null state if the verifiers of A combine with verifiers of B to yield B's verifiers
        and the falsifiers of A combine with falsifiers of B to yield B's falsifiers.
        Otherwise it is falsified by the null state.
        
        Args:
            left_sent_obj (Sentence): The essential proposition sentence object (A)
            right_sent_obj (Sentence): The proposition containing the essence (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            tuple: A pair (verifiers, falsifiers) where:
                - verifiers (set): Contains null_state if A is essential to B, empty otherwise
                - falsifiers (set): Contains null_state if A is not essential to B, empty otherwise
        """
        product = self.semantics.product
        coproduct = self.semantics.coproduct
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        if product(Y_V, Z_V) == Z_V and coproduct(Y_F, Z_F) == Z_F:
            return {self.semantics.null_state}, set()
        return set(), {self.semantics.null_state}
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the bottom element with proper indentation and formatting.
        
        Args:
            sentence_obj (Sentence): The sentence object containing the proposition
            eval_point (dict): The point of evaluation (typically a world)
            indent_num (int): The current indentation level
            use_colors (bool): Whether to use colored output for formatting
        """
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class RelevanceOperator(syntactic.Operator):
    """Implementation of the relevance operator (≼).
    
    This operator represents the relevance relation between propositions, where
    A ≼ B means that A is relevant to B. This captures a weaker notion than
    grounding or essence, focusing only on content relevance.
    
    The truth conditions involve two requirements:
    1. Verifiers of A and B must combine to verify B
    2. Falsifiers of A and B must combine to falsify B
    
    Class Attributes:
        name (str): Symbol representing the relevance relation ("\\preceq")
        arity (int): Number of arguments (2)
    """

    name = "\\preceq"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Defines truth conditions for relevance relation at an evaluation point.
        
        The relevance relation A ≼ B is true at an evaluation point if and only if:
        1. The fusion of any verifiers of A and B verifies B
        2. The fusion of any falsifiers of A and B falsifies B
        
        This implements the idea that A is relevant to B when both the verifiers and
        falsifiers of A can meaningfully combine with those of B to yield B's content.
        
        Args:
            leftarg (Sentence): The relevant proposition (A)
            rightarg (Sentence): The proposition being related to (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the truth condition
        """
        N = self.semantics.N
        sem = self.semantics
        x = z3.BitVec("t_peq_x", N)
        y = z3.BitVec("t_peq_y", N)
        return z3.And(
            ForAll(
                [x, y],
                z3.Implies(
                    z3.And(
                        sem.extended_verify(x, leftarg, eval_point),
                        sem.extended_verify(y, rightarg, eval_point)
                    ),
                    sem.extended_verify(sem.fusion(x, y), rightarg, eval_point)
                ),
            ),
            ForAll(
                [x, y],
                z3.Implies(
                    z3.And(
                        sem.extended_falsify(x, leftarg, eval_point),
                        sem.extended_falsify(y, rightarg, eval_point)
                    ),
                    sem.extended_falsify(sem.fusion(x, y), rightarg, eval_point)
                ),
            ),
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Defines falsity conditions for relevance relation at an evaluation point.
        
        The relevance relation A ≼ B is false at an evaluation point if either:
        1. There exist verifiers of A and B whose fusion does not verify B, or
        2. There exist falsifiers of A and B whose fusion does not falsify B
        
        This implements the negation of relevance, where A fails to be relevant to B
        if either verifiers or falsifiers fail to combine appropriately.
        
        Args:
            leftarg (Sentence): The relevant proposition (A)
            rightarg (Sentence): The proposition being related to (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the falsity condition
        """
        sem = self.semantics
        N = self.semantics.N
        x = z3.BitVec("f_seq_x", N)
        y = z3.BitVec("f_seq_y", N)
        return z3.Or(
            Exists(
                [x, y],
                z3.And(
                    sem.extended_verify(x, leftarg, eval_point),
                    sem.extended_verify(y, rightarg, eval_point),
                    z3.Not(sem.extended_verify(sem.fusion(x, y), rightarg, eval_point))
                ),
            ),
            Exists(
                [x, y],
                z3.And(
                    sem.extended_falsify(x, leftarg, eval_point),
                    sem.extended_falsify(y, rightarg, eval_point),
                    z3.Not(sem.extended_falsify(sem.fusion(x, y), rightarg, eval_point))
                ),
            ),
        )

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """Defines verification conditions for relevance relation in the extended semantics.
        
        In the extended semantics, a state verifies A ≼ B if and only if:
        1. It is the null state, and
        2. The relevance relation holds between A and B
        
        This implements the idea that relevance statements, when true, are verified
        by the null state since they express a purely logical relationship.
        
        Args:
            state (BitVecRef): The state being evaluated as a verifier
            leftarg (Sentence): The relevant proposition (A)
            rightarg (Sentence): The proposition being related to (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the verification condition
        """
        return z3.And(
            state == self.semantics.null_state,
            self.true_at(leftarg, rightarg, eval_point)
        )

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        """Defines falsification conditions for relevance relation in the extended semantics.
        
        In the extended semantics, a state falsifies A ≼ B if and only if:
        1. It is the null state, and
        2. The relevance relation fails to hold between A and B
        
        This implements the idea that relevance statements, when false, are falsified
        by the null state since they express a purely logical relationship.
        
        Args:
            state (BitVecRef): The state being evaluated as a falsifier
            leftarg (Sentence): The relevant proposition (A)
            rightarg (Sentence): The proposition being related to (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the falsification condition
        """
        return z3.And(
            state == self.semantics.null_state,
            self.false_at(leftarg, rightarg, eval_point)
        )

    def find_verifiers_and_falsifiers(self, left_sent_obj, right_sent_obj, eval_point):
        """Finds the verifiers and falsifiers for a relevance relation between propositions.
        
        Takes two sentence objects as arguments and returns the verifiers and falsifiers
        for their relevance relation. For relevance A ≼ B, the relation is verified by
        the null state if both verifiers and falsifiers of A combine with those of B to
        yield B's verifiers and falsifiers respectively. Otherwise it is falsified by
        the null state.
        
        Args:
            left_sent_obj (Sentence): The relevant proposition sentence object (A)
            right_sent_obj (Sentence): The proposition being related to (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            tuple: A pair (verifiers, falsifiers) where:
                - verifiers (set): Contains null_state if A is relevant to B, empty otherwise
                - falsifiers (set): Contains null_state if A is not relevant to B, empty otherwise
        """
        product = self.semantics.product
        coproduct = self.semantics.coproduct
        Y_V, Y_F = left_sent_obj.proposition.find_proposition()
        Z_V, Z_F = right_sent_obj.proposition.find_proposition()
        if product(Y_V, Z_V) == Z_V and coproduct(Y_F, Z_F) == Z_F:
            return {self.semantics.null_state}, set()
        return set(), {self.semantics.null_state}
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the bottom element with proper indentation and formatting.
        
        Args:
            sentence_obj (Sentence): The sentence object containing the proposition
            eval_point (dict): The point of evaluation (typically a world)
            indent_num (int): The current indentation level
            use_colors (bool): Whether to use colored output for formatting
        """
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


##############################################################################
########################## COUNTERFACTUAL OPERATORS ##########################
##############################################################################

class CounterfactualOperator(syntactic.Operator):
    """Implementation of the counterfactual conditional operator (□→).
    
    This operator represents the counterfactual conditional 'if A were the case, B would be the case',
    often written as A □→ B. The semantics involves considering alternative worlds where the
    antecedent A is true, and checking if the consequent B is also true in those worlds.
    
    The truth conditions state that A □→ B is true at a world w if B is true in all the
    closest A-worlds to w (worlds where A is true that are most similar to w).
    
    Class Attributes:
        name (str): Symbol representing the counterfactual conditional ("\boxright")
        arity (int): Number of arguments (2)
    """
    name = "\\boxright"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Defines truth conditions for counterfactual conditional at an evaluation point.
        
        A counterfactual A □→ B is true at an evaluation point if and only if B is true
        in all the A-alternatives to the evaluation point.
        
        Args:
            leftarg (Sentence): The antecedent proposition (A)
            rightarg (Sentence): The consequent proposition (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the truth condition that B holds
                     in all A-alternatives to the evaluation point.
        """
        semantics = self.semantics
        N = semantics.N
        x = z3.BitVec("t_ncf_x", N)
        u = z3.BitVec("t_ncf_u", N)
        return ForAll(
            [x, u],
            z3.Implies(
                z3.And(
                    semantics.extended_verify(x, leftarg, eval_point), # need extended_verify
                    semantics.is_alternative(u, x, eval_point)
                ),
                semantics.true_at(rightarg, u),
            ),
        )
    
    def false_at(self, leftarg, rightarg, eval_point):
        """Defines falsity conditions for counterfactual conditional at an evaluation point.
        
        A counterfactual A □→ B is false at an evaluation point if and only if B is false
        in at least one of the A-alternatives to the evaluation point.
        
        Args:
            leftarg (Sentence): The antecedent proposition (A)
            rightarg (Sentence): The consequent proposition (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the falsity condition that B
                     does not hold in some A-alternative to the evaluation point
        """
        semantics = self.semantics
        N = semantics.N
        x = z3.BitVec("f_ncf_x", N)
        u = z3.BitVec("f_ncf_u", N)
        return Exists(
            [x, u],
            z3.And(
                semantics.extended_verify(x, leftarg, eval_point), # need extended_verify
                semantics.is_alternative(u, x, eval_point),
                semantics.false_at(rightarg, u)),
        )
    
    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """Defines verification conditions for counterfactual conditional in the extended semantics.
        
        In the extended semantics, a state verifies A □→ B if and only if:
        1. It is the null state, and
        2. The counterfactual relation holds between A and B
        
        This implements the idea that counterfactual statements, when true, are verified
        by the null state since they express a purely logical relationship.
        
        Args:
            state (BitVecRef): The state being evaluated as a verifier
            leftarg (Sentence): The antecedent proposition (A)
            rightarg (Sentence): The consequent proposition (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the verification condition
        """
        return z3.And(
            state == self.semantics.null_state,
            self.true_at(leftarg, rightarg, eval_point)
        )
    
    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        """Defines falsification conditions for counterfactual conditional in the extended semantics.
        
        In the extended semantics, a state falsifies A □→ B if and only if:
        1. It is the null state, and
        2. The counterfactual relation fails to hold between A and B
        
        This implements the idea that counterfactual statements, when false, are falsified
        by the null state since they express a purely logical relationship.
        
        Args:
            state (BitVecRef): The state being evaluated as a falsifier
            leftarg (Sentence): The antecedent proposition (A)
            rightarg (Sentence): The consequent proposition (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the falsification condition
        """
        return z3.And(
            state == self.semantics.null_state,
            self.false_at(leftarg, rightarg, eval_point)
        )

    def find_verifiers_and_falsifiers(self, leftarg, rightarg, eval_point):
        """Finds the verifiers and falsifiers for a counterfactual conditional between propositions.
        
        Takes two sentence objects as arguments and returns the verifiers and falsifiers
        for their counterfactual conditional. For counterfactual A □→ B, the relation is 
        verified by the null state if B is true in all A-alternatives to the evaluation point.
        Otherwise it is falsified by the null state.
        
        Args:
            leftarg (Sentence): The antecedent sentence object (A)
            rightarg (Sentence): The consequent sentence object (B)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            tuple: A pair (verifiers, falsifiers) where:
                - verifiers (set): Contains null_state if A □→ B is true, empty otherwise
                - falsifiers (set): Contains null_state if A □→ B is false, empty otherwise
                
        Raises:
            ValueError: If the counterfactual is neither true nor false at the evaluation point
        """
        evaluate = leftarg.proposition.model_structure.z3_model.evaluate
        if bool(evaluate(self.true_at(leftarg, rightarg, eval_point))):
            return {self.semantics.null_state}, set()
        if bool(evaluate(self.false_at(leftarg, rightarg, eval_point))):
            return set(), {self.semantics.null_state}
        raise ValueError(
            f"{leftarg.name} {self.name} {rightarg.name} "
            f"is neither true nor false in the world {eval_point}."
        )
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """
        For modal and counterfactual operators, this method:
        1. Prints the full proposition at the current evaluation point
        2. Prints the antecedent's evaluation at the current world
        3. Prints the consequent's at all alternative worlds being considered
        4. Uses increased indentation to show the nested structure
        
        Args:
            sentence_obj (Sentence): The sentence object containing the proposition
            eval_point (dict): The point of evaluation (typically a world)
            indent_num (int): The current indentation level for formatting output
            use_colors (bool): Whether to use ANSI color codes in output
        """
        is_alt = self.semantics.calculate_alternative_worlds
        model_structure = sentence_obj.proposition.model_structure
        left_argument_obj = sentence_obj.original_arguments[0]
        left_argument_verifiers = left_argument_obj.proposition.verifiers
        alt_worlds = is_alt(left_argument_verifiers, eval_point, model_structure)
        self.print_over_worlds(sentence_obj, eval_point, alt_worlds, indent_num, use_colors)


class ImpositionOperator(syntactic.Operator):
    """Implementation of the Kit Fine's imposition semantics for counterfactuals.
    
    The truth conditions state that (A \\imposition B) is true at a world w if
    B is true in all worlds that result from imposing the verifiers for A on w.
    
    Class Attributes:
        name (str): Symbol representing the imposition operator ("\\imposition")
        arity (int): Number of arguments (2)
    """
    name = "\\imposition"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_world):
        """Defines truth conditions for imposition at an evaluation world.
        
        (A \\imposition B) is true at a world w if and only if B is true in all worlds
        that result from imposing any verifier of A on w.
        
        Args:
            leftarg (Sentence): The proposition being imposed (A)
            rightarg (Sentence): The consequent proposition (B)
            eval_world (dict): The world where the imposition is evaluated
            
        Returns:
            BoolRef: Z3 expression representing the truth condition that B holds
                    in all worlds resulting from imposing A's verifiers on eval_world
        """
        sem = self.semantics
        N = sem.N
        x = z3.BitVec("t_imp_x", N)
        u = z3.BitVec("t_imp_u", N)
        return ForAll(
            [x, u],
            z3.Implies(
                z3.And(
                    sem.extended_verify(x, leftarg, eval_world),
                    sem.imposition(x, eval_world, u)
                ),
                sem.true_at(rightarg, u),
            ),
        )
    
    def false_at(self, leftarg, rightarg, eval_world):
        """Defines falsity conditions for imposition at an evaluation world.
        
        (A \\imposition B) is false at a world w if and only if B is false in at
        least one world that results from imposing some verifier of A on w.
        
        Args:
            leftarg (Sentence): The proposition being imposed (A)
            rightarg (Sentence): The consequent proposition (B)
            eval_world (dict): The world where the imposition is evaluated
            
        Returns:
            BoolRef: Z3 expression representing the falsity condition that B fails
                    to hold in some world resulting from imposing A on eval_world
        """
        sem = self.semantics
        N = sem.N
        x = z3.BitVec("f_imp_x", N)
        u = z3.BitVec("f_imp_u", N)
        return Exists(
            [x, u],
            z3.And(
                sem.extended_verify(x, leftarg, eval_world),
                sem.imposition(x, eval_world, u),
                sem.false_at(rightarg, u)),
            )


    def extended_verify(self, state, leftarg, rightarg, eval_world):
        """Defines verification conditions for imposition in the extended semantics.
        
        In the extended semantics, a state verifies (A \\imposition B) if and only if:
        1. It is the null state, and
        2. The imposition relation holds between A and B
        
        This implements the idea that imposition statements, when true, are verified
        by the null state since they express a purely logical relationship.
        
        Args:
            state (BitVecRef): The state being evaluated as a verifier
            leftarg (Sentence): The proposition being imposed (A)
            rightarg (Sentence): The consequent proposition (B)
            eval_world (dict): The world where the imposition is evaluated
            
        Returns:
            BoolRef: Z3 expression representing the verification condition
        """
        return z3.And(
            state == self.semantics.null_state,
            self.true_at(leftarg, rightarg, eval_world)
        )
    
    def extended_falsify(self, state, leftarg, rightarg, eval_world):
        """Defines falsification conditions for imposition in the extended semantics.
        
        In the extended semantics, a state falsifies (A \\imposition B) if and only if:
        1. It is the null state, and
        2. The imposition relation fails to hold between A and B
        
        This implements the idea that imposition statements, when false, are falsified
        by the null state since they express a purely logical relationship.
        
        Args:
            state (BitVecRef): The state being evaluated as a falsifier
            leftarg (Sentence): The proposition being imposed (A)
            rightarg (Sentence): The consequent proposition (B)
            eval_world (dict): The world where the imposition is evaluated
            
        Returns:
            BoolRef: Z3 expression representing the falsification condition
        """
        return z3.And(
            state == self.semantics.null_state,
            self.false_at(leftarg, rightarg, eval_world)
        )

    def find_verifiers_and_falsifiers(self, leftarg, rightarg, eval_world):
        """Finds the verifiers and falsifiers for an imposition relation between propositions.
        
        Takes two sentence objects as arguments and returns the verifiers and falsifiers
        for their imposition relation. For imposition (A \\imposition B), the relation is 
        verified by the null state if B is true in all worlds that result from imposing A's
        verifiers on the evaluation world. Otherwise it is falsified by the null state.
        
        Args:
            leftarg (Sentence): The proposition being imposed (A)
            rightarg (Sentence): The consequent proposition (B)
            eval_world (dict): The world where the imposition is evaluated
            
        Returns:
            tuple: A pair (verifiers, falsifiers) where:
                - verifiers (set): Contains null_state if A \\imposition B is true, empty otherwise
                - falsifiers (set): Contains null_state if A \\imposition B is false, empty otherwise
                
        Raises:
            ValueError: If the imposition is neither true nor false at the evaluation world
        """
        evaluate = leftarg.proposition.model_structure.z3_model.evaluate
        if bool(evaluate(self.true_at(leftarg, rightarg, eval_world))):
            return {self.semantics.null_state}, set()
        if bool(evaluate(self.false_at(leftarg, rightarg, eval_world))):
            return set(), {self.semantics.null_state}
        raise ValueError(
            f"{leftarg.name} {self.name} {rightarg.name} "
            f"is neither true nor false in the world {eval_world}."
        )
    
    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """
        For modal and counterfactual operators, this method:
        1. Prints the full proposition at the current evaluation point
        2. Prints the antecedent's evaluation at the current world
        3. Prints the consequent's at all alternative worlds being considered
        4. Uses increased indentation to show the nested structure
        
        Args:
            sentence_obj (Sentence): The sentence object containing the proposition
            eval_point (dict): The point of evaluation (typically a world)
            indent_num (int): The current indentation level for formatting output
            use_colors (bool): Whether to use ANSI color codes in output
        """
        is_outcome = self.semantics.calculate_outcome_worlds
        model_structure = sentence_obj.proposition.model_structure
        left_argument_obj = sentence_obj.original_arguments[0]
        left_argument_verifiers = left_argument_obj.proposition.verifiers
        alt_worlds = is_outcome(left_argument_verifiers, eval_world, model_structure)
        self.print_over_worlds(sentence_obj, eval_world, alt_worlds, indent_num, use_colors)




##############################################################################
########################### INTENSIONAL OPERATORS ############################
##############################################################################

class NecessityOperator(syntactic.Operator):
    """Implementation of the necessity/universal modality (□).
    
    This operator represents the modal necessity 'it is necessarily the case that',
    often written as □A. The semantics involves quantifying over all possible worlds
    in the model and checking if A is true in all of them.
    
    The truth conditions state that □A is true at a world w if A is true in all
    possible worlds whatsoever.
    
    Class Attributes:
        name (str): Symbol representing necessity ("\\Box")
        arity (int): Number of arguments (1)
    """
    name = "\\Box"
    arity = 1

    def true_at(self, argument, eval_point):
        """Defines truth conditions for necessity at an evaluation point.
        
        The necessity □A is true at an evaluation point if and only if
        A is true at every possible world in the model.
        
        Args:
            argument (Sentence): The sentence being necessitated (A)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the truth condition that A holds
                    in all possible worlds
        """
        sem = self.semantics
        u = z3.BitVec("t_nec_u", sem.N)
        return ForAll(
            u,
            z3.Implies(
                sem.is_world(u),
                sem.true_at(argument, u),
            ),
        )
    
    def false_at(self, argument, eval_point):
        """Defines falsity conditions for necessity at an evaluation point.
        
        The necessity □A is false at an evaluation point if and only if
        A is false at some possible world in the model.
        
        Args:
            argument (Sentence): The sentence being necessitated (A)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the falsity condition that A fails
                    to hold in at least one possible world
        """
        sem = self.semantics
        u = z3.BitVec("t_nec_u", sem.N)
        return Exists(
            u,
            z3.And(
                sem.is_world(u),
                sem.false_at(argument, u),
            ),
        )
    
    def extended_verify(self, state, argument, eval_point):
        """Defines verification conditions for necessity in the extended semantics.
        
        In the extended semantics, a state verifies □A if and only if:
        1. It is the null state, and
        2. A is true in all possible worlds
        
        This implements the idea that necessity statements, when true, are verified
        by the null state since they express a purely logical relationship.
        
        Args:
            state (BitVecRef): The state being evaluated as a verifier
            argument (Sentence): The sentence being necessitated (A)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the verification condition
        """
        return z3.And(
            state == self.semantics.null_state,
            self.true_at(argument, eval_point)
        )
    
    def extended_falsify(self, state, argument, eval_point):
        """Defines falsification conditions for necessity in the extended semantics.
        
        In the extended semantics, a state falsifies □A if and only if:
        1. It is the null state, and
        2. A is false in at least one possible world
        
        This implements the idea that necessity statements, when false, are falsified
        by the null state since they express a purely logical relationship.
        
        Args:
            state (BitVecRef): The state being evaluated as a falsifier
            argument (Sentence): The sentence being necessitated (A)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            BoolRef: Z3 expression representing the falsification condition
        """
        return z3.And(
            state == self.semantics.null_state,
            self.false_at(argument, eval_point)
        )

    def find_verifiers_and_falsifiers(self, argument, eval_point):
        """Finds the verifiers and falsifiers for a necessity statement.
        
        For necessity □A, the statement is verified by the null state if A is true
        in all possible worlds, and falsified by the null state if A is false in
        at least one possible world. This implements the idea that necessity statements,
        when true or false, are verified/falsified by the null state since they
        express purely logical relationships.
        
        Args:
            argument (Sentence): The sentence being necessitated (A)
            eval_point (dict): The point of evaluation (typically a world)
            
        Returns:
            tuple: A pair (verifiers, falsifiers) where:
                - verifiers (set): Contains null_state if □A is true, empty otherwise
                - falsifiers (set): Contains null_state if □A is false, empty otherwise
                
        Raises:
            ValueError: If the necessity statement is neither true nor false at the evaluation point
        """
        evaluate = argument.proposition.model_structure.z3_model.evaluate
        if bool(evaluate(self.true_at(argument, eval_point))):
            return {self.semantics.null_state}, set()
        if bool(evaluate(self.false_at(argument, eval_point))):
            return set(), {self.semantics.null_state}
        raise ValueError(
            f"{self.name} {argument} "
            f"is neither true nor false in the world {eval_point}."
        )
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """
        For modal and counterfactual operators, this method:
        1. Prints the full proposition at the current evaluation point
        2. Prints the antecedent's evaluation at the current world
        3. Prints the consequent's at all alternative worlds being considered
        4. Uses increased indentation to show the nested structure
        
        Args:
            sentence_obj (Sentence): The sentence object containing the proposition
            eval_point (dict): The point of evaluation (typically a world)
            indent_num (int): The current indentation level for formatting output
            use_colors (bool): Whether to use ANSI color codes in output
        """
        all_worlds = sentence_obj.proposition.model_structure.z3_world_states
        self.print_over_worlds(sentence_obj, eval_point, all_worlds, indent_num, use_colors)


##############################################################################
######################## DEFINED EXTENSIONAL OPERATORS #######################
##############################################################################

class ConditionalOperator(syntactic.DefinedOperator):
    """Implementation of material implication/conditional (→).
    
    This operator represents the material conditional 'if A then B', defined as
    ¬A ∨ B. It is true when either A is false or B is true (or both).
    
    As a defined operator, it has no direct semantic implementation but instead
    derives its semantics from its definition in terms of more basic operators.
    
    Class Attributes:
        name (str): Symbol representing material implication ("\\rightarrow")
        arity (int): Number of arguments (2)
        primitive (bool): Always False for defined operators
    """

    name = "\\rightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg): # type: ignore
        """Defines the material conditional A → B as ¬A ∨ B.
        
        The material conditional is defined in terms of more basic operators:
        negation and disjunction. A → B is equivalent to ¬A ∨ B, meaning
        the conditional is true when either A is false or B is true.
        
        Args:
            leftarg: The antecedent of the conditional (A)
            rightarg: The consequent of the conditional (B)
            
        Returns:
            list: A nested list structure representing ¬A ∨ B in terms of
                 primitive operators OrOperator and NegationOperator
        """
        return [OrOperator, [NegationOperator, leftarg], rightarg]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the bottom element with proper indentation and formatting.
        
        Args:
            sentence_obj (Sentence): The sentence object containing the proposition
            eval_point (dict): The point of evaluation (typically a world)
            indent_num (int): The current indentation level
            use_colors (bool): Whether to use colored output for formatting
        """
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class BiconditionalOperator(syntactic.DefinedOperator):
    """Implementation of material biconditional/equivalence (↔).
    
    This operator represents the material biconditional 'A if and only if B',
    defined as (A → B) ∧ (B → A). It is true when A and B have the same truth value
    (either both true or both false).
    
    As a defined operator, it has no direct semantic implementation but instead
    derives its semantics from its definition in terms of more basic operators.
    
    Class Attributes:
        name (str): Symbol representing material biconditional ("\\leftrightarrow")
        arity (int): Number of arguments (2)
        primitive (bool): Always False for defined operators
    """

    name = "\\leftrightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg): # type: ignore
        """Defines the material biconditional A ↔ B as (A → B) ∧ (B → A).
        
        The material biconditional is defined in terms of more basic operators:
        conjunction and material implication. A ↔ B is equivalent to 
        (A → B) ∧ (B → A), meaning the biconditional is true when A and B
        have the same truth value.
        
        Args:
            leftarg: The left argument of the biconditional (A)
            rightarg: The right argument of the biconditional (B)
            
        Returns:
            list: A nested list structure representing (A → B) ∧ (B → A) in terms of
                 primitive operators AndOperator and ConditionalOperator
        """
        right_to_left = [ConditionalOperator, leftarg, rightarg]
        left_to_right = [ConditionalOperator, rightarg, leftarg]
        return [AndOperator, right_to_left, left_to_right]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the bottom element with proper indentation and formatting.
        
        Args:
            sentence_obj (Sentence): The sentence object containing the proposition
            eval_point (dict): The point of evaluation (typically a world)
            indent_num (int): The current indentation level
            use_colors (bool): Whether to use colored output for formatting
        """
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


##############################################################################
###################### DEFINED COUNTERFACTUAL OPERATORS ######################
##############################################################################

class MightCounterfactualOperator(syntactic.DefinedOperator):
    """Implementation of the 'might counterfactual' operator (◇→).
    
    This operator represents 'if A were the case, B might be the case', defined as
    ¬(A □→ ¬B). It is true when there exists at least one A-world where B is true.
    
    As a defined operator, it derives its semantics from the definition in terms
    of the counterfactual operator and negation.
    
    Class Attributes:
        name (str): Symbol representing the might counterfactual ("\\diamondright")
        arity (int): Number of arguments (2)
        primitive (bool): Always False for defined operators
    """

    name = "\\diamondright"
    arity = 2

    def derived_definition(self, leftarg, rightarg): # type: ignore
        """Defines the might counterfactual A ◇→ B as ¬(A □→ ¬B).
        
        The might counterfactual is defined in terms of more basic operators:
        negation and the counterfactual conditional. A ◇→ B is equivalent to
        ¬(A □→ ¬B), meaning there exists at least one A-world where B is true.
        
        Args:
            leftarg: The antecedent of the might counterfactual (A)
            rightarg: The consequent of the might counterfactual (B)
            
        Returns:
            list: A nested list structure representing ¬(A □→ ¬B) in terms of
                 primitive operators NegationOperator and CounterfactualOperator
        """
        return [
            NegationOperator, [
                CounterfactualOperator,
                leftarg,
                [NegationOperator, rightarg]
            ]
        ]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """
        For modal and counterfactual operators, this method:
        1. Prints the full proposition at the current evaluation point
        2. Prints the antecedent's evaluation at the current world
        3. Prints the consequent's at all alternative worlds being considered
        4. Uses increased indentation to show the nested structure
        
        Args:
            sentence_obj (Sentence): The sentence object containing the proposition
            eval_point (dict): The point of evaluation (typically a world)
            indent_num (int): The current indentation level for formatting output
            use_colors (bool): Whether to use ANSI color codes in output
        """
        is_alt = self.semantics.calculate_alternative_worlds
        model_structure = sentence_obj.proposition.model_structure
        left_argument_obj = sentence_obj.original_arguments[0]
        left_argument_verifiers = left_argument_obj.proposition.verifiers
        alt_worlds = is_alt(left_argument_verifiers, eval_point, model_structure)
        self.print_over_worlds(sentence_obj, eval_point, alt_worlds, indent_num, use_colors)


class MightImpositionOperator(syntactic.DefinedOperator):
    """Implementation of the 'might imposition' operator.
    
    This operator represents 'if A were imposed, B might be the case', defined as
    ¬(A \\imposition ¬B). It is true when there exists at least one outcome of
    imposing A where B is true.
    
    As a defined operator, it derives its semantics from the definition in terms
    of the imposition operator and negation.
    
    Class Attributes:
        name (str): Symbol representing the might imposition (\\could)
        arity (int): Number of arguments (2)
        primitive (bool): Always False for defined operators
    """

    name = "\\could"
    arity = 2

    def derived_definition(self, leftarg, rightarg): # type: ignore
        """Defines the might imposition A \\could B as ¬(A \\imposition ¬B).
        
        The might imposition is defined in terms of more basic operators:
        negation and the imposition operator. A \\could B is equivalent to
        ¬(A \\imposition ¬B), meaning there exists at least one outcome of
        imposing A where B is true.
        
        Args:
            leftarg: The proposition being imposed (A)
            rightarg: The consequent proposition (B)
            
        Returns:
            list: A nested list structure representing ¬(A \\imposition ¬B) in terms of
                 primitive operators NegationOperator and ImpositionOperator
        """
        return [
            NegationOperator, [
                ImpositionOperator,
                leftarg,
                [NegationOperator, rightarg]
            ]
        ]

    def print_method(self, sentence_obj, eval_world, indent_num, use_colors):
        """
        For modal and counterfactual operators, this method:
        1. Prints the full proposition at the current evaluation point
        2. Prints the antecedent's evaluation at the current world
        3. Prints the consequent's at all alternative worlds being considered
        4. Uses increased indentation to show the nested structure
        
        Args:
            sentence_obj (Sentence): The sentence object containing the proposition
            eval_point (dict): The point of evaluation (typically a world)
            indent_num (int): The current indentation level for formatting output
            use_colors (bool): Whether to use ANSI color codes in output
        """
        is_outcome = self.semantics.calculate_outcome_worlds
        model_structure = sentence_obj.proposition.model_structure
        left_argument_obj = sentence_obj.original_arguments[0]
        left_argument_verifiers = left_argument_obj.proposition.verifiers
        alt_worlds = is_outcome(left_argument_verifiers, eval_world, model_structure)
        self.print_over_worlds(sentence_obj, eval_world, alt_worlds, indent_num, use_colors)



##############################################################################
####################### DEFINED INTENSIONAL OPERATORS ########################
##############################################################################

class PossibilityOperator(syntactic.DefinedOperator):
    """Implementation of the possibility/existential modality (◇).
    
    This operator represents the modal possibility 'it is possibly the case that',
    often written as ◇A. It is defined as ¬□¬A, meaning 'it is not necessarily the case
    that not-A'.
    
    The truth conditions (derived from its definition) state that ◇A is true at a world w
    if A is true in at least one possible world accessible from w.
    
    Class Attributes:
        name (str): Symbol representing possibility ("\\Diamond")
        arity (int): Number of arguments (1)
        primitive (bool): Always False for defined operators
    """

    name = "\\Diamond"
    arity = 1

    def derived_definition(self, argument): # type: ignore
        """Defines the possibility operator ◇A as ¬□¬A.
        
        The possibility operator is defined in terms of more basic operators:
        negation and necessity. ◇A is equivalent to ¬□¬A, meaning 'it is not
        necessarily the case that not-A', or equivalently, 'A is true in at
        least one possible world'.
        
        Args:
            arg: The argument of the possibility operator (A)
            
        Returns:
            list: A nested list structure representing ¬□¬A in terms of
                 primitive operators NegationOperator and NecessityOperator
        """
        return [NegationOperator, [NecessityOperator, [NegationOperator, argument]]]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """
        For modal and counterfactual operators, this method:
        1. Prints the full proposition at the current evaluation point
        2. Prints the antecedent's evaluation at the current world
        3. Prints the consequent's at all alternative worlds being considered
        4. Uses increased indentation to show the nested structure
        
        Args:
            sentence_obj (Sentence): The sentence object containing the proposition
            eval_point (dict): The point of evaluation (typically a world)
            indent_num (int): The current indentation level for formatting output
            use_colors (bool): Whether to use ANSI color codes in output
        """
        all_worlds = sentence_obj.proposition.model_structure.z3_world_states
        self.print_over_worlds(sentence_obj, eval_point, all_worlds, indent_num, use_colors)


class CFNecessityOperator(syntactic.DefinedOperator):
    """Implementation of the counterfactual necessity operator.
    
    This operator represents 'it is counterfactually necessary that', defined as
    ⊤ □→ A. It is true when A holds in all ⊤-alternatives to the evaluation world
    (which amounts to all worlds).
    
    As a defined operator, it derives its semantics from the definition in terms
    of the counterfactual operator and the top operator.
    
    Class Attributes:
        name (str): Symbol representing counterfactual necessity ("\\CFBox")
        arity (int): Number of arguments (1)
        primitive (bool): Always False for defined operators
    """

    name = "\\CFBox"
    arity = 1

    def derived_definition(self, argument): # type: ignore
        """Defines the counterfactual necessity operator □_CF A as ⊤ □→ A.
        
        The counterfactual necessity operator is defined in terms of more basic operators:
        the counterfactual conditional and the top operator. □_CF A is equivalent to
        ⊤ □→ A, meaning 'if anything were the case (which it always is), A would be the case'.
        
        Args:
            argument: The argument of the counterfactual necessity operator (A)
            
        Returns:
            list: A nested list structure representing ⊤ □→ A in terms of
                 primitive operators CounterfactualOperator and TopOperator
        """
        return [CounterfactualOperator, [TopOperator], argument]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """
        For modal and counterfactual operators, this method:
        1. Prints the full proposition at the current evaluation point
        2. Prints the antecedent's evaluation at the current world
        3. Prints the consequent's at all alternative worlds being considered
        4. Uses increased indentation to show the nested structure
        
        Args:
            sentence_obj (Sentence): The sentence object containing the proposition
            eval_point (dict): The point of evaluation (typically a world)
            indent_num (int): The current indentation level for formatting output
            use_colors (bool): Whether to use ANSI color codes in output
        """
        is_alt = self.semantics.calculate_alternative_worlds
        model_structure = sentence_obj.proposition.model_structure
        left_argument_obj = sentence_obj.original_arguments[0]
        left_argument_verifiers = left_argument_obj.proposition.verifiers
        alt_worlds = is_alt(left_argument_verifiers, eval_point, model_structure)
        self.print_over_worlds(sentence_obj, eval_point, alt_worlds, indent_num, use_colors)

class CFPossibilityOperator(syntactic.DefinedOperator):
    """Implementation of the counterfactual possibility operator.
    
    This operator represents 'it is counterfactually possible that', defined as
    ⊤ ◇→ A. It is true when A holds in at least one ⊤-alternative to the evaluation world
    (which amounts to some possible world).
    
    As a defined operator, it derives its semantics from the definition in terms
    of the might counterfactual operator and the top operator.
    
    Class Attributes:
        name (str): Symbol representing counterfactual possibility ("\\CFDiamond")
        arity (int): Number of arguments (1)
        primitive (bool): Always False for defined operators
    """

    name = "\\CFDiamond"
    arity = 1

    def derived_definition(self, argument): # type: ignore
        """Defines the counterfactual possibility operator ◇_CF A as ⊤ ◇→ A.
        
        The counterfactual possibility operator is defined in terms of more basic operators:
        the might counterfactual operator and the top operator. ◇_CF A is equivalent to
        ⊤ ◇→ A, meaning 'if anything were the case (which it always is), A might be the case'.
        
        Args:
            argument: The argument of the counterfactual possibility operator (A)
            
        Returns:
            list: A nested list structure representing ⊤ ◇→ A in terms of
                 primitive operators MightCounterfactualOperator and TopOperator
        """
        return [MightCounterfactualOperator, [TopOperator], argument]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """
        For modal and counterfactual operators, this method:
        1. Prints the full proposition at the current evaluation point
        2. Prints the antecedent's evaluation at the current world
        3. Prints the consequent's at all alternative worlds being considered
        4. Uses increased indentation to show the nested structure
        
        Args:
            sentence_obj (Sentence): The sentence object containing the proposition
            eval_point (dict): The point of evaluation (typically a world)
            indent_num (int): The current indentation level for formatting output
            use_colors (bool): Whether to use ANSI color codes in output
        """
        is_alt = self.semantics.calculate_alternative_worlds
        model_structure = sentence_obj.proposition.model_structure
        left_argument_obj = sentence_obj.original_arguments[0]
        left_argument_verifiers = left_argument_obj.proposition.verifiers
        alt_worlds = is_alt(left_argument_verifiers, eval_point, model_structure)
        self.print_over_worlds(sentence_obj, eval_point, alt_worlds, indent_num, use_colors)


default_operators = syntactic.OperatorCollection(
    # primitive extensional operators
    NegationOperator,
    AndOperator,
    OrOperator,

    # primitive extremal operators
    TopOperator,
    BotOperator,

    # primitive constitutive operators
    IdentityOperator,
    GroundOperator,
    EssenceOperator,
    RelevanceOperator,
    
    # primitive counterfactual operators
    CounterfactualOperator,
    ImpositionOperator,

    # primitive modal operators
    NecessityOperator,

    # defined extensional operators
    ConditionalOperator,
    BiconditionalOperator,

    # defined counterfactual operators
    MightCounterfactualOperator,
    MightImpositionOperator,

    # defined modal operators
    PossibilityOperator,
    CFNecessityOperator,
    CFPossibilityOperator,
)

