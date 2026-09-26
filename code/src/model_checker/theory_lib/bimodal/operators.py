"""Implements the operators for bimodal logic in the model checker.

This module provides implementations of various logical operators used in bimodal logic,
which combines temporal and modal reasoning. The operators are organized into several
categories based on their semantic role:

Extensional Operators:
    - NegationOperator (¬): Logical negation
    - AndOperator (∧): Logical conjunction
    - OrOperator (∨): Logical disjunction
    - ConditionalOperator (→): Material implication (defined)
    - BiconditionalOperator (↔): Material biconditional (defined)

Extremal Operators:
    - BotOperator (⊥): Logical contradiction/falsity
    - TopOperator (⊤): Logical tautology/truth (defined)

Modal Operators:
    - NecessityOperator (□): Truth in all possible worlds
    - DefPossibilityOperator (◇): Truth in at least one possible world (defined)

Temporal Operators:
    - FutureOperator (⏵): Truth at all future times
    - PastOperator (⏴): Truth at all past times
    - UntilOperator (U): Event holds at future time with guard in between
    - SinceOperator (S): Event held at past time with guard in between
    - DefFutureOperator: Possibility of future truth (defined)
    - DefPastOperator: Possibility of past truth (defined)

## Change of meaning (witness-family certificate redesign)

Every primitive operator's `true_at`/`false_at` used to build a quantified Z3 formula
(`ForAll`/`Exists` over world IDs or time, via `_fresh_bound_int`-suffixed bound variables to
avoid the aliasing hazard documented below). That machinery is retired outright (see
`semantic/core.py`'s own module docstring): the certificate encoding is quantifier-free, and
truth values are label-membership lookups (D5). **Each primitive operator's `true_at` now
mirrors its own case in `semantic/formula.py`'s `translate` dispatch** (report 01 section 4.4:
"each primitive operator carries its translation rule and its `true_at`/`false_at` as bit
lookup") -- reconstructing the `Formula` its own combinator produces from its
already-translated arguments, then looking up
`self.semantics.witness_registry.bit(eval_point["lasso"], eval_point["position"], formula)`.
This is not a second, independently-maintained copy of `translate`'s dispatch table: each
operator mirrors only its own single case, exactly as `translate` already states it, so there is
one rule per operator, asserted in exactly two places by construction (not two independently
evolving encodings of the same rule).

`NegationOperator`/`AndOperator`/`OrOperator` needed **no change at all**: their `true_at`/
`false_at` already delegate recursively to `self.semantics.true_at`/`false_at` on their
arguments, which is D5's translate-then-lookup contract already, and their `find_truth_condition`
already only manipulates the generic `{key: (true_positions, false_positions)}` shape
`BimodalProposition.extension` still uses (Phase 11) -- nothing here inspects a `world_id`'s
*meaning*, only its role as a dict key, so nothing broke. `BotOperator`, `NecessityOperator`
(`\\Box`), `FutureOperator`, `PastOperator`, `UntilOperator`, and `SinceOperator` did need
rewriting: they built quantified Z3 formulas or read `eval_point["world"]`/`eval_point["time"]`
directly, both retired.

**`find_truth_condition` is deleted from every primitive operator.** Nothing calls it any more:
`BimodalProposition.find_extension` (Phase 11) computes truth values directly from certificate
labels, not by recursing through operators. Retaining a method nobody calls, referencing
attributes (`self.semantics.M`, `self.semantics.world_time_intervals`,
`self.semantics.all_false`) that no longer exist, would be dead, actively misleading code, not a
harmless leftover.

**Every `print_method` now delegates to `self.general_print`** (the base `syntactic.Operator`
method, unchanged and already eval-point-shape-agnostic: it prints the sentence's own
proposition, then recurses into each argument sentence at the *same* `eval_point`).
`print_over_worlds`/`print_over_times` (also base-class, shared across theories) are retired
from every call site here: they read `eval_point["world"]`/`["time"]` and bitvector-specific
display logic that has no analogue for `(lasso, position)` points, and the certificate's own
boxed-subformula table (`semantic/model.py`'s `print_certificate`, Phase 13) already gives box
guesses and false-box witnesses their own dedicated display -- there is no remaining need for a
per-operator "show me this argument evaluated at every alternative world/time" listing.

The defined operators (`\\rightarrow`, `\\leftrightarrow`, `\\top`, `\\Diamond`, `\\future`,
`\\past`, `\\next`, `\\prev`) keep their `derived_definition`s completely unchanged -- they
already reduce to primitives before `translate` (or any operator's own `true_at`) ever sees them
-- and only needed their `print_method`s updated to `general_print` for the same reason as the
primitives.

**The process-global bound-variable counter (`_fresh_bound_int`/`reset_bound_var_counter`) is
deleted along with the last `ForAll`/`Exists` construction it existed to protect** -- see
`semantic/core.py`'s `_reset_global_state`, which no longer calls `reset_bound_var_counter`
(this was the last consumer).

All operators adhere to a fail-fast philosophy, raising explicit errors when
required data is missing or invalid rather than attempting fallbacks.
"""

from model_checker import z3_shim as z3

from model_checker import syntactic

from .semantic.formula import Bot, Box, Imp, Snce, Untl, translate


def _bit(semantics, eval_point, formula):
    """Look up `formula`'s label bit at `eval_point` (D5's translate-then-lookup contract),
    shared by every primitive operator's `true_at` below."""
    return semantics.witness_registry.bit(eval_point["lasso"], eval_point["position"], formula)


##############################################################################
############################ EXTENSIONAL OPERATORS ###########################
##############################################################################

class NegationOperator(syntactic.Operator):
    """Logical negation operator that inverts the truth value of its argument.

    This operator implements classical logical negation (¬). When applied to a formula A,
    it returns true when A is false and false when A is true.

    Key Properties:
        - Involutive: ¬¬A ≡ A
        - Preserves excluded middle: A ∨ ¬A is a tautology
        - Preserves non-contradiction: ¬(A ∧ ¬A) is a tautology
        - Extensional: Value depends only on truth value of argument

    Example:
        If p means "it's raining", then ¬p means "it's not raining"
    """

    name = "\\neg"
    arity = 1

    def true_at(self, argument, eval_point):
        """Returns true if argument is false."""
        return self.semantics.false_at(argument, eval_point)

    def false_at(self, argument, eval_point):
        """Returns false if argument is true."""
        return self.semantics.true_at(argument, eval_point)

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class AndOperator(syntactic.Operator):
    """Logical conjunction operator that returns true when both arguments are true.

    This operator implements classical logical conjunction (∧). When applied to formulas
    A and B, it returns true when both A and B are true, and false otherwise.

    Key Properties:
        - Commutative: A ∧ B ≡ B ∧ A
        - Associative: (A ∧ B) ∧ C ≡ A ∧ (B ∧ C)
        - Identity: A ∧ ⊤ ≡ A
        - Annihilator: A ∧ ⊥ ≡ ⊥
        - Idempotent: A ∧ A ≡ A
        - Extensional: Value depends only on truth values of arguments

    Example:
        If p means "it's raining" and q means "it's cold", then (p ∧ q) means
        "it's raining and it's cold"
    """

    name = "\\wedge"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Returns true if both arguments are true."""
        semantics = self.semantics
        return z3.And(
            semantics.true_at(leftarg, eval_point),
            semantics.true_at(rightarg, eval_point)
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Returns true if either argument is false."""
        semantics = self.semantics
        return z3.Or(
            semantics.false_at(leftarg, eval_point),
            semantics.false_at(rightarg, eval_point)
        )

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class OrOperator(syntactic.Operator):
    """Logical disjunction operator that returns true when at least one argument is true.

    This operator implements classical logical disjunction (∨). When applied to formulas
    A and B, it returns true when either A or B (or both) are true, and false otherwise.

    Key Properties:
        - Commutative: A ∨ B ≡ B ∨ A
        - Associative: (A ∨ B) ∨ C ≡ A ∨ (B ∨ C)
        - Identity: A ∨ ⊥ ≡ A
        - Annihilator: A ∨ ⊤ ≡ ⊤
        - Idempotent: A ∨ A ≡ A
        - Extensional: Value depends only on truth values of arguments

    Example:
        If p means "it's raining" and q means "it's cold", then (p ∨ q) means
        "it's raining or it's cold (or both)"
    """

    name = "\\vee"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Returns true if either argument is true."""
        semantics = self.semantics
        return z3.Or(
            semantics.true_at(leftarg, eval_point),
            semantics.true_at(rightarg, eval_point)
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Returns true if both arguments are false."""
        semantics = self.semantics
        return z3.And(
            semantics.false_at(leftarg, eval_point),
            semantics.false_at(rightarg, eval_point)
        )

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


##############################################################################
############################## EXTREMAL OPERATORS ############################
##############################################################################

class BotOperator(syntactic.Operator):
    """Bottom element of the space of propositions is false at all worlds and times.

    This operator implements logical falsity (⊥). It evaluates to false at every world
    and time point in the model structure.

    Key Properties:
        - Always evaluates to false regardless of context
        - Identity element for disjunction: ⊥ ∨ A ≡ A
        - Annihilator for conjunction: ⊥ ∧ A ≡ ⊥
        - Negation gives top: ¬⊥ ≡ ⊤

    Under the certificate encoding, `⊥`'s label bit is forced false at every position by
    local coherence itself (`witness_constraints.py`'s coherence clause for `Bot`:
    `Not(bit(lasso, t, Bot()))`) -- `true_at` looks it up rather than hard-coding `False`
    directly, so a corrupted encoding that failed to assert that clause would surface as an
    unconstrained (not silently-correct) variable.

    Example:
        ⊥ represents a logical contradiction like "it's raining and not raining"
    """

    name = "\\bot"
    arity = 0

    def true_at(self, eval_point):
        """Looks up `Bot()`'s label bit -- forced false by local coherence."""
        return _bit(self.semantics, eval_point, Bot())

    def false_at(self, eval_point):
        """`Not(true_at(...))`."""
        return z3.Not(self.true_at(eval_point))

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


##############################################################################
############################## MODAL OPERATORS ###############################
##############################################################################

class NecessityOperator(syntactic.Operator):
    """Modal operator that evaluates whether a formula holds in all possible worlds.

    This operator implements 'it is necessary that'. Under the certificate encoding, "all
    possible worlds" means every certified history (every lasso in the found `WitnessFamily`)
    at every position -- exactly what (C3) box faithfulness certifies (`docs/ADEQUACY.md`
    Corollary 2.2: the certificate's lassos and their translates are exactly `H_F`).

    Key Properties:
        - Dual of possibility: □A ≡ ¬◇¬A
        - `true_at`/`false_at` are a direct lookup of the box guess `bx(translate(argument))`
          mirroring `translate`'s own `\\Box` case (`Box(translate(a))`) -- the guess variable
          itself, not a fresh quantifier, is what (C3)'s constraints (Phase 8) tie to "true in
          every lasso" / "false in some lasso, somewhere".

    Example:
        If p means "it's raining", then □p means "it is necessarily raining"
        (true in every certified history).
    """
    name = "\\Box"
    arity = 1

    def true_at(self, argument, eval_point):
        """Looks up the label bit of `Box(translate(argument))` -- mirrors `translate`'s own
        `\\Box` rule (`semantic/formula.py`)."""
        formula = Box(translate(argument))
        return _bit(self.semantics, eval_point, formula)

    def false_at(self, argument, eval_point):
        """`Not(true_at(...))`."""
        return z3.Not(self.true_at(argument, eval_point))

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments. The boxed-subformula table
        (`semantic/model.py`'s `print_certificate`) is where a false box's witness history
        and position are shown; this method only prints `\\Box A`'s own truth value at
        `eval_point`."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


##############################################################################
############################## TENSE OPERATORS ###############################
##############################################################################

class FutureOperator(syntactic.Operator):
    """Temporal operator that evaluates whether a formula holds at all future times.

    This operator implements 'it will always be the case that' (G). Mirrors `translate`'s
    own `\\Future` rule: `G A := ¬(⊤ U ¬A)` (`semantic/formula.py`) -- `\\Future` is the
    "always" primitive, not "eventually" (that is the defined `\\future`, `DefFutureOperator`
    below).

    Example:
        If p means "it's raining", then ⏵p means "it will always be raining"
        (true at every future position of the certified history).
    """
    name = "\\Future"
    arity = 1

    def true_at(self, argument, eval_point):
        """Looks up the label bit of `¬(⊤ U ¬argument)` -- mirrors `translate`'s own
        `\\Future` rule."""
        top = Imp(Bot(), Bot())
        formula = Imp(Untl(top, Imp(translate(argument), Bot())), Bot())
        return _bit(self.semantics, eval_point, formula)

    def false_at(self, argument, eval_point):
        """`Not(true_at(...))`."""
        return z3.Not(self.true_at(argument, eval_point))

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class PastOperator(syntactic.Operator):
    """Temporal operator that evaluates whether an argument holds at all past times.

    This operator implements 'it has always been the case that' (H). Mirrors `translate`'s
    own `\\Past` rule: `H A := ¬(⊤ S ¬A)` (`semantic/formula.py`).

    Example:
        If p means "it's raining", then ⏴p means "it has always been raining"
        (true at every past position of the certified history).
    """
    name = "\\Past"
    arity = 1

    def true_at(self, argument, eval_point):
        """Looks up the label bit of `¬(⊤ S ¬argument)` -- mirrors `translate`'s own
        `\\Past` rule."""
        top = Imp(Bot(), Bot())
        formula = Imp(Snce(top, Imp(translate(argument), Bot())), Bot())
        return _bit(self.semantics, eval_point, formula)

    def false_at(self, argument, eval_point):
        """`Not(true_at(...))`."""
        return z3.Not(self.true_at(argument, eval_point))

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class UntilOperator(syntactic.Operator):
    """Temporal operator U(guard, event): event holds at some future time s > t,
    and guard holds for all times in the open interval (t, s).

    **Guard-first**, matching the Lean development's `untl` constructor exactly (D2):
    `true_at(self, guard_arg, event_arg, eval_point)` is positional identity against
    `Untl`'s own `(guard, event)` field order. Mirrors `translate`'s own `\\Until` rule,
    which is likewise positional identity: `Untl(guard=translate(guard_arg),
    event=translate(event_arg))`. ModelChecker's own event-first order (citing the Burgess
    convention) has been retired in favor of this cross-repository uniformity; there is no
    longer a swap anywhere in this path.

    Key Properties:
        - Strict witness: the event time s must be strictly greater than evaluation time t
        - Open guard interval: guard holds for all r in (t, s), excluding both endpoints
        - Guard-first: U(guard, event) -- event is what eventually happens

    Example:
        If p means "waiting" and q means "the train arrives", then U(p, q) means
        "we are waiting until the train arrives"
    """

    name = "\\Until"
    arity = 2

    def true_at(self, guard_arg, event_arg, eval_point):
        """Looks up the label bit of `Untl(guard=translate(guard_arg),
        event=translate(event_arg))` -- mirrors `translate`'s own `\\Until` rule.
        Positional identity: no guard/event argument swap (D2)."""
        formula = Untl(guard=translate(guard_arg), event=translate(event_arg))
        return _bit(self.semantics, eval_point, formula)

    def false_at(self, guard_arg, event_arg, eval_point):
        """`Not(true_at(...))`."""
        return z3.Not(self.true_at(guard_arg, event_arg, eval_point))

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class SinceOperator(syntactic.Operator):
    """Temporal operator S(guard, event): event held at some past time s < t,
    and guard held for all times in the open interval (s, t).

    Guard-first, mirroring `UntilOperator`'s own convention and `translate`'s `\\Since`
    rule: positional identity, no guard/event argument swap (D2).

    Example:
        If p means "waiting" and q means "the announcement was made", then S(p, q) means
        "we had been waiting until the announcement was made"
    """

    name = "\\Since"
    arity = 2

    def true_at(self, guard_arg, event_arg, eval_point):
        """Looks up the label bit of `Snce(guard=translate(guard_arg),
        event=translate(event_arg))` -- mirrors `translate`'s own `\\Since` rule.
        Positional identity: no guard/event argument swap."""
        formula = Snce(guard=translate(guard_arg), event=translate(event_arg))
        return _bit(self.semantics, eval_point, formula)

    def false_at(self, guard_arg, event_arg, eval_point):
        """`Not(true_at(...))`."""
        return z3.Not(self.true_at(guard_arg, event_arg, eval_point))

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


##############################################################################
######################## DEFINED EXTENSIONAL OPERATORS ########################
##############################################################################

class ConditionalOperator(syntactic.DefinedOperator):
    """Material conditional operator that returns true unless the antecedent is true and consequent false.

    This operator implements classical material implication (→), defined as
    `A → B ≡ ¬A ∨ B`. `derived_definition` reduces it to primitives before any `true_at`
    (this operator's own, or any other's) ever sees it -- it has no `true_at`/`false_at` of
    its own, matching every other `DefinedOperator` in this module.

    Example:
        If p means "it's raining" and q means "the ground is wet", then (p → q) means
        "if it's raining then the ground is wet" (in the material sense)
    """

    name = "\\rightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):  # type: ignore
        return [OrOperator, [NegationOperator, leftarg], rightarg]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class BiconditionalOperator(syntactic.DefinedOperator):
    """Material biconditional operator that returns true when both arguments have the same truth value.

    This operator implements classical material biconditional (↔), defined as
    `A ↔ B ≡ (A → B) ∧ (B → A)`.

    Example:
        If p means "it's raining" and q means "there are clouds", then (p ↔ q) means
        "it's raining if and only if there are clouds" (in the material sense)
    """

    name = "\\leftrightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):  # type: ignore
        right_to_left = [ConditionalOperator, leftarg, rightarg]
        left_to_right = [ConditionalOperator, rightarg, leftarg]
        return [AndOperator, right_to_left, left_to_right]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


##############################################################################
####################### DEFINED EXTREMAL OPERATORS ###########################
##############################################################################

class TopOperator(syntactic.DefinedOperator):
    """Top element of the space of propositions is true at all worlds and times.

    This operator implements logical truth (⊤), defined as `⊤ ≡ ¬⊥`.

    Example:
        ⊤ represents a logical tautology like "it's raining or not raining"
    """

    name = "\\top"
    arity = 0

    def derived_definition(self):  # type: ignore
        """Define top in terms of negation and bottom."""
        return [NegationOperator, [BotOperator]]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


##############################################################################
####################### DEFINED INTENSIONAL OPERATORS ########################
##############################################################################

class DefPossibilityOperator(syntactic.DefinedOperator):
    """Modal operator that evaluates whether a formula holds in at least one possible world.

    This operator implements 'it is possible that', defined as the dual of necessity:
    `◇A ≡ ¬□¬A`.

    Example:
        If p means "it's raining", then ◇p means "it is possible that it's raining"
        (true in at least one certified history).
    """
    name = "\\Diamond"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
        """Define possibility in terms of negation and necessity."""
        return [NegationOperator, [NecessityOperator, [NegationOperator, argument]]]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


##############################################################################
######################### DEFINED TEMPORAL OPERATORS #########################
##############################################################################

class DefFutureOperator(syntactic.DefinedOperator):
    """Temporal operator that evaluates whether a formula holds at some future time.

    This operator implements 'it will at some point be the case that' (F), defined as the
    dual of `\\Future`'s "always" (G): `⏵A ≡ ¬⏵_G¬A`.

    Example:
        If p means "it's raining", then ⏵p means "it will at some point be raining"
        (true at some future position of the certified history).
    """

    name = "\\future"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
        return [NegationOperator, [FutureOperator, [NegationOperator, argument]]]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class DefPastOperator(syntactic.DefinedOperator):
    """Temporal operator that evaluates whether a formula held at some past time (P),
    defined as the dual of `\\Past`'s "always" (H): `⏴A ≡ ¬⏴_H¬A`."""

    name = "\\past"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
        return [NegationOperator, [PastOperator, [NegationOperator, argument]]]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class DefNextOperator(syntactic.DefinedOperator):
    """Temporal operator for 'next instant': true iff argument holds at the immediately next time.

    Defined as Next(phi) = U(bot, phi): bot (falsity) holds as the guard in the open interval
    (t, s), and phi holds as the event at some future time s > t. Since bot is never true, the
    interval (t, s) must be empty, meaning s is the immediately next time after t.
    """

    name = "\\next"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
        return [UntilOperator, [BotOperator], argument]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class DefPrevOperator(syntactic.DefinedOperator):
    """Temporal operator for 'previous instant': true iff argument held at the immediately prior time.

    Defined as Prev(phi) = S(bot, phi): bot (falsity) holds as the guard in the open interval
    (s, t), and phi held as the event at some past time s < t. Since bot is never true, the
    interval (s, t) must be empty, meaning s is the immediately previous time before t.
    """

    name = "\\prev"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
        return [SinceOperator, [BotOperator], argument]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


bimodal_operators = syntactic.OperatorCollection(
    # extensional operators
    NegationOperator,
    AndOperator,
    OrOperator,

    # extremal operators
    TopOperator,

    # modal operators
    NecessityOperator,

    # tense operators
    FutureOperator,
    PastOperator,
    UntilOperator,
    SinceOperator,

    # defined operators
    ConditionalOperator,
    BiconditionalOperator,
    BotOperator,
    DefPossibilityOperator,
    DefFutureOperator,
    DefPastOperator,
    DefNextOperator,
    DefPrevOperator,
)
