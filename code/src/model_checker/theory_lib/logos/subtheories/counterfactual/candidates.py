"""Candidate verification clauses for the counterfactual conditional.

The counterfactual operator in ``operators.py`` gives ``A \\boxright B`` the
verifier set ``{w}`` at evaluation world ``w``, so the proposition it
expresses changes with the point of evaluation.  This module adds one
operator per *context-free* candidate clause, each sharing the truth clause
of ``CounterfactualOperator`` verbatim and differing only in
``extended_verify`` / ``extended_falsify`` (the Z3 side) and
``find_verifiers_and_falsifiers`` (the Python side).  The operators live
alongside the original so that identical examples can be run under every
clause; ``frame_oracle.py`` states the same clauses over explicit frames.

Clauses, writing ``T(w)`` for "the counterfactual is true at world ``w``" and
``W`` for the world states:

- ``\\boxrightI`` (imposition-local): ``s`` verifies iff every ``A``-verifier
  imposed on ``s`` reaches only ``B``-worlds -- the truth clause with ``s``
  in the world slot.
- ``\\boxrightW`` (world-state): the fusion closure of ``{w in W : T(w)}``.
- ``\\boxrightL`` (settlers): ``{s : every world above s is a T-world}``.
- ``\\boxrightM`` (minimal settlers): the parthood-minimal settlers.
- ``\\boxrightMC`` (generated settlers): the fusion closure of the minimal
  settlers.
- ``\\boxrightIL`` (imposition-local settlers): ``V_I`` intersected with
  ``V_L``.

Falsifier clauses are the polarity duals.  Every ``\\diamondrightK`` is the
defined might-counterfactual ``\\neg (A \\boxrightK \\neg B)``.

Roster.  The Z3 operators implemented here are ``I`` (refuted control), the
baselines ``W`` and ``L``, and -- once the settled-imposition clauses land --
``ILC`` (fusion closure of ``IL``, the mechanical control), ``ILMC`` (fusion
closure of the parthood-minimal ``IL`` members, the primary candidate) and
``MC``.  The clauses ``IL``, ``ILM``, ``M``, ``SR``, ``SRC`` and the
exact-imposition family are stated oracle-only in ``frame_oracle.py`` and
populate the comparison tables; they have no Z3 operator.

Two encodings of ``T(w)`` are available on the Z3 side.  ``direct`` inlines
the truth clause for each concrete world; ``predicate`` allocates one Z3
function per (operator, antecedent, consequent) whose ``2^N`` defining
constraints are appended to the semantics' frame constraints, so a clause
nested in an antecedent refers to a small atom instead of re-expanding the
truth clause under every quantifier instance.  ``truth_encoding`` selects the
default; see ``TRUTH_ENCODING`` below.
"""

from typing import TYPE_CHECKING, Any, Callable, Dict, List, Optional, Set, Tuple

from model_checker import z3_shim as z3

from model_checker import syntactic
from ..extensional.operators import NegationOperator
from .operators import CounterfactualOperator, MightCounterfactualOperator

if TYPE_CHECKING:
    from model_checker.theory_lib.logos.semantic import LogosSemantics

DIRECT = "direct"
PREDICATE = "predicate"

#: Default Z3 encoding of the truth set used by the world-quantifying clauses.
TRUTH_ENCODING = DIRECT

_MEMO_ATTR = "_cf_candidate_memo"


def _memo(semantics: Any) -> Dict[Any, Any]:
    """Per-semantics cache of concrete-world subterms and truth predicates."""
    memo = getattr(semantics, _MEMO_ATTR, None)
    if memo is None:
        memo = {}
        setattr(semantics, _MEMO_ATTR, memo)
    return memo


def _concrete(state: Any) -> Optional[int]:
    """The integer value of a concrete bit-vector, or ``None`` when symbolic."""
    as_long = getattr(state, "as_long", None)
    return None if as_long is None else int(as_long())


class SolvedModelView:
    """Python-side view of one solved model for a counterfactual ``left □→ right``.

    States are integers; the truth set is computed from the antecedent's
    proposition (its Python-side verifiers), the semantics' ``is_alternative``
    evaluated in the model, and the recursive truth clause of the consequent,
    without consulting any candidate's Z3 verifier clause.
    """

    def __init__(self, semantics: Any, leftarg: Any, rightarg: Any) -> None:
        model = leftarg.proposition.model_structure
        evaluate = model.z3_model.evaluate
        self.model = model
        self.semantics = semantics
        self.states: List[int] = list(range(1 << semantics.N))
        self.bitvecs = model.all_states
        self.possible: Set[int] = {int(s.as_long()) for s in model.z3_possible_states}
        self.worlds: Set[int] = {int(w.as_long()) for w in model.z3_world_states}
        self.antecedent_verifiers: Set[int] = {int(v.as_long()) for v in leftarg.proposition.verifiers}
        self.consequent_true: Dict[int, bool] = {
            u: bool(evaluate(semantics.true_at(rightarg, {"world": self.bitvecs[u]})))
            for u in self.worlds
        }
        self.consequent_false: Dict[int, bool] = {
            u: bool(evaluate(semantics.false_at(rightarg, {"world": self.bitvecs[u]})))
            for u in self.worlds
        }
        self._alt_cache: Dict[Tuple[int, int], Set[int]] = {}
        self._evaluate = evaluate
        self.true_worlds: Set[int] = {w for w in self.worlds if self.cf_true(w)}
        self.false_worlds: Set[int] = {w for w in self.worlds if self.cf_false(w)}

    def alternatives(self, s: int, a: int) -> Set[int]:
        key = (s, a)
        if key not in self._alt_cache:
            is_alt = self.semantics.is_alternative
            bv = self.bitvecs
            self._alt_cache[key] = {
                u for u in self.worlds if bool(self._evaluate(is_alt(bv[u], bv[a], bv[s])))
            }
        return self._alt_cache[key]

    def cf_true(self, s: int) -> bool:
        """The truth clause with ``s`` in the world slot."""
        return all(
            self.consequent_true[u]
            for a in self.antecedent_verifiers
            for u in self.alternatives(s, a)
        )

    def cf_false(self, s: int) -> bool:
        return any(
            self.consequent_false[u]
            for a in self.antecedent_verifiers
            for u in self.alternatives(s, a)
        )

    def worlds_above(self, s: int) -> Set[int]:
        return {w for w in self.worlds if s & w == s}

    def settlers(self) -> Tuple[Set[int], Set[int]]:
        v = {s for s in self.states if all(w in self.true_worlds for w in self.worlds_above(s))}
        f = {s for s in self.states if all(w in self.false_worlds for w in self.worlds_above(s))}
        return v, f

    def imposition_local(self) -> Tuple[Set[int], Set[int]]:
        return (
            {s for s in self.states if self.cf_true(s)},
            {s for s in self.states if self.cf_false(s)},
        )

    def to_bitvecs(self, states: Set[int]) -> Set[Any]:
        return {self.bitvecs[s] for s in states}


def fusion_closure(states: Set[int]) -> Set[int]:
    """The fusions of nonempty subsets of ``states``."""
    closed = set(states)
    frontier = list(closed)
    while frontier:
        new = []
        for s in frontier:
            for t in list(closed):
                u = s | t
                if u not in closed:
                    closed.add(u)
                    new.append(u)
        frontier = new
    return closed


def minimal_elements(states: Set[int]) -> Set[int]:
    """The parthood-minimal members of ``states``."""
    return {s for s in states if not any(t != s and t & s == t for t in states)}


class CandidateCounterfactual(CounterfactualOperator):
    """Base class for the context-free candidate clauses.

    Subclasses set ``key`` and implement ``verifier_clause`` /
    ``falsifier_clause`` (Z3 side, taking an explicit encoding) and
    ``python_sets`` (Python side over a ``SolvedModelView``).  ``true_at``,
    ``false_at`` and ``print_method`` are inherited unchanged.
    """

    semantics: "LogosSemantics"
    key: str = ""
    truth_encoding: str = TRUTH_ENCODING

    # -- Z3-side building blocks ------------------------------------------

    def is_world_at(self, world: Any) -> Any:
        """``is_world(world)``, memoized for concrete worlds."""
        w = _concrete(world)
        if w is None:
            return self.semantics.is_world(world)
        memo = _memo(self.semantics)
        key = ("is_world", w)
        if key not in memo:
            memo[key] = self.semantics.is_world(world)
        return memo[key]

    def truth_predicate(self, leftarg: Any, rightarg: Any, eval_point: Dict[str, Any]) -> Any:
        """The Z3 function ``cf_true(w)`` for this pair, defined at every state.

        Created once per (operator, antecedent, consequent) and semantics
        instance; its ``2^N`` defining constraints are appended to
        ``semantics.frame_constraints`` on creation, which is only sound while
        constraints are still being collected (before solving).
        """
        semantics = self.semantics
        memo = _memo(semantics)
        key = ("predicate", self.name, leftarg.name, rightarg.name)
        if key not in memo:
            count = sum(1 for k in memo if k[0] == "predicate")
            predicate = z3.Function(
                f"cf_true_{self.key}_{count}", z3.BitVecSort(semantics.N), z3.BoolSort()
            )
            for w in semantics.all_states:
                semantics.frame_constraints.append(
                    predicate(w) == self.true_at(leftarg, rightarg, semantics.with_world(eval_point, w))
                )
            memo[key] = predicate
        return memo[key]

    def truth_at_world(self, leftarg: Any, rightarg: Any, eval_point: Dict[str, Any],
                       world: Any, encoding: Optional[str] = None) -> Any:
        """A Z3 expression for ``T(world)`` under the chosen encoding."""
        encoding = encoding or self.truth_encoding
        if encoding == PREDICATE:
            return self.truth_predicate(leftarg, rightarg, eval_point)(world)
        w = _concrete(world)
        if w is None:
            return self.true_at(leftarg, rightarg, self.semantics.with_world(eval_point, world))
        memo = _memo(self.semantics)
        key = ("true", self.name, leftarg.name, rightarg.name, w)
        if key not in memo:
            memo[key] = self.true_at(leftarg, rightarg, self.semantics.with_world(eval_point, world))
        return memo[key]

    def falsity_at_world(self, leftarg: Any, rightarg: Any, eval_point: Dict[str, Any],
                         world: Any, encoding: Optional[str] = None) -> Any:
        """A Z3 expression for the falsity clause at ``world``.

        Under the predicate encoding this is ``Not(cf_true(world))``: the
        recursive truth and falsity clauses are complementary at every world,
        which the cross-validation tests check on each solved model.
        """
        encoding = encoding or self.truth_encoding
        if encoding == PREDICATE:
            return z3.Not(self.truth_predicate(leftarg, rightarg, eval_point)(world))
        w = _concrete(world)
        if w is None:
            return self.false_at(leftarg, rightarg, self.semantics.with_world(eval_point, world))
        memo = _memo(self.semantics)
        key = ("false", self.name, leftarg.name, rightarg.name, w)
        if key not in memo:
            memo[key] = self.false_at(leftarg, rightarg, self.semantics.with_world(eval_point, world))
        return memo[key]

    def settler_clause(self, state: Any, world_condition: Callable[[Any], Any]) -> Any:
        """``every world above state satisfies world_condition``."""
        semantics = self.semantics
        return z3.And([
            z3.Implies(
                z3.And(self.is_world_at(w), semantics.is_part_of(state, w)),
                world_condition(w),
            )
            for w in semantics.all_states
        ])

    def closure_clause(self, state: Any, member: Callable[[Any], Any]) -> Any:
        """``state`` is a fusion of a nonempty set of states satisfying ``member``.

        Some member lies below ``state`` and every atomic part of ``state``
        lies in some member below ``state``.
        """
        semantics = self.semantics
        states = semantics.all_states
        atoms = [states[1 << i] for i in range(semantics.N)]
        members = {int(t.as_long()): member(t) for t in states}
        below = z3.Or([
            z3.And(members[int(t.as_long())], semantics.is_part_of(t, state)) for t in states
        ])
        covered = z3.And([
            z3.Implies(
                semantics.is_part_of(x, state),
                z3.Or([
                    z3.And(
                        members[int(t.as_long())],
                        semantics.is_part_of(x, t),
                        semantics.is_part_of(t, state),
                    )
                    for t in states
                ]),
            )
            for x in atoms
        ])
        return z3.And(below, covered)

    # -- clause API ---------------------------------------------------------

    def verifier_clause(self, state: Any, leftarg: Any, rightarg: Any,
                        eval_point: Dict[str, Any], encoding: Optional[str] = None) -> Any:
        raise NotImplementedError

    def falsifier_clause(self, state: Any, leftarg: Any, rightarg: Any,
                         eval_point: Dict[str, Any], encoding: Optional[str] = None) -> Any:
        raise NotImplementedError

    def extended_verify(self, state, leftarg, rightarg, eval_point):
        """Context-free: the evaluation world in ``eval_point`` is never consulted."""
        return self.verifier_clause(state, leftarg, rightarg, eval_point, self.truth_encoding)

    def extended_falsify(self, state, leftarg, rightarg, eval_point):
        return self.falsifier_clause(state, leftarg, rightarg, eval_point, self.truth_encoding)

    # -- Python side ------------------------------------------------------

    def python_sets(self, view: SolvedModelView) -> Tuple[Set[int], Set[int]]:
        raise NotImplementedError

    def find_verifiers_and_falsifiers(self, leftarg, rightarg, eval_point):
        """Python-side verifiers and falsifiers, independent of ``eval_point``."""
        view = SolvedModelView(self.semantics, leftarg, rightarg)
        v, f = self.python_sets(view)
        return view.to_bitvecs(v), view.to_bitvecs(f)


class ImpositionLocalCounterfactual(CandidateCounterfactual):
    """``\\boxrightI``: the truth clause with the candidate state in the world slot."""

    name = "\\boxrightI"
    key = "I"

    def verifier_clause(self, state, leftarg, rightarg, eval_point, encoding=None):
        return self.true_at(leftarg, rightarg, self.semantics.with_world(eval_point, state))

    def falsifier_clause(self, state, leftarg, rightarg, eval_point, encoding=None):
        return self.false_at(leftarg, rightarg, self.semantics.with_world(eval_point, state))

    def python_sets(self, view):
        return view.imposition_local()


class WorldStateCounterfactual(CandidateCounterfactual):
    """``\\boxrightW``: fusion closure of the worlds at which the counterfactual is true."""

    name = "\\boxrightW"
    key = "W"

    def verifier_clause(self, state, leftarg, rightarg, eval_point, encoding=None):
        return self.closure_clause(
            state,
            lambda t: z3.And(self.is_world_at(t), self.truth_at_world(leftarg, rightarg, eval_point, t, encoding)),
        )

    def falsifier_clause(self, state, leftarg, rightarg, eval_point, encoding=None):
        return self.closure_clause(
            state,
            lambda t: z3.And(self.is_world_at(t), self.falsity_at_world(leftarg, rightarg, eval_point, t, encoding)),
        )

    def python_sets(self, view):
        return fusion_closure(view.true_worlds), fusion_closure(view.false_worlds)


class SettlerCounterfactual(CandidateCounterfactual):
    """``\\boxrightL``: states every world above which makes the counterfactual true."""

    name = "\\boxrightL"
    key = "L"

    def verifier_clause(self, state, leftarg, rightarg, eval_point, encoding=None):
        return self.settler_clause(
            state, lambda w: self.truth_at_world(leftarg, rightarg, eval_point, w, encoding)
        )

    def falsifier_clause(self, state, leftarg, rightarg, eval_point, encoding=None):
        return self.settler_clause(
            state, lambda w: self.falsity_at_world(leftarg, rightarg, eval_point, w, encoding)
        )

    def python_sets(self, view):
        return view.settlers()


def _might_variant(counterfactual: type, name: str) -> type:
    """The defined might-counterfactual ``\\neg (A \\boxrightK \\neg B)`` for one candidate."""

    def derived_definition(self, leftarg, rightarg):
        return [NegationOperator, [counterfactual, leftarg, [NegationOperator, rightarg]]]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        MightCounterfactualOperator.print_method(self, sentence_obj, eval_point, indent_num, use_colors)

    doc = (
        f"``{name}``: might-counterfactual defined from ``{counterfactual.name}`` "
        f"as the negation of the counterfactual with negated consequent."
    )
    return type(
        f"{counterfactual.__name__.replace('Counterfactual', 'MightCounterfactual')}",
        (syntactic.DefinedOperator,),
        {
            "__doc__": doc,
            "name": name,
            "arity": 2,
            "derived_definition": derived_definition,
            "print_method": print_method,
        },
    )


ImpositionLocalMightCounterfactual = _might_variant(ImpositionLocalCounterfactual, "\\diamondrightI")
WorldStateMightCounterfactual = _might_variant(WorldStateCounterfactual, "\\diamondrightW")
SettlerMightCounterfactual = _might_variant(SettlerCounterfactual, "\\diamondrightL")

#: Candidate key -> primitive operator class.
CANDIDATE_OPERATORS: Dict[str, type] = {
    "I": ImpositionLocalCounterfactual,
    "W": WorldStateCounterfactual,
    "L": SettlerCounterfactual,
}

#: Candidate key -> defined might-counterfactual class.
MIGHT_OPERATORS: Dict[str, type] = {
    "I": ImpositionLocalMightCounterfactual,
    "W": WorldStateMightCounterfactual,
    "L": SettlerMightCounterfactual,
}


def get_candidate_operators() -> Dict[str, type]:
    """Operator name -> class for every candidate and its might variant."""
    operators: Dict[str, type] = {}
    for key, cls in CANDIDATE_OPERATORS.items():
        operators[cls.name] = cls
        operators[MIGHT_OPERATORS[key].name] = MIGHT_OPERATORS[key]
    return operators


def substitute_candidate(formula: str, key: str) -> str:
    """Rewrite ``\\boxright``/``\\diamondright`` in ``formula`` to candidate ``key``'s operators."""
    return (
        formula.replace("\\boxright ", f"\\boxright{key} ")
        .replace("\\diamondright ", f"\\diamondright{key} ")
    )
