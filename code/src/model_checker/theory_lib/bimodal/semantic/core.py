"""Core semantics for the bimodal theory: witness-family certificate search.

This module contains `BimodalSemantics`, the framework-facing semantic class for bimodal
logic (BL) under the certificate redesign -- see `docs/ADEQUACY.md` for the soundness
argument this class's constraints discharge, and the implementation plan's decisions
D1-D9 for the design choices cited by name throughout (`specs/184_.../plans/
01_witness-family-certificate-redesign.md`).

## Change of meaning

This module previously implemented a window-and-abundance Z3 encoding: a finite time
domain `(-M, M)`, `ForAll`/`Exists`-quantified frame axioms (nullity, converse,
compositionality, seriality, interpolation), and a Skolemized "abundance" constraint
asserting time-shift closure as a solver axiom. That encoding is retired outright, not
repaired -- see the task description's "why replace rather than repair" for the decisive
evidence (it refutes the paper's own MF axiom). `BimodalSemantics` is rewritten to the
certificate encoding's own contract; there is no relationship between the old and new
class bodies beyond the shared name.

## What this class now does

A certificate search has no notion of a state bit-width or a bounded time domain: the
"model" is the certified `ShiftSet` a satisfying certificate denotes (`docs/ADEQUACY.md`
section 3), whose world states are `(lasso, position)` pairs over an *infinite* carrier.
The variables are exactly `WitnessRegistry`'s (`witness_registry.py`): one Boolean per
`(lasso, position slot, closure formula)` label bit, one Boolean box guess per boxed
closure member, and a lasso-index allocation per boxed subformula's witness lasso.

**D3 -- `N` and `all_states` stay as vestigial attributes.** `models/structure.py`
unconditionally reads `self.semantics.all_states` and `self.semantics.N`
(`models/structure.py:101-102`), while `SemanticDefaults.__init__` only defines them when
`'N'` is a settings key (`models/semantic.py:119`). Since the certificate encoding has no
`'N'` setting at all, `__init__` sets `self.N = 0` and `self.all_states = []` explicitly.

**D4 -- settings.** `back`/`mid`/`fwd` (the maximum segment lengths of `LabelledLasso`,
matching `WitnessRegistry`'s `nb`/`nm`/`nf`) replace `N`/`M`; `max_witnesses` (optional,
default `None` = uncapped) replaces `temporal_depth`. `contingent`/`disjoint` are gone
along with the proposition-level machinery they used to gate (`proposition.py`, a later
phase). `max_time`, `expectation`, `iterate` and `solver` are unchanged.

**D5 -- the target position is a one-hot selector, not a fixed origin.** `premise_behavior`/
`conclusion_behavior` build the guarded windowed implication `And(Implies(sel[t], bit(0, t,
tr(p))) for t in target_window())` (and the negated form for conclusions) directly against
the registry and `WitnessConstraintGenerator.sel`, rather than calling `true_at` at a fixed
`main_point` the way the retired encoding did. `finalize_certificate()` adds the
complementary exactly-one constraint over the same selector.

**D6 -- two-phase constraint emission with an idempotent `finalize_certificate()`.**
`ModelConstraints.__init__` (`models/constraints.py:80`) reads `semantics.frame_constraints`
*by reference* and calls `semantics.premise_behavior`/`conclusion_behavior` for every
premise/conclusion **before** a `ModelStructure` (and therefore `_setup_solver`) is ever
constructed. So by the time `finalize_certificate()` runs (from `BimodalStructure`'s
`_setup_solver` override, a later phase), `_known_closure` already contains every formula
premise/conclusion-translation can contribute -- box faithfulness, the exactly-one
selector constraint and the per-lasso local-coherence/fulfilment constraints (which need
to know every witness lasso a boxed subformula might allocate) are therefore deferred to
this single method, appended to `self.frame_constraints` **in place** (never reassigned)
so `ModelConstraints`'s aliased reference sees the mutation. Guarded by
`self._certificate_finalized` so a second call (`re_solve()`, the iterator) is a no-op.

**D8 -- never report validity.** No method here decides "no certificate" one way or the
other; that is `BimodalStructure`'s job (a later phase). This module's own contribution to
D8 is structural: nothing it builds can be read as a validity claim, only as "a countermodel
matching (C1)-(C4) does/does not exist within the configured segment lengths."

**Deleted wholesale** (no replacement, no compatibility shim): `define_sorts`,
`define_primitives`, `is_valid_duration`, `build_task_rel_at`, the five frame-axiom
builders (`build_nullity_identity_constraint`, `build_converse_constraint`,
`build_forward_comp_constraint`, `build_seriality_constraint`,
`build_interpolation_constraint`), `ForAllTime`, `ExistsTime`, `build_frame_constraints`,
`is_valid_time`/`is_valid_time_for_world`, the shift/interval helpers (`can_shift_forward`,
`can_shift_backward`, `is_shifted_by`, `matching_states_when_shifted`,
`world_interval_constraint`, `time_interval_constraint`, `has_interval`,
`valid_array_domain`), all six abundance variants (`build_abundance_constraint`,
`skolem_abundance_constraint`, `capped_skolem_abundance_constraint`,
`depth_bounded_skolem_abundance_constraint`, `build_grounded_abundance_constraints`, and
`is_time_shifted`), `build_task_minimization_constraint`, `generate_time_intervals`, and
the whole `extract_model_elements` family (`extract_model_elements`,
`_extract_valid_world_ids`, `_extract_world_arrays`, `_extract_time_intervals`,
`safe_select`, `_extract_world_histories`, `_extract_time_shift_relations`). Certificate
extraction from a satisfying Z3 model is `extract_certificate` (a later phase).
"""

from __future__ import annotations

from typing import Any, Dict, FrozenSet, List, Optional, Tuple

from model_checker import z3_shim as z3

from model_checker.solver import is_true
from model_checker.models.semantic import SemanticDefaults

from .certificate import LabelledLasso, WitnessFamily
from .formula import Box, Formula, subformula_closure, translate
from .witness_registry import WitnessRegistry
from .witness_constraints import WitnessConstraintGenerator


##############################################################################
######################### SEMANTICS AND PROPOSITIONS #########################
##############################################################################

class BimodalSemantics(SemanticDefaults):
    """Framework-facing semantics for the witness-family certificate search over bimodal
    logic's discrete (Z) time. See the module docstring for the certificate design this
    class implements and the decisions (D1-D9) it follows."""

    DEFAULT_EXAMPLE_SETTINGS: Dict[str, Any] = {
        # Maximum back/mid/fwd segment lengths for the searched LabelledLasso family
        # (matching WitnessRegistry's nb/nm/nf). Small defaults, raised on demand.
        'back': 2,
        'mid': 1,
        'fwd': 2,
        # Optional cap on the number of distinct witness-lasso indices ever handed out;
        # None (the default) means uncapped -- one witness lasso per boxed subformula.
        'max_witnesses': None,
        # Maximum time Z3 is permitted to look for a model
        'max_time': 1,
        # Whether a model is expected or not (used for unit testing)
        'expectation': True,
        # Number of model iterations to generate
        'iterate': 1,
        # Solver backend: 'z3' or 'cvc5'
        'solver': 'z3',
    }

    # No additional general (display) settings: the certificate printer (a later phase)
    # needs no vertical-alignment option -- histories print as a single line each.
    ADDITIONAL_GENERAL_SETTINGS: Dict[str, Any] = {}

    def __init__(self, settings: Dict[str, Any]) -> None:
        # Initialize the superclass to set defaults and reset global state
        super().__init__(settings)

        # D3: N and all_states are vestigial attributes the framework reads
        # unconditionally (models/structure.py:101-102); the certificate encoding has no
        # 'N' setting, so SemanticDefaults.__init__ never sets them (models/semantic.py:119).
        self.N = 0
        self.all_states: List[Any] = []

        # D4: segment lengths and the optional witness cap.
        self.back: int = settings['back']
        self.mid: int = settings['mid']
        self.fwd: int = settings['fwd']
        self.max_witnesses: Optional[int] = settings.get('max_witnesses')

        # The Z3 variable layer (Phase 6) and the quantifier-free constraint generators
        # (Phases 7-8), sharing one closure that grows as premises/conclusions are
        # translated (see _register_closure and D6's module-docstring section).
        self._known_closure: FrozenSet[Formula] = frozenset()
        # Every premise/conclusion's translation, in the order premise_behavior/
        # conclusion_behavior were called (matching ModelConstraints.__init__'s own
        # per-premise/conclusion order) -- Phase 10's extraction and JSON export need
        # this list; true_at/false_at do not (see their own docstrings).
        self._premise_formulas: List[Formula] = []
        self._conclusion_formulas: List[Formula] = []
        self.witness_registry = WitnessRegistry(
            self.back, self.mid, self.fwd,
            closure=frozenset(),
            max_witnesses=self.max_witnesses,
        )
        self.constraint_generator = WitnessConstraintGenerator(self.witness_registry)

        # D6: frame_constraints starts empty. finalize_certificate() is the sole writer,
        # mutating this list in place (never reassigning it) so ModelConstraints's
        # by-reference copy (models/constraints.py:80) observes the mutation.
        self.frame_constraints: List["z3.BoolRef"] = []
        self._certificate_finalized = False
        # Overwritten by finalize_certificate() with the definitive list once every boxed
        # closure member's witness lasso has been allocated; this default (main lasso
        # only) is exactly what finalize_certificate() would produce for a closure with no
        # boxes, so extract_certificate stays correct even if called (unusually) before a
        # solve that never needed finalize_certificate to allocate anything further.
        self._active_lassos: List[int] = [0]

        # D5: premise/conclusion behaviour is the guarded windowed implication over the
        # one-hot target selector, not a lookup at a fixed evaluation point.
        self.premise_behavior = self._premise_behavior
        self.conclusion_behavior = self._conclusion_behavior

        # D5: main_point no longer names a fixed (world, time) evaluation pair -- the
        # target position is existential (the one-hot selector). "position" is filled in
        # with the concrete extracted target time only after a certificate is found
        # (semantic/model.py's extraction hook, a later phase); it stays None until then,
        # and forever for an unsatisfiable solve (D8: never report validity).
        self.main_point: Dict[str, Any] = {"lasso": 0, "position": None}

        # Populated by the certificate-extraction hook (a later phase) after a
        # satisfiable solve.
        self.certificate = None
        self.target_time: Optional[int] = None

    def _reset_global_state(self) -> None:
        """Reset any global state that could cause interference between examples.

        See `SemanticDefaults._reset_global_state`'s own docstring for the general
        contract. This override resets only what genuinely survives across
        `BimodalSemantics` instances: a stale `model_structure` back-reference from a
        previous example. The process-global bound-variable counter this method used to
        reset (`operators.py`'s `reset_bound_var_counter`) was deleted in Phase 14 along
        with the last `ForAll`/`Exists` construction it existed to protect -- the
        certificate encoding is quantifier-free (D6), so there is no longer any
        aliasing hazard for it to guard against.
        """
        super()._reset_global_state()

        if hasattr(self, 'model_structure'):
            delattr(self, 'model_structure')

        # Reset main_point; __init__ sets its real (post-construction) value afterwards.
        self.main_point = None

    # ------------------------------------------------------------------
    # Closure discovery (D6): every premise/conclusion translation grows the known
    # closure; finalize_certificate() consumes it once every premise and conclusion has
    # been seen.
    # ------------------------------------------------------------------

    def _register_closure(self, formula: Formula) -> None:
        self._known_closure = self._known_closure | subformula_closure(formula)

    def _premise_behavior(self, premise: Any) -> "z3.BoolRef":
        """D5: `And(Implies(sel[t], bit(0, t, tr(premise))) for t in target_window())`."""
        formula = translate(premise)
        self._register_closure(formula)
        self._premise_formulas.append(formula)
        window = self.witness_registry.target_window()
        return z3.And(*[
            z3.Implies(
                self.constraint_generator.sel(t),
                self.witness_registry.bit(0, t, formula),
            )
            for t in window
        ])

    def _conclusion_behavior(self, conclusion: Any) -> "z3.BoolRef":
        """D5: the negated form of `_premise_behavior`, for a conclusion."""
        formula = translate(conclusion)
        self._register_closure(formula)
        self._conclusion_formulas.append(formula)
        window = self.witness_registry.target_window()
        return z3.And(*[
            z3.Implies(
                self.constraint_generator.sel(t),
                z3.Not(self.witness_registry.bit(0, t, formula)),
            )
            for t in window
        ])

    # ------------------------------------------------------------------
    # Truth lookup (D5): translate, then look up the label bit. No recursive operator
    # dispatch -- local coherence (finalize_certificate's constraints) already stitches
    # every closure member's bit to its constituents' bits, so a compound formula's truth
    # value is exactly its own label bit, not a formula built from its parts' bits.
    # ------------------------------------------------------------------

    def true_at(self, sentence: Any, eval_point: Dict[str, Any]) -> "z3.BoolRef":
        """Return the label bit for `sentence`'s translation at `eval_point`.

        Args:
            sentence: The (type-updated) `Sentence` to evaluate.
            eval_point: `{"lasso": int, "position": int}` -- a concrete lasso index and
                integer position, e.g. from an already-extracted certificate. This is not
                the mechanism used to state the premises/conclusions themselves (see
                `_premise_behavior`/`_conclusion_behavior`, which range over the target
                window via the existential selector rather than fixing a position here).
        """
        formula = translate(sentence)
        return self.witness_registry.bit(eval_point["lasso"], eval_point["position"], formula)

    def false_at(self, sentence: Any, eval_point: Dict[str, Any]) -> "z3.BoolRef":
        """`Not(true_at(sentence, eval_point))`."""
        return z3.Not(self.true_at(sentence, eval_point))

    # ------------------------------------------------------------------
    # Two-phase constraint emission (D6)
    # ------------------------------------------------------------------

    def finalize_certificate(self) -> None:
        """Idempotently append the certificate search's global constraints to
        `self.frame_constraints`.

        By the time this runs, every premise and conclusion has already been translated
        (via `_premise_behavior`/`_conclusion_behavior`, called from `ModelConstraints.
        __init__` before any `ModelStructure` -- and therefore this method -- can run), so
        `self._known_closure` is the full closure the search needs. This method:

        1. Allocates one witness lasso per boxed subformula in the closure (main lasso
           index `0` plus at most one lasso per `Box` member -- report 01 section 4.4's
           "at most one more than the number of boxes"; `max_witnesses`, if set, forces
           sharing via `WitnessRegistry.allocate_witness_lasso`'s round-robin instead).
        2. Emits (C1) local coherence and (C2) fulfilment for every lasso in use.
        3. Emits (C3) box faithfulness across every lasso in use.
        4. Emits (C4)'s exactly-one constraint over the target selector (the guarded
           premise/conclusion implications were already added per premise/conclusion by
           `_premise_behavior`/`_conclusion_behavior`, so `target_constraints` is called
           with empty premise/conclusion lists here to avoid emitting them twice).

        Guarded by `self._certificate_finalized`: a second call is a no-op, since
        `re_solve()` and the model iterator (a later phase) both call this again.
        """
        if self._certificate_finalized:
            return
        self._certificate_finalized = True

        closure = self._known_closure
        self.witness_registry.closure = closure

        lassos = [0]
        for formula in closure:
            if isinstance(formula, Box):
                index = self.witness_registry.allocate_witness_lasso(formula.child)
                if index not in lassos:
                    lassos.append(index)

        # Recorded for extract_certificate (Phase 10): the definitive, ordered list of
        # lasso indices in this search, main lasso (0) always first.
        self._active_lassos: List[int] = lassos

        for lasso in lassos:
            self.frame_constraints.extend(
                self.constraint_generator.local_coherence_constraints(lasso)
            )
            self.frame_constraints.extend(
                self.constraint_generator.fulfilment_constraints(lasso)
            )

        self.frame_constraints.extend(
            self.constraint_generator.box_faithfulness_constraints(lassos)
        )

        self.frame_constraints.extend(
            self.constraint_generator.target_constraints([], [])
        )

    # ------------------------------------------------------------------
    # Certificate extraction from a satisfying Z3 model (Phase 10)
    # ------------------------------------------------------------------

    def extract_certificate(self, z3_model: Any) -> Tuple[WitnessFamily, int]:
        """Build the `WitnessFamily` and target time a satisfying `z3_model` denotes.

        Must be called after `finalize_certificate()` (so `self._active_lassos` and
        `self.witness_registry.closure` are the final, complete ones) and after a
        satisfiable solve. For each lasso in `self._active_lassos`, reads one label per
        position in `self.witness_registry.target_window()` -- exactly one representative
        position per slot, in `back`-then-`mid`-then-`fwd` order -- and splits that window
        into the three segments `LabelledLasso` expects. Reads every boxed closure member's
        guess into `bx`. Reads the one-hot target selector to recover the concrete target
        time (`self.constraint_generator.sel`); exactly one must be true, since
        `finalize_certificate` asserts exactly-one over the same selector set.

        Returns `(family, target_time)`. Callers (the Phase 12 structure re-check hook)
        must independently re-check the returned family via `certificate.recheck` before
        treating it as a countermodel -- see `docs/ADEQUACY.md` section 6.2 (obligation S3).
        """
        registry = self.witness_registry
        closure = registry.closure
        window = list(registry.target_window())

        lassos: List[LabelledLasso] = []
        for lasso_index in self._active_lassos:
            labels = [
                frozenset(
                    formula
                    for formula in closure
                    if is_true(
                        z3_model.eval(registry.bit(lasso_index, t, formula), model_completion=True)
                    )
                )
                for t in window
            ]
            back = tuple(labels[: registry.nb])
            mid = tuple(labels[registry.nb: registry.nb + registry.nm])
            fwd = tuple(labels[registry.nb + registry.nm:])
            lassos.append(LabelledLasso(back=back, mid=mid, fwd=fwd))

        bx: Dict[Formula, bool] = {}
        for formula in closure:
            if isinstance(formula, Box):
                bx[formula.child] = is_true(
                    z3_model.eval(registry.guess(formula.child), model_completion=True)
                )

        family = WitnessFamily(bx=bx, lassos=tuple(lassos))

        target_time: Optional[int] = None
        for t in window:
            selector = self.constraint_generator.sel(t)
            if is_true(z3_model.eval(selector, model_completion=True)):
                target_time = t
                break
        if target_time is None:
            raise RuntimeError(
                "extract_certificate: no position of the one-hot target selector is true "
                "in this model -- finalize_certificate()'s exactly-one constraint should "
                "make this impossible for a genuinely satisfying model"
            )

        return family, target_time

    def export_certificate_json(
        self, family: WitnessFamily, target_time: int
    ) -> Dict[str, object]:
        """Serialize `family` to the certificate wire format (`WitnessFamily.to_json`),
        using this search's own recorded premises/conclusions (`_premise_formulas`/
        `_conclusion_formulas`) and `target_time`."""
        return family.to_json(
            premises=self._premise_formulas,
            conclusions=self._conclusion_formulas,
            target_time=target_time,
        )

    def inject_z3_model_values(self, z3_model: Any, original_semantics: "BimodalSemantics", model_constraints: Any) -> None:
        """Pin every label bit, box guess, and target-selector Boolean from a previous
        iteration's `z3_model` as a concrete constraint on `model_constraints`.

        Rewritten for the certificate encoding's variable set (label bits, box guesses,
        the one-hot selector) in place of the retired encoding's world/truth_condition/
        task_rel variables. `original_semantics`'s registry/generator objects are read for
        their variable tables; the Z3 `BoolRef` objects themselves are reused directly
        (their names depend only on lasso/slot/formula, or on formula/position -- never on
        which `BimodalSemantics` instance created them -- so no reconstruction against
        `self` is needed). Consumed by the model iterator (Phase 15 wires this in).
        """
        registry = original_semantics.witness_registry
        generator = original_semantics.constraint_generator

        for var in registry._bits.values():
            value = z3_model.eval(var, model_completion=True)
            model_constraints.all_constraints.append(var if is_true(value) else z3.Not(var))

        for var in registry._guesses.values():
            value = z3_model.eval(var, model_completion=True)
            model_constraints.all_constraints.append(var if is_true(value) else z3.Not(var))

        for var in generator._sel.values():
            value = z3_model.eval(var, model_completion=True)
            model_constraints.all_constraints.append(var if is_true(value) else z3.Not(var))
