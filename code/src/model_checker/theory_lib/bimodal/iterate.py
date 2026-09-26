"""Bimodal theory specific model iteration implementation.

This module provides the BimodalModelIterator implementation which handles:
1. Detecting differences between models using the certificate encoding's own variables
2. Creating constraints to differentiate models by label bits and box guesses
3. Displaying those differences

## Change of meaning

The retired encoding's iterator compared world histories (`{world_id: {time: state}}`),
truth conditions read via `semantics.truth_condition`, and `task_rel`/time-shift-relation
tables. None of that exists any more (see `semantic/core.py`'s own module docstring). This
module is rewritten around the certificate encoding's own variable set: label bits
(`WitnessRegistry._bits`), box guesses (`WitnessRegistry._guesses`), and the extracted
`WitnessFamily`/`target_time` pair (`semantic/core.py`'s `extract_certificate`, Phase 10).

## `_create_difference_constraint`/`_create_non_isomorphic_constraint` ARE the live loop's
exclusion mechanism for this theory (HISTORY: they used not to be)

HISTORY: `BaseModelIterator.iterate()`/`iterate_generator()` (`model_checker/iterate/core.py`)
used to call a composed, theory-agnostic `ConstraintGenerator`
(`model_checker/iterate/constraints.py`) directly, whose own exclusion logic was entirely gated
on `hasattr(semantics, 'is_world')` -- true of the other three theories (which keep a bitvector
world-state predicate), **false of this one** (D3/D4 deliberately have no state-existence
predicate at all; the certified carrier is `{0,...,k} x Z`, not enumerated states). That made
`_create_difference_constraint`/`_create_non_isomorphic_constraint` below dead code from the live
loop's perspective, and it made `iterate: N > 1` crash outright on the unguarded `is_world` call
before that gap was even reached (see `iterate/models.py`'s `build_new_model_structure`).

The shared iterate framework now exposes three polymorphic extension points on
`BaseModelIterator` -- `_pin_theory_specific_values`, `_build_exclusion_constraints` (which calls
`_create_difference_constraint`), and `_check_model_isomorphism` -- each with a base-class
default that preserves the other three theories' previous behavior. This class overrides all
three below (see each method's own docstring), so the live loop now genuinely consults them:
`_create_difference_constraint`'s blocking clause is the actual exclusion constraint bimodal's
live `iterate: N > 1` search enforces, not merely an interface-parity stub. See
`iterate/README.md`'s Extension Guide for the full three-hook contract shared across theories.

`_create_non_isomorphic_constraint` remains reachable a second way too: `_build_stronger_constraint`
(`iterate/core.py`) composes it with the generic `ConstraintGenerator` escape constraint when the
live loop hits an isomorphic model. `_check_model_isomorphism` below now performs real detection
(see the next section) rather than the constant "not isomorphic" it used to return, so this
composition path *is* exercised for bimodal too, not only for the other three theories.

## Isomorphism detection and rejection are rotation/permutation-invariant

`_check_model_isomorphism` and `_create_non_isomorphic_constraint` both consult
`semantic/symmetry.py`'s single shared definition of the rotation/permutation group
`(Z/nb x Z/nf)^L (rtimes) S_{L-1}` acting on a certificate (`L` lassos: the main lasso plus
`L - 1` witness lassos): each lasso may be independently rotated within its own `back`/`fwd`
segments, and the witness-lasso indices `1..L-1` may be permuted, holding the main lasso (index
`0`) fixed. Group size is `(nb * nf)**L * factorial(L - 1)`, capped
(`symmetry.DEFAULT_GROUP_CAP`) with a documented reduced generating-set fallback once the full
group would be impractically large to enumerate.

**Detection** (`_check_model_isomorphism`) compares `symmetry.certificate_orbit_key` between the
new structure's certificate and every previously-found structure's -- a pure-Python, orbit-
invariant canonical key, no Z3 involved. It is self-validating and needs no re-check of its own:
every certificate it compares was already independently re-checked (`semantic/model.py`'s S3
hook) before this method ever sees it, so any matching key witnesses a transform whose image is
already known valid.

**Exclusion** (`_create_non_isomorphic_constraint`) builds a conjunction, one disjunctive
conjunct per group element whose transform of the handed model's certificate independently
re-checks as `"countermodel"` (`certificate.recheck`) -- discarding elements that don't, since
permutation is provably condition-preserving but a nontrivial rotation is not in general (a
rotation moves the `back`/`mid` and `mid`/`fwd` boundaries the local-coherence and fulfilment
biconditionals read across, so it can leave the certificate space; see `symmetry.py`'s own
docstring for the argument). Each retained conjunct ranges over `_orbit_variables()` --
`_bits` + `_guesses` (`_certificate_variables()`'s own set, deliberately unchanged: the exact-bit
`_create_difference_constraint` still ranges over exactly those two, never the selector) plus the
one-hot target selector `_sel`, since a lasso-`0` rotation moves which position the target
condition reads.
"""

import sys
import logging

from model_checker import z3_shim as z3

from model_checker.iterate.core import BaseModelIterator
from model_checker.solver import is_true
from model_checker.theory_lib.bimodal.semantic import symmetry
from model_checker.theory_lib.bimodal.semantic import certificate
from model_checker.theory_lib.bimodal.semantic.certificate import WitnessFamily

# Configure logging
logger = logging.getLogger(__name__)
if not logger.handlers:
    handler = logging.StreamHandler(sys.stdout)
    formatter = logging.Formatter('[BIMODAL-ITERATE] %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    logger.setLevel(logging.WARNING)


class BimodalModelIterator(BaseModelIterator):
    """Model iterator for the bimodal theory (certificate encoding). See the module
    docstring for the change of meaning and the discovered live-loop exclusion gap."""

    def __init__(self, build_example):
        super().__init__(build_example)
        self._ensure_frame_constraints_in_search_solver()

    def _ensure_frame_constraints_in_search_solver(self):
        """Defensive workaround for a bug discovered while testing Phase 4's orbit
        exclusion: the live loop's persistent search solver
        (`self.constraint_generator.solver`, `iterate/constraints.py`) can start with
        **none** of `semantics.frame_constraints` asserted -- confirmed empirically,
        `len(self.constraint_generator.solver.assertions())` is `0` right after
        construction for a real `BuildExample`.

        Root cause, traced into `models/structure.py`'s shared `ModelDefaults.solve()`:
        it does `self.stored_solver = self.solver` *before* calling `_setup_solver`,
        which then reassigns `self.solver` to a *different*, freshly populated solver
        object and returns it -- `stored_solver` is left pointing at the solver's
        pristine, pre-population state (a brand-new, always-empty `create_solver(...)`
        result) forever. `ConstraintGenerator._create_persistent_solver` reads
        `model_structure.solver` first and falls back to `stored_solver` only when
        `.solver` is `None` -- which it is here, since this theory's certificate
        S3 recheck (`semantic/model.py`) runs after `_cleanup_solver_resources()` has
        already cleared it. The live loop therefore searches against an
        under-constrained problem (no local coherence, fulfilment, box-faithfulness,
        *or the actual premise/conclusion* asserted at all): "differs in at least one
        `_bits`/`_guesses`/`_sel` variable" can then be satisfied by flipping a bit
        that carries no real information -- `build_new_model_structure`'s independent
        rebuild-and-recheck (S3) re-derives it to the same value regardless -- so a
        "genuinely new" Z3 model can decode to the *identical* certificate, defeating
        `_create_difference_constraint` and this plan's orbit exclusion alike. This is
        a bug in the shared engine (`models/structure.py`'s `solve()`), out of this
        task's file scope (`theory_lib/bimodal/` only). The fix here is a theory-local,
        defensive re-assertion at iterator construction, mirroring the already-
        established precedent `_pin_theory_specific_values` sets for working around a
        generic-framework assumption this theory's certificate encoding does not fit.

        Re-asserts `semantics.frame_constraints` (mutated in place by
        `finalize_certificate`, and therefore up to date by the time this constructor
        runs -- `example.model_structure` already exists and was already solved) *and*
        `model_constraints.model_constraints`/`.premise_constraints`/
        `.conclusion_constraints` -- **not** `model_constraints.all_constraints`. An
        earlier version of this fix read `all_constraints` directly and produced a
        search solver that still accepted a `sel[t]` choice the *guarded premise
        implication* would reject (confirmed empirically: `Implies(sel[-2], lab_..._
        Imp(Untl, Bot))` evaluated `False` under a model the under-constrained search
        solver nonetheless reported `sat`). Root cause: `ModelConstraints.__init__`
        computes `all_constraints = frame_constraints + model_constraints + ...` via
        list concatenation (a *snapshot*, copying elements at that moment) *before*
        `finalize_certificate()` ever runs (that happens later, from `BimodalStructure.
        __init__` -> `_setup_solver`) -- so `all_constraints` permanently misses every
        coherence/fulfilment/box-faithfulness/target constraint, even though `model_
        constraints.frame_constraints` itself (the plain attribute, not the snapshot)
        stays correctly aliased to `semantics.frame_constraints` and does pick them up.
        `model_constraints.model_constraints`/`premise_constraints`/
        `conclusion_constraints` are unaffected by this timing gap (nothing mutates
        them after `ModelConstraints.__init__` returns), so reading those three
        directly, alongside the live `semantics.frame_constraints`, is both correct
        and complete.

        Defensive about test doubles: several existing unit/integration tests
        construct the iterator against `_mock_build_example`, whose `model_
        constraints` is a bare `Mock()` -- `.model_constraints`/`.premise_constraints`/
        `.conclusion_constraints` on that double are auto-created `Mock` attributes,
        not real lists, and must not be concatenated onto the constraint list (would
        raise `TypeError` or silently corrupt it). Each of the four sources is only
        used when it is an actual `list`; a test double simply contributes nothing
        beyond whatever real `semantics.frame_constraints` it was given (matching
        this method's original, narrower behavior for those tests).
        """
        model_constraints = self.build_example.model_constraints
        semantics = model_constraints.semantics
        solver = self.constraint_generator.solver
        constraints: list = []
        frame = getattr(semantics, "frame_constraints", None)
        if isinstance(frame, list):
            constraints.extend(frame)
        for attr in ("model_constraints", "premise_constraints", "conclusion_constraints"):
            value = getattr(model_constraints, attr, None)
            if isinstance(value, list):
                constraints.extend(value)
        for constraint in constraints:
            solver.add(constraint)

    def _certificate_variables(self):
        """Every label-bit and box-guess Z3 Boolean this search declared -- shared by
        `_create_difference_constraint` and `_create_non_isomorphic_constraint`."""
        semantics = self.build_example.model_constraints.semantics
        registry = semantics.witness_registry
        return list(registry._bits.values()) + list(registry._guesses.values())

    def _pin_theory_specific_values(self, temp_solver, z3_model, model_constraints):
        """Pin every certificate variable (label bit / box guess) declared by the
        *new* model's own `witness_registry` to its value in `z3_model`, mirroring the
        generic `is_world`/`verify`/`falsify` pinning `build_new_model_structure`
        performs for the other three theories.

        This is required, not merely helpful: the certificate encoding has no
        state-existence predicate at all (D3/D4; `N = 0`), so the generic pinning loop
        in `iterate/models.py` cannot reach any of this theory's actual model content --
        without this override, `build_new_model_structure` would solve model 2+ against
        only the frame constraints (via `model_constraints.all_constraints`) with
        *nothing* pinning the label bits or box guesses to the values the search just
        found, so the rebuilt structure would not reflect the model the solver actually
        returned.

        Note the variables come from `model_constraints.semantics`, not
        `self.build_example.model_constraints.semantics`: `build_new_model_structure`
        constructs a fresh `BimodalSemantics` instance (and therefore a fresh
        `WitnessRegistry`) for every new model, so the variables to pin must be read
        from that same fresh instance -- the original search's own registry holds a
        disjoint set of Z3 constants.

        **Second discovered bug, fixed here defensively.** `iterate/models.py`'s
        `build_new_model_structure` calls this hook *before* constructing the
        `model_structure_class` instance whose `_setup_solver` is what actually calls
        `finalize_certificate()` on the fresh semantics (`semantic/model.py`'s
        `BimodalStructure._setup_solver`). At the point this method runs, the fresh
        registry has therefore only allocated bits for whatever `_premise_behavior`/
        `_conclusion_behavior` touched during `ModelConstraints.__init__` -- confirmed
        empirically: `10` of the `70` bits this search actually needs, `0` of `1`
        guesses, no witness lasso allocated at all. Pinning that partial set leaves
        every *other* certificate variable (most of them) completely free for the
        rebuild's later solve, so it converges on whatever assignment Z3 finds first
        for the *fresh* problem -- deterministically reproducing the very first model
        every time, regardless of which candidate `z3_model` this call was asked to
        pin. Calling `finalize_certificate()` here first (idempotent, per its own
        docstring, so the later call from `_setup_solver` is a no-op) allocates every
        witness lasso and creates every `_bits`/`_guesses` entry this search will ever
        need *before* they are read below, so the full set gets pinned.
        """
        semantics = model_constraints.semantics
        semantics.finalize_certificate()
        registry = semantics.witness_registry
        variables = list(registry._bits.values()) + list(registry._guesses.values())
        for var in variables:
            value = z3_model.eval(var, model_completion=True)
            pinned = var if is_true(value) else z3.Not(var)
            temp_solver.add(pinned)
            # **Third discovered bug, fixed here defensively.** `build_new_model_
            # structure` (`iterate/models.py`) stores this method's `temp_solver`
            # assertions into `model_constraints.all_constraints` ("so the model will
            # use them", per its own comment) -- but `models/structure.py`'s
            # `_setup_solver` (called next, from `BimodalStructure.__init__` via
            # `_setup_solver`'s own override, which just delegates to the base class)
            # never reads `all_constraints` at all: it reads `model_constraints.
            # frame_constraints`/`.model_constraints`/`.premise_constraints`/
            # `.conclusion_constraints` -- four separate lists, built once at
            # `ModelConstraints.__init__` time, well before any pin exists. Every pin
            # this method adds to `temp_solver` is therefore silently discarded before
            # it ever reaches the solver that actually builds the rebuilt structure --
            # confirmed empirically: rebuilding against a candidate model that
            # genuinely differs from the search's previous model, bit for bit,
            # nonetheless decoded to a certificate byte-for-byte identical to the
            # first one, every time, since the rebuild solve was effectively
            # unconstrained by any of these pins and simply reproduced the same
            # deterministic first solution to the fresh (unpinned) problem. This is a
            # bug in the shared engine (`iterate/models.py`), out of this task's file
            # scope. The fix here: also append directly to `semantics.frame_
            # constraints`, which *is* one of the four lists `_setup_solver` reads,
            # and which `model_constraints.frame_constraints` aliases by reference
            # (D6's own aliasing discipline, `semantic/model.py`'s `_setup_solver`
            # docstring) -- so this pin reaches the solver regardless of the dead
            # `all_constraints` path. `temp_solver.add(pinned)` above is kept
            # unchanged for interface parity with the existing unit tests
            # (`TestPinTheorySpecificValues`), which assert against `temp_solver`
            # directly.
            semantics.frame_constraints.append(pinned)

        # Also pin the one-hot target selector (`_sel`), for the same reason as
        # `_bits`/`_guesses` above: `premise_constraints`/`conclusion_constraints`
        # (`ModelConstraints.__init__`) are guarded implications keyed by `sel[t]`,
        # and leaving every `sel[t]` free lets the fresh rebuild's solver pick any
        # position satisfying `target_constraints`'s exactly-one requirement -- not
        # necessarily the same position the search's own model selected. Pinning it
        # removes that remaining, otherwise-unconstrained degree of freedom.
        for t in registry.target_window():
            var = semantics.constraint_generator.sel(t)
            value = z3_model.eval(var, model_completion=True)
            pinned = var if is_true(value) else z3.Not(var)
            temp_solver.add(pinned)
            semantics.frame_constraints.append(pinned)

    def _check_model_isomorphism(self, new_structure, new_model):
        """Real orbit-key detector: reports `(True, previous_model)` when
        `new_structure`'s certificate lies in the same rotation/permutation orbit
        (`semantic/symmetry.py`'s `certificate_orbit_key`) as a previously-found one,
        `(False, None)` otherwise. Remains a **complete opt-out of the shared
        `ModelGraph` path** -- this is not a re-adoption of graph-based checking.

        The shared `ModelGraph` representation (`iterate/graph.py`) is built from
        `model_structure.z3_world_states`, which this theory's certificate encoding
        never populates (D3/D4 have no state-existence predicate to enumerate at all --
        see this module's own docstring). Two structures that both lack the attribute
        therefore both produce an *empty* graph, and NetworkX reports two empty graphs
        as isomorphic -- a false positive, not "no information": left un-overridden,
        every model after the first would be wrongly declared a duplicate of the
        first and skipped forever (see `iterate/tests/`'s regression test documenting
        this exact false positive on two empty-graph `ModelGraph`s). `ModelGraph` is
        therefore never constructed for this theory, exactly as before -- what changes
        here is that "not isomorphic" is no longer the *only* answer this method can
        give: it is now a real, orbit-key-based comparison, not merely a stub with
        nothing meaningful to compare.

        Detection is self-validating and needs no re-check of its own: it only ever
        compares `new_structure`'s already-independently-rechecked certificate
        (`semantic/model.py`'s S3 hook) against a previous certificate that was
        rechecked the same way when it was found -- no unverified transform is ever
        asserted valid by this method (decision D-B). Orbit *exclusion* -- making sure
        the next search actually avoids the whole orbit, not just this one model -- is
        `_create_non_isomorphic_constraint`'s job, not this one's.

        Mirrors the base class's own `zip(previous_structures, previous_models)`
        pairing convention (`iterate/graph.py`'s `IsomorphismChecker.check_isomorphism`)
        by reading `self.model_structures`/`self.found_models` directly, since this
        override's signature (matching the extension point) is not handed those lists
        as arguments.
        """
        new_certificate = getattr(new_structure, "certificate", None)
        if not isinstance(new_certificate, WitnessFamily):
            return False, None
        new_target_time = getattr(new_structure, "target_time", None)
        new_key = symmetry.certificate_orbit_key(new_certificate, new_target_time)

        # Memoize each previously-found structure's orbit key by identity, so a search
        # that checks many new models against the same growing `model_structures` list
        # recomputes each *previous* structure's key at most once rather than once per
        # comparison.
        memo = getattr(self, "_orbit_key_memo", None)
        if memo is None:
            memo = {}
            self._orbit_key_memo = memo

        for previous_structure, previous_model in zip(self.model_structures, self.found_models):
            previous_certificate = getattr(previous_structure, "certificate", None)
            if not isinstance(previous_certificate, WitnessFamily):
                continue
            cache_key = id(previous_structure)
            previous_key = memo.get(cache_key)
            if previous_key is None:
                previous_target_time = getattr(previous_structure, "target_time", None)
                previous_key = symmetry.certificate_orbit_key(previous_certificate, previous_target_time)
                memo[cache_key] = previous_key
            if new_key == previous_key:
                return True, previous_model

        return False, None

    def _blocking_clause(self, prev_model):
        """`Or(var != prev_model's value for var)` over every certificate variable --
        `True` (as a Z3 constraint) exactly when the next model differs from `prev_model` in
        at least one label bit or box guess."""
        variables = self._certificate_variables()
        if not variables:
            return None
        disjuncts = []
        for var in variables:
            prev_value = prev_model.eval(var, model_completion=True)
            disjuncts.append(var != z3.BoolVal(bool(is_true(prev_value))))
        return z3.Or(*disjuncts)

    def _create_difference_constraint(self, previous_models):
        """Blocking clause requiring difference, in at least one label bit or box guess,
        from every model in `previous_models` (D6's certificate variable set). See the
        module docstring: not on the live iteration loop's own exclusion path, but kept
        for interface parity and direct programmatic use.
        """
        clauses = [
            clause
            for clause in (self._blocking_clause(prev_model) for prev_model in previous_models)
            if clause is not None
        ]
        return z3.And(*clauses) if clauses else z3.BoolVal(True)

    def _orbit_variables(self):
        """Every variable `_create_non_isomorphic_constraint`'s orbit clause may range
        over: every label bit and box guess (`_certificate_variables()`'s own set) plus
        the one-hot target-selector Booleans
        (`WitnessConstraintGenerator._sel`). Deliberately a *different* method from
        `_certificate_variables()`, not an extension of it in place: `_create_
        difference_constraint`'s variable set stays exactly `_bits` + `_guesses` (Non-
        Goal 1) -- only the orbit clause needs the selector, since C4 (what the
        selector encodes) is exactly what a lasso-`0` rotation moves (see
        `semantic/symmetry.py`'s `selector_action`)."""
        semantics = self.build_example.model_constraints.semantics
        registry = semantics.witness_registry
        generator = semantics.constraint_generator
        return (
            list(registry._bits.values())
            + list(registry._guesses.values())
            + list(generator._sel.values())
        )

    def _orbit_blocking_clause(self, isomorphic_model):
        """The orbit-exclusion clause for `isomorphic_model`: one disjunctive conjunct
        per element of `isomorphic_model`'s certificate's rotation/permutation orbit
        (`semantic/symmetry.py`) that survives a `certificate.recheck` gate (decision
        D-C) -- dropping any element whose transform is not itself a valid certificate
        (D-A: rotation is not generally condition-preserving).

        `isomorphic_model`'s certificate is decoded once (`extract_certificate`), not
        once per group element. For each retained element `g`, the conjunct is built
        over `_orbit_variables()`'s three families -- `_bits` (moved by
        `symmetry.slot_action`), `_guesses` (never moved -- box guesses are global to
        the family, not per-lasso/per-position), and `_sel` (moved by
        `symmetry.selector_action`) -- each disjunct reading `isomorphic_model`'s value
        at a variable's *preimage* under `g` and asserting the variable itself differs
        from that value. This is what actually excludes `g`'s image of the model, not
        merely `g`'s representative.
        """
        semantics = self.build_example.model_constraints.semantics
        registry = semantics.witness_registry
        generator = semantics.constraint_generator
        family, target_time = semantics.extract_certificate(isomorphic_model)
        lasso_count = len(family.lassos)

        conjuncts = []
        for element in symmetry.enumerate_group(registry.nb, registry.nf, lasso_count):
            transformed_family, transformed_target_time = symmetry.apply(element, family, target_time)
            verdict = certificate.recheck(
                transformed_family,
                semantics._premise_formulas,
                semantics._conclusion_formulas,
                transformed_target_time,
            )
            if verdict.get("status") != "countermodel":
                continue

            disjuncts = []
            for old_key, new_key in symmetry.slot_action(registry, element).items():
                old_var = registry._bits[old_key]
                new_var = registry._bits[new_key]
                value = is_true(isomorphic_model.eval(old_var, model_completion=True))
                disjuncts.append(new_var != z3.BoolVal(value))
            for var in registry._guesses.values():
                value = is_true(isomorphic_model.eval(var, model_completion=True))
                disjuncts.append(var != z3.BoolVal(value))
            for old_t, new_t in symmetry.selector_action(registry, element).items():
                old_var = generator.sel(old_t)
                new_var = generator.sel(new_t)
                value = is_true(isomorphic_model.eval(old_var, model_completion=True))
                disjuncts.append(new_var != z3.BoolVal(value))

            if disjuncts:
                conjuncts.append(z3.Or(*disjuncts))

        if not conjuncts:
            return z3.BoolVal(True)
        if len(conjuncts) == 1:
            return conjuncts[0]
        return z3.And(*conjuncts)

    def _create_non_isomorphic_constraint(self, isomorphic_model):
        """Blocking clause requiring difference from every recheck-valid element of
        `isomorphic_model`'s rotation/permutation orbit (`_orbit_blocking_clause`), not
        just `isomorphic_model` itself. See `semantic/symmetry.py`'s module docstring
        for the group this excludes and D-A/D-B/D-C for why exclusion recheck-gates
        each element. `_create_difference_constraint` above is deliberately unchanged
        (Non-Goal 1): it keeps ranging over `_certificate_variables()` only.

        **Direct-assert workaround for a discovered bug in the shared engine.**
        `BaseModelIterator._build_stronger_constraint` (`iterate/core.py`) composes this
        method's return value into a *local* `extended_constraints` list, but the live
        loop's `continue` -- taken immediately after an isomorphic hit -- returns to the
        top of the search `while` loop, which recomputes `extended_constraints` from
        `_build_exclusion_constraints` alone and never revisits the list the composed
        constraint was appended to. The orbit-blocking clause this method returns is
        therefore silently discarded before it ever reaches
        `ConstraintGenerator.check_satisfiability`, and the search re-finds the exact
        same isomorphic model forever (confirmed empirically: with the Phase 3 detector
        live and this bug unworked-around, `TestLiveIteration` regresses to `0`
        genuinely-new models found, `isomorphic_model_count` never advancing past the
        same repeated match). This is a bug in `iterate/core.py`, out of this task's
        file scope (`theory_lib/bimodal/` only, plus one sentence in
        `iterate/README.md` -- see the plan's Risk table). Rather than edit the shared
        engine, this method also asserts its own clause directly onto the persistent
        solver (`self.constraint_generator.solver` -- `iterate/constraints.py`'s
        `ConstraintGenerator`, not to be confused with `semantics.constraint_generator`,
        this theory's own `WitnessConstraintGenerator`) as a side effect, so the
        exclusion takes effect on the *next* `check_satisfiability` call regardless of
        whether the caller's bookkeeping honors the return value. The return value
        itself is unchanged in meaning, kept for interface parity and direct
        programmatic use (e.g. the existing `TestNonIsomorphicOrbitExclusion` suite,
        which calls this method directly without going through the live loop at all).
        """
        clause = self._orbit_blocking_clause(isomorphic_model)
        self.constraint_generator.solver.add(clause)
        return clause

    def _create_stronger_constraint(self, isomorphic_model):
        """Create constraint for finding stronger models. Not specialized for the
        certificate encoding (matches the retired encoding's own placeholder)."""
        return z3.BoolVal(True)

    def _calculate_differences(self, new_structure, previous_structure):
        """Label-bit and box-guess differences between two certificate-encoded model
        structures, read from each structure's own extracted `certificate`
        (`semantic/core.py`'s `extract_certificate`, Phase 10) rather than from Z3 models
        directly -- both structures have already independently re-checked their own
        certificate (Phase 12's S3 hook) by the time this runs.
        """
        differences = {
            "labels": {},
            "box_guesses": {},
            "target_time": None,
        }

        new_certificate = getattr(new_structure, "certificate", None)
        previous_certificate = getattr(previous_structure, "certificate", None)
        if new_certificate is None or previous_certificate is None:
            return differences

        semantics = new_structure.semantics
        window = list(semantics.witness_registry.target_window())

        label_diffs = {}
        lasso_count = max(len(new_certificate.lassos), len(previous_certificate.lassos))
        for lasso_index in range(lasso_count):
            new_lasso = new_certificate.lassos[lasso_index] if lasso_index < len(new_certificate.lassos) else None
            old_lasso = previous_certificate.lassos[lasso_index] if lasso_index < len(previous_certificate.lassos) else None
            if new_lasso is None or old_lasso is None:
                label_diffs[lasso_index] = {"added": new_lasso is not None, "removed": old_lasso is not None}
                continue
            position_diffs = {}
            for t in window:
                new_label = new_lasso.label(t)
                old_label = old_lasso.label(t)
                if new_label != old_label:
                    position_diffs[t] = {"old": sorted(map(repr, old_label)), "new": sorted(map(repr, new_label))}
            if position_diffs:
                label_diffs[lasso_index] = position_diffs
        if label_diffs:
            differences["labels"] = label_diffs

        guess_diffs = {}
        all_boxed = set(new_certificate.bx.keys()) | set(previous_certificate.bx.keys())
        for child in all_boxed:
            new_guess = new_certificate.bx_of(child)
            old_guess = previous_certificate.bx_of(child)
            if new_guess != old_guess:
                guess_diffs[repr(child)] = {"old": old_guess, "new": new_guess}
        if guess_diffs:
            differences["box_guesses"] = guess_diffs

        new_time = getattr(new_structure, "target_time", None)
        old_time = getattr(previous_structure, "target_time", None)
        if new_time != old_time:
            differences["target_time"] = {"old": old_time, "new": new_time}

        return differences

    def display_model_differences(self, model_structure, output=sys.stdout):
        """Print label-bit/box-guess/target-time differences from the previous model."""
        if not hasattr(model_structure, 'model_differences') or not model_structure.model_differences:
            return

        differences = model_structure.model_differences
        print("\n=== DIFFERENCES FROM PREVIOUS MODEL ===\n", file=output)

        if differences.get('labels'):
            print("Label Changes:", file=output)
            for lasso_index, changes in differences['labels'].items():
                if isinstance(changes, dict) and ('added' in changes or 'removed' in changes):
                    if changes.get('added'):
                        print(f"  + Lasso L{lasso_index} added", file=output)
                    if changes.get('removed'):
                        print(f"  - Lasso L{lasso_index} removed", file=output)
                    continue
                print(f"  Lasso L{lasso_index} changed:", file=output)
                for position, change in sorted(changes.items()):
                    print(f"    Position {position}: {change['old']} -> {change['new']}", file=output)

        if differences.get('box_guesses'):
            print("\nBox Guess Changes:", file=output)
            for formula_repr, change in differences['box_guesses'].items():
                print(f"  {formula_repr}: {change['old']} -> {change['new']}", file=output)

        if differences.get('target_time'):
            change = differences['target_time']
            print(f"\nTarget Time: {change['old']} -> {change['new']}", file=output)

    def iterate_generator(self):
        """Merge bimodal-specific (label/guess) differences into each yielded model,
        matching the retired encoding's own override pattern."""
        for model in super().iterate_generator():
            if len(self.model_structures) >= 2:
                theory_diffs = self._calculate_differences(model, self.model_structures[-2])
                if hasattr(model, 'model_differences') and model.model_differences:
                    model.model_differences.update(theory_diffs)
                else:
                    model.model_differences = theory_diffs

            yield model


# Wrapper function for use in theory examples
def iterate_example(example, max_iterations=None):
    """Find multiple models for a bimodal theory example.

    Args:
        example: A BuildExample instance with a bimodal theory model
        max_iterations: Maximum number of models to find (optional)

    Returns:
        list: List of distinct model structures
    """
    iterator = BimodalModelIterator(example)

    if max_iterations is not None:
        iterator.max_iterations = max_iterations

    model_structures = iterator.iterate()

    for structure in model_structures:
        if hasattr(structure, 'model_differences') and structure.model_differences:
            def create_print_method(struct):
                def print_method(output=None):
                    iterator.display_model_differences(struct, output or sys.stdout)
                    return True
                return print_method
            structure.print_model_differences = create_print_method(structure)

    return model_structures


def iterate_example_generator(example, max_iterations=None):
    """Generator version of iterate_example that yields models incrementally.

    Args:
        example: A BuildExample instance with bimodal theory.
        max_iterations: Maximum number of models to find.

    Yields:
        Model structures as they are discovered.
    """
    if max_iterations is not None:
        if not hasattr(example, 'settings'):
            example.settings = {}
        example.settings['iterate'] = max_iterations

    iterator = BimodalModelIterator(example)
    example._iterator = iterator

    yield from iterator.iterate_generator()


# Mark the generator function for BuildModule detection
iterate_example_generator.returns_generator = True
iterate_example_generator.__wrapped__ = iterate_example_generator
