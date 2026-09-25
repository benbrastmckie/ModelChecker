"""bimodal_logic.provider - Z3OracleProvider entry point.

This module provides the Z3OracleProvider class that implements the
bimodal_harness oracle interface using the Z3 SMT solver, backed by
ModelChecker's witness-family certificate encoding for discrete (Z) time
(`model_checker.theory_lib.bimodal.semantic`).

## Change of meaning

This module previously implemented the oracle against a window-and-abundance
Z3 encoding: a bounded integer time domain `(-M, M)`, an explicit `task_rel`
relation approximating BimodalLogic's `TaskFrame` axioms (nullity, converse,
forward_comp), and a `temporal_depth`-driven sizing formula
`M = max(depth + 2, 3)` chosen to avoid boundary-vacuity artifacts in that
bounded window. That encoding, its frame-axiom approximation, and its sizing
formula are retired outright (see
`code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` for the
certificate design this module now sits on top of) -- there is no `task_rel`,
no bounded window, and no boundary-vacuity concern to size around, so none of
that machinery is repaired here, only removed.

## The certificate encoding, briefly

A countermodel is now a **witness-family certificate**: a box guess plus a
labelled bi-infinite lasso (and one witness lasso per boxed subformula guessed
false), searched for with fixed `back`/`mid`/`fwd` segment lengths (matching
`model_checker.theory_lib.bimodal.semantic.witness_registry.WitnessRegistry`).
The search is quantifier-free (no `ForAll`/`Exists`/MBQI/E-matching), so this
oracle's solves are now measured in single-digit milliseconds rather than the
seconds-to-tens-of-seconds the retired encoding needed (measured directly:
every bimodal example decides in well under 50ms under this encoding). Every
returned countermodel has already passed the theory's own independent
pure-Python re-check (`BimodalStructure`'s S3 obligation) before this provider
ever sees it -- a defect in the encoder surfaces as a loud
`ModelConstructionError`, not as a bad oracle answer.

## Frame class

`supported_frame_classes = frozenset({"ZTime"})`: the certificate encoding is
scoped to discrete (Z) time only (dense/continuous time are out of scope for
this design -- see `ADEQUACY.md`'s "Why Z-time only" section). "ZTime" here
names the same frame class BimodalLogic's own tableau-bridge protocol uses for
this theory (`~/Projects/BimodalLogic/BimodalTools/README.md`'s frame-class
vocabulary), not a Z3-side approximation label the way the retired encoding's
"Base" was.

## Never claims validity

`find_countermodel` returns `None` for exactly two cases: a genuinely
UNSAT search (no certificate exists within the configured segment lengths --
the theory's own D8 discipline: `ADEQUACY.md` section 7.4) or an unsupported
`frame_class`. Neither case is reported as "the formula is valid" -- absence
of a certificate at the searched bounds is inconclusive with respect to
validity in general (the (ADEQ) completeness direction is open), and this
provider makes no claim beyond what was actually searched. A search that
could not decide within its time/rlimit budget raises `OracleTimeoutError`
rather than returning `None`, keeping the three-valued contract (countermodel
/ no-countermodel-within-bounds / did-not-decide) intact.
"""

from __future__ import annotations

from .errors import OracleTimeoutError
from .translation import (
    json_to_prefix,
    temporal_depth,
    prefix_to_infix,
    fold_formula,
)
from .serialization import serialize_countermodel
from model_checker.utils.context import isolated_z3_context
from model_checker import ModelConstraints, Syntax
from model_checker.theory_lib.bimodal import (
    BimodalSemantics,
    BimodalProposition,
    BimodalStructure,
    bimodal_operators,
)


class Z3OracleProvider:
    """Z3-based oracle provider for bimodal logic reasoning, backed by the
    witness-family certificate encoding.

    The oracle's `supported_frame_classes = frozenset({"ZTime"})` matches the
    certificate encoding's own scope (discrete time only). See the module
    docstring for the change of meaning from the retired window-and-abundance
    encoding and the never-claims-validity discipline this provider follows.

    Attributes:
        provider_id (str): Unique identifier for this provider.
        provider_version (str): Semantic version string.
        semantics_version (str): Version string for the bimodal semantics.
        supported_frame_classes (frozenset): Set of supported frame class names.
        capabilities (dict): Dict of provider capability flags and limits.
    """

    # Class-level constants (static properties)
    provider_id = "bmlogic_z3_base_v1"
    provider_version = "0.2.0"
    semantics_version = "bimodal-logic-certificate-v0.1.0"
    supported_frame_classes = frozenset({"ZTime"})
    capabilities = {
        "max_back": 6,
        "max_mid": 4,
        "max_fwd": 6,
        "supports_enriched_tags": True,
        "z3_timeout_configurable": True,
    }

    def __init__(self):
        """Initialize the Z3OracleProvider.

        Sets up the internal semantics reference (kept as None to prevent
        cross-call state leakage).
        """
        self._semantics = None

    def _segment_lengths(self, depth: int) -> tuple[int, int, int]:
        """Choose `(back, mid, fwd)` for a formula of the given temporal
        depth, clamped to `capabilities`' declared maxima.

        The certificate search is quantifier-free and measured in single-digit
        milliseconds even at generous segment lengths, so this sizing is
        deliberately simple -- unlike the retired encoding's
        boundary-safety-driven `M = max(depth+2, 3)` formula, there is no
        vacuity artifact to size around here (the certificate's fulfilment
        condition is checked over the Lean-proved wide window regardless of
        segment length, `ADEQUACY.md` section 5). `back`/`fwd` grow with
        depth to give deeper formulas more periodic room to place their
        witnesses; `mid` stays at the class default.
        """
        back = min(max(depth + 2, 2), self.capabilities["max_back"])
        fwd = min(max(depth + 2, 2), self.capabilities["max_fwd"])
        mid = min(1, self.capabilities["max_mid"])
        return back, mid, fwd

    def find_countermodel(
        self,
        formula_json: dict,
        frame_class: str = "ZTime",
        timeout_ms: int = 5000,
        max_rlimit: int | None = None,
    ) -> dict | None:
        """Find a countermodel for the given formula JSON.

        Implements the bimodal_harness oracle interface: given a formula in JSON
        format, determines whether it is invalid (a witness-family certificate
        exists for its negation-search) and if so, returns a structured
        countermodel dict built from that certificate. Returns None for
        tautologies (no certificate found within the configured segment
        lengths) and unsupported frame classes.

        Pipeline:
            json_to_prefix() -> prefix_to_infix() ->
            Syntax([], [infix], bimodal_operators) ->
            BimodalSemantics(settings) ->
            ModelConstraints(settings, syntax, semantics, BimodalProposition) ->
            BimodalStructure(model_constraints, settings) ->
            serialize_countermodel(...)

        Args:
            formula_json: A dict with a "tag" field and tag-specific fields,
                following the JSON formula schema in translation.py.
            frame_class: The frame class to check against. Only "ZTime" is
                supported; other values return None immediately.
            timeout_ms: Maximum solver time in milliseconds.
            max_rlimit: Optional deterministic Z3 resource-unit budget --
                the load-independent complement to `timeout_ms` documented
                in `code/docs/core/TESTING_GUIDE.md` section 8.6. Unlike
                `timeout_ms` (wall-clock, so it inherits host-load
                variance), the same constraint set exhausts the same
                `max_rlimit` budget regardless of CPU load. Default-off:
                when `None` (the default) or falsy, no `max_rlimit` key is
                added to the settings dict and behavior is byte-for-byte
                unchanged, mirroring `ModelDefaults.solve()`'s own
                default-off `if max_rlimit:` guard. When set, it is passed
                through to `Z3SolverAdapter.set_rlimit()` alongside (not
                instead of) `timeout_ms`; prefer using both together for a
                test whose flakiness is specifically load-driven.

        Returns:
            A dict with countermodel fields if a certificate is found.
            None means exclusively one of: no certificate exists within the
            configured segment lengths (never reported as "the formula is
            valid" -- see the module docstring's never-claims-validity
            discipline), or `frame_class` is unsupported. None never means
            "the solver did not decide" -- that outcome raises
            OracleTimeoutError instead.

        Raises:
            OracleTimeoutError: The Z3 solver exhausted `timeout_ms` or
                `max_rlimit` (whichever fired first) without reaching a
                verdict (`structure.timeout` was true). This is an
                inconclusive result, not evidence the formula is valid --
                callers must not treat it as a countermodel-not-found case.
        """
        # Check frame class support
        if frame_class not in self.supported_frame_classes:
            return None

        depth = temporal_depth(formula_json)
        back, mid, fwd = self._segment_lengths(depth)

        # Fold formula for output (enrich primitive forms to enriched tags)
        formula_folded = fold_formula(formula_json)

        # Convert JSON formula to infix string for ModelChecker Syntax
        prefix = json_to_prefix(formula_json)
        infix = prefix_to_infix(prefix)

        # Build settings dict (D4: back/mid/fwd replace N/M/temporal_depth).
        settings = {
            'back': back,
            'mid': mid,
            'fwd': fwd,
            'max_time': timeout_ms / 1000.0,
            'expectation': True,
            'solver': 'z3',
        }
        # Deterministic, load-independent resource budget, alongside the
        # wall-clock timeout above. Optional and default-off: only added
        # when truthy, mirroring ModelDefaults.solve()'s own guard -- so no
        # existing caller's settings dict (and therefore behavior) changes.
        if max_rlimit:
            settings['max_rlimit'] = max_rlimit

        # Reset internal semantics reference to prevent leakage
        self._semantics = None

        # Run solver within isolated Z3 context to prevent state leakage
        result = None
        try:
            with isolated_z3_context():
                semantics = BimodalSemantics(settings)
                # Keep reference only within context; will be None after exit
                self._semantics = semantics
                syntax = Syntax([], [infix], bimodal_operators)
                model_constraints = ModelConstraints(
                    settings, syntax, semantics, BimodalProposition
                )
                structure = BimodalStructure(model_constraints, settings)

                # Check if the solver decided the formula at all. `timeout`
                # and `z3_model_status` are deliberately kept separate signals
                # (see model_checker.models.structure): a timeout means the
                # solver did not decide, which is not the same claim as a
                # decided UNSAT. Collapsing them into the same `None` return
                # would silently launder "gave up" into "proven valid".
                if structure.timeout:
                    self._semantics = None  # redundant with `finally`; kept for symmetry
                    raise OracleTimeoutError(
                        timeout_ms=timeout_ms,
                        temporal_depth=depth,
                        # Repurposed field (errors.py's stable constructor
                        # signature is shared with the untouched
                        # oracle/bimodal_logic/tests/test_cross_oracle_differential.py):
                        # the total certificate segment budget searched, not
                        # a bounded-window size.
                        M=back + mid + fwd,
                        max_rlimit=max_rlimit,
                    )
                if not structure.z3_model_status:
                    self._semantics = None
                    return None

                # Serialize the countermodel from the found, independently
                # re-checked certificate (BimodalStructure's own S3 hook has
                # already verified it before this line ever runs).
                result = serialize_countermodel(
                    structure=structure,
                    formula_json=formula_json,
                    formula_folded=formula_folded,
                    depth=depth,
                    back=back,
                    mid=mid,
                    fwd=fwd,
                    semantics_version=self.semantics_version,
                )
        finally:
            # Always clear the semantics reference when done
            self._semantics = None

        return result

    def validate_self(
        self, spot_check_formulas: list, timeout_ms: int = 5000
    ) -> bool:
        """Validate the oracle against a list of known-invalid formulas.

        Returns True only if all spot_check_formulas produce non-None results
        from find_countermodel() (i.e., all can find countermodels).

        Args:
            spot_check_formulas: List of JSON formula dicts that should all
                have countermodels (be invalid).
            timeout_ms: Solver budget passed through to each
                find_countermodel() call. Defaults to 5000 to match
                find_countermodel()'s own default; callers spot-checking
                formulas with non-trivial temporal_depth should pass an
                explicit wider budget so an under-sized timeout does not
                masquerade as a semantic verdict about the oracle.

        Returns:
            True if every formula produces a non-None countermodel result.
            False if any formula returns None (no countermodel found).

        Raises:
            OracleTimeoutError: propagates from find_countermodel() if any
                spot-check formula's solve does not decide within its
                budget. A spot check that cannot obtain a verdict is a
                tooling problem (an under-sized budget), not evidence the
                oracle is unsound, so it is not caught here and does not
                count as `False`.
        """
        for formula in spot_check_formulas:
            result = self.find_countermodel(formula, timeout_ms=timeout_ms)
            if result is None:
                return False
        return True
