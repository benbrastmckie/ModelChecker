"""Model structure for the bimodal theory: certificate solve, extraction, independent
re-check, and printing.

## Change of meaning

The retired encoding's `BimodalStructure` extracted world histories (`{world_id: {time:
state}}`), world arrays, and time-shift relations from a bounded `(-M, M)` Z3 model, and
printed them as time-aligned columns. That encoding is retired (see `semantic/core.py`'s own
module docstring). This module is rewritten around the certificate encoding: a world state is
a `(lasso, position)` pair on a found `WitnessFamily` (`semantic/certificate.py`), and the task
relation is the shift `(lasso, t) -> (lasso, t + d)` for every integer `d` -- not asserted by
any Z3 constraint, but true *by construction* of the certified `ShiftSet`
(`docs/ADEQUACY.md` section 3, Corollary 2.1).

## The re-check hook (obligation S3)

`__init__` is the mechanism that discharges (SOUND)'s obligation S3 (`docs/ADEQUACY.md`
sections 2 and 6.2): *whatever the search reports actually satisfies (C1)-(C4)* is decided
here, on every satisfying Z3 model, independently of the Z3 model object, by extracting a
`WitnessFamily` (`BimodalSemantics.extract_certificate`, Phase 10) and immediately re-checking
it with the pure-Python `certificate.recheck` (Phase 4). This is not a defensive test bolted on
after the fact -- it is *the* thing standing between a Z3 encoder bug and a false countermodel
report (section 6.2: "an encoder bug becomes a loud rejection, not a false report"). A verdict
other than `"countermodel"` raises `ModelConstructionError` immediately; nothing downstream
(printing, `extract_propositions`, iteration) ever sees an unverified certificate.

## Never report validity (D8)

An unsatisfiable solve leaves `self.certificate = None` and `self.target_time = None`.
Everywhere this module prints that case, the wording is "no certificate found within the
configured bounds", explicitly not a validity claim (`docs/ADEQUACY.md` section 7.4).

## The output gate (item 1)

The mandatory `recheck` guard above discharges S3 against this repository's *own* Python
decision procedures -- it cannot catch a defect shared between the Z3 encoder and `recheck`
itself, since both are this repository's code. The governing asymmetry
(`docs/TRUST_PIPELINE.md`) is that a countermodel is a positive, checkable witness: an
*independent* second implementation (`semantic/checker.py`, resolving a standalone Lean-built
`check_certificate` binary) can be run against every reported countermodel, per run, at
negligible cost (~50ms measured). The `'verify'` setting (`self.verify_mode`, mirroring
`self.semantics.verify_mode` -- see `semantic/core.py` for why this attribute is deliberately
not named `self.verify`) controls whether and how strictly that second leg runs, immediately
after the mandatory `recheck` guard:

- `'off'` -- no independent check is attempted; `semantic/checker.py` is never even asked to
  resolve. The mandatory Python re-check above still runs (it is unconditional, not part of this
  setting).
- `'auto'` (default) -- the independent check runs when a checker resolves; the countermodel is
  *always* reported, labelled either independently-checked or Python-re-checked-only. Absence of
  a checker never fails a solve.
- `'required'` -- a countermodel that cannot be independently checked is withheld: this raises
  `ModelConstructionError` instead of reporting it, naming how to obtain a checker.

A checker that resolves but whose real-invocation echo does not match what was sent
(`semantic/checker.py`'s `ProtocolFailure`) is never swallowed into "unchecked" -- it is
re-raised as loudly as the mandatory `recheck` guard's own failure, since it means the two sides
are talking about different certificates.

**Wording discipline (F2).** The checked-state label is worded from
`BimodalTools/CertificateImport.lean`'s own `Acceptance` docstring vocabulary only -- Lean
constructed a `WitnessFamily.Refutes` term for this certificate by applying a *compile-time*
kernel-checked implication to four *run-time* decisions. It never says "a kernel-checked proof
for this particular certificate" (the phrase `docs/ADEQUACY.md` section 6.2 and
`docs/TRUST_PIPELINE.md` currently use, reported as a finding for the certificate-wire hardening
task to fix, not edited here): that phrasing describes the reserved third `Acceptance` value
(per-certificate kernel checking by re-elaboration), which nothing this checker produces today.
"""

from __future__ import annotations

import sys
import time
from typing import Any, Dict, List, Optional, TextIO, Tuple

from model_checker.models.structure import ModelDefaults
from model_checker.theory_lib.errors import ModelConstructionError

from .certificate import _box_window, recheck
from .checker import ProtocolFailure, check_certificate
from .formula import Atom, Box, Formula
from .render import build_names, print_differences


class BimodalStructure(ModelDefaults):
    """Model structure for the certificate encoding: finalizes the certificate search
    before solving (D6), extracts and independently re-checks a found certificate (S3,
    D8), and prints it. See the module docstring for the change of meaning from the
    retired encoding.
    """

    def __init__(self, model_constraints: Any, settings: Dict[str, Any]) -> None:
        super().__init__(model_constraints, settings)

        # D8: never report validity. None until (and unless) a satisfying, independently
        # re-checked certificate is found.
        self.certificate = None
        self.target_time: Optional[int] = None

        # Item 1's output gate state -- always present (even for a no-certificate solve, or
        # under 'verify': 'off') so print_certificate/print_evaluation never need a hasattr
        # guard. Overwritten below once a certificate is found and 'verify' != 'off'.
        self.verify_mode: str = settings.get("verify", "auto")
        self.verification_checked = False
        self.verification_acceptance: Optional[str] = None
        self.verification_provenance: Optional[str] = None
        self.verification_reason: Optional[str] = None

        if self.z3_model_status and self.z3_model is not None:
            # Give semantics a reference to this model structure, matching every other
            # theory's convention (some operator/print helpers may need it).
            self.semantics.model_structure = self

            family, target_time = self.semantics.extract_certificate(self.z3_model)

            # Obligation S3 (docs/ADEQUACY.md section 6.2): decide (C1)-(C4) independently
            # of the Z3 model object, on every reported countermodel, and fail loudly on
            # anything else. This is deliberately not wrapped in a try/except -- a defect
            # here must surface immediately, not be swallowed into a silent "no model".
            verdict = recheck(
                family,
                premises=self.semantics._premise_formulas,
                conclusions=self.semantics._conclusion_formulas,
                target_time=target_time,
            )
            if verdict["status"] != "countermodel":
                raise ModelConstructionError(
                    "Z3 reported a satisfying model, but the certificate extracted from it "
                    "failed the independent pure-Python re-check of (C1)-(C4). This is the "
                    "fail-fast guard docs/ADEQUACY.md section 6.2 (obligation S3) exists "
                    f"for: the defect is in the Z3 constraint generators or in "
                    f"extract_certificate, not in the example. Re-check verdict: {verdict!r}",
                    theory="bimodal",
                    context={"verdict": verdict},
                    suggestion=(
                        "Inspect witness_constraints.py's constraint generators and "
                        "core.py's extract_certificate against docs/ADEQUACY.md sections "
                        "1 and 5 -- this is a soundness bug in the encoding, not in the "
                        "formula being checked."
                    ),
                )

            self.certificate = family
            self.target_time = target_time
            self.semantics.certificate = family
            self.semantics.target_time = target_time
            # main_point is the same dict object self.semantics.main_point aliases
            # (models/structure.py's own __init__ set self.main_point = self.semantics.
            # main_point), so mutating it in place keeps both in sync -- mirroring D6's
            # frame_constraints aliasing discipline.
            self.main_point["position"] = target_time

            # Item 1's output gate (module docstring, "The output gate"): the independent
            # second leg, gated by 'verify' (self.verify_mode, already set above to
            # settings['verify'] == self.semantics.verify_mode). Deliberately placed after every
            # assignment above so a withholding raise below leaves self.certificate/
            # target_time already set -- 'required' withholds the *report*, not the
            # extraction; a caller inspecting the structure after catching the error still
            # sees what was found, matching the recheck guard's own no-swallowing discipline.
            if self.verify_mode != "off":
                payload = self.semantics.export_certificate_json(family, target_time)
                try:
                    outcome = check_certificate(payload)
                except ProtocolFailure as exc:
                    raise ModelConstructionError(
                        "The independent checker resolved and responded, but its echo of "
                        "the parsed certificate does not match the exact bytes this "
                        "repository sent -- the two sides are talking about different "
                        "certificates. This is semantic/checker.py's protocol-failure "
                        f"guard, not a rejection of the countermodel itself. {exc}",
                        theory="bimodal",
                        context={"protocol_failure": str(exc)},
                        suggestion=(
                            "Inspect WitnessFamily.to_json's wire export and the checker's "
                            "own canonical-bytes parser for a mismatch -- this is a "
                            "protocol bug, not a soundness bug in the encoding."
                        ),
                    ) from exc

                if outcome.available:
                    self.verification_checked = True
                    self.verification_acceptance = outcome.verdict.get("acceptance")
                    self.verification_provenance = outcome.checker.provenance
                elif self.verify_mode == "required":
                    raise ModelConstructionError(
                        "A satisfying certificate was found, but 'verify': 'required' "
                        "demands an independent check before reporting a countermodel, and "
                        f"no checker is available. Reason: {outcome.reason}",
                        theory="bimodal",
                        context={"verify": "required", "reason": outcome.reason},
                        suggestion=(
                            "Obtain a standalone checker binary -- see docs/SETTINGS.md's "
                            "'Certificate Verification' section for BIMODAL_CHECKER_BIN and "
                            "the per-user cache location -- or relax 'verify' to 'auto' to "
                            "report the countermodel labelled as Python-re-checked only."
                        ),
                    )
                else:
                    self.verification_reason = outcome.reason

    def _setup_solver(self, model_constraints: Any) -> Any:
        """D6: finalize the certificate's global constraints before the base class reads
        `model_constraints.frame_constraints` -- the by-reference alias
        (`models/constraints.py:80`) is what makes this mutation visible there.
        `finalize_certificate()` is itself idempotent, so this is safe to call again from
        `re_solve()` or the model iterator."""
        self.semantics.finalize_certificate()
        return super()._setup_solver(model_constraints)

    # ------------------------------------------------------------------
    # Extraction helpers (world states are lasso indices; task relation is the shift)
    # ------------------------------------------------------------------

    def extract_states(self) -> Dict[str, List[str]]:
        """`{"worlds": [...], "possible": [], "impossible": []}`. A "world" here is a
        whole certified history -- one lasso -- not a `(lasso, position)` point; bimodal
        has no possible/impossible distinction, matching the retired encoding's own
        convention."""
        states: Dict[str, List[str]] = {"worlds": [], "possible": [], "impossible": []}
        if self.certificate is not None:
            states["worlds"] = [f"L{i}" for i in range(len(self.certificate.lassos))]
        return states

    def extract_evaluation_world(self) -> Optional[str]:
        """The main lasso's on-screen name (`L0`), or `None` if no certificate was found."""
        if self.certificate is None:
            return None
        return f"L{self.main_point['lasso']}"

    def extract_relations(self) -> Dict[str, Any]:
        """The task relation is the shift `(lasso, t) -> (lasso, t + d)` for every integer
        `d` -- true by construction of the certified `ShiftSet`
        (`docs/ADEQUACY.md` section 3, Corollary 2.1), not asserted by any Z3 constraint.
        Described structurally rather than enumerated, since it relates infinitely many
        pairs. Also carries `box_guesses`: one JSON-ready entry per boxed subformula in the
        closure (`formula` as its `repr`, `guess`, and for a false guess the certificate-derived
        `witness` `{lasso, position}` -- see `box_witness`)."""
        if self.certificate is None:
            return {}
        return {
            "shift": {
                "description": (
                    "(lasso, t) -> (lasso, t + d) for every integer d -- the shift action "
                    "on the certified ShiftSet (docs/ADEQUACY.md section 3)"
                ),
            },
            "box_guesses": [
                {
                    "formula": repr(child),
                    "guess": guess,
                    "witness": (
                        None if witness is None
                        else {"lasso": witness[0], "position": witness[1]}
                    ),
                }
                for child, guess, witness in self.box_guesses()
            ],
        }

    def extract_propositions(self) -> Dict[Any, Dict[str, Optional[bool]]]:
        """`{sentence_letter: {"L{i}": truth_value_or_None}}`, read at `self.target_time`
        via each sentence letter's own built `BimodalProposition` (Phase 11)."""
        propositions: Dict[Any, Dict[str, Optional[bool]]] = {}
        if self.certificate is None:
            return propositions
        if not hasattr(self, 'syntax') or not hasattr(self.syntax, 'propositions'):
            return propositions

        for _prop_name, sentence_obj in self.syntax.propositions.items():
            sentence_letter = getattr(sentence_obj, 'sentence_letter', None)
            proposition = getattr(sentence_obj, 'proposition', None)
            if sentence_letter is None or proposition is None:
                continue
            propositions[sentence_letter] = {}
            for lasso_index in range(len(self.certificate.lassos)):
                world_name = f"L{lasso_index}"
                try:
                    propositions[sentence_letter][world_name] = proposition.truth_value_at(
                        lasso_index, self.target_time
                    )
                except Exception:
                    # Best-effort export helper -- skip a lasso that cannot be evaluated
                    # rather than aborting the whole export.
                    pass
        return propositions

    # ------------------------------------------------------------------
    # Printing
    # ------------------------------------------------------------------

    def _format_label(self, label) -> str:
        """A label rendered over its atom valuations (report 01 section 4.4): the sorted
        base names of every `Atom` the label contains, e.g. `{A,B}`, or `{}` if none."""
        atoms = sorted(f.base for f in label if isinstance(f, Atom))
        return "{" + ",".join(atoms) + "}"

    def _format_lasso(self, lasso_index: int, lasso: Any) -> str:
        """`(back)^w | mid | (fwd)^w`, marking the evaluation position (if it falls in
        this lasso's printed window) with brackets."""
        registry = self.semantics.witness_registry
        mark_slot: Optional[int] = None
        if lasso_index == self.main_point.get("lasso") and self.target_time is not None:
            mark_slot = registry.wrap(self.target_time)

        def _segment(labels, start_slot: int) -> List[str]:
            parts = []
            for offset, label in enumerate(labels):
                text = self._format_label(label)
                if mark_slot is not None and start_slot + offset == mark_slot:
                    text = f"[{text}]"
                parts.append(text)
            return parts

        back_parts = _segment(lasso.back, 0)
        mid_parts = _segment(lasso.mid, lasso.nb)
        fwd_parts = _segment(lasso.fwd, lasso.nb + lasso.nm)

        back_str = f"({', '.join(back_parts)})^w"
        fwd_str = f"({', '.join(fwd_parts)})^w"
        mid_str = ", ".join(mid_parts) if mid_parts else "-"
        return f"{back_str} | {mid_str} | {fwd_str}"

    def box_witness(self, child: Formula) -> Optional[Tuple[int, int]]:
        """The `(lasso_index, t)` at which the certificate falsifies `Box(child)`, or `None`
        when the box is guessed true (or there is no certificate).

        Computed from the certificate alone: the pair returned satisfies exactly the (C3)
        predicate `child not in lassos[i].label(t)` for a `t` in `_box_window(lassos[i])`.
        `WitnessRegistry._witness_lassos` is deliberately never consulted -- its index is
        reserved capacity, not provenance (`box_faithfulness_constraints` lets any lasso
        falsify a box, so the reserved lasso may not be the one that does). A non-main
        falsifier is preferred when one exists, since "another history" is what a reader
        expects a box witness to be; the main lasso is reported honestly otherwise.
        """
        if self.certificate is None or self.certificate.bx_of(child):
            return None
        lassos = self.certificate.lassos
        for lasso_index, lasso in enumerate(lassos):
            if lasso_index == 0:
                continue
            for t in _box_window(lasso):
                if child not in lasso.label(t):
                    return lasso_index, t
        for t in _box_window(lassos[0]):
            if child not in lassos[0].label(t):
                return 0, t
        return None

    def box_guesses(self) -> List[Tuple[Formula, bool, Optional[Tuple[int, int]]]]:
        """`(child, guess, witness)` for every boxed subformula in the closure, sorted by
        `repr(child)` for determinism; `witness` is `box_witness(child)`."""
        if self.certificate is None:
            return []
        children = sorted(
            {f.child for f in self.semantics.witness_registry.closure if isinstance(f, Box)},
            key=repr,
        )
        return [(child, self.certificate.bx_of(child), self.box_witness(child)) for child in children]

    def _verification_label(self) -> str:
        """One-line rendering of item 1's output gate state -- see the module docstring's
        "The output gate" and "Wording discipline (F2)" sections for the contract this
        wording follows. Never says "kernel-checked proof": that phrase names the reserved
        third `Acceptance` value (per-certificate kernel checking), which nothing this
        checker produces today."""
        if self.verify_mode == "off":
            return (
                "independent check skipped ('verify': 'off'); re-checked by this "
                "repository's own pure-Python decision procedures only"
            )
        if self.verification_checked:
            acceptance = self.verification_acceptance or "unknown"
            provenance = (
                f", checkout {self.verification_provenance}"
                if self.verification_provenance
                else ""
            )
            return (
                "independently checked -- Lean constructed a WitnessFamily.Refutes term "
                "for this certificate by applying a compile-time kernel-checked "
                f"implication to four run-time decisions (acceptance: {acceptance}"
                f"{provenance})"
            )
        return (
            "re-checked by this repository's own pure-Python decision procedures only "
            f"(no independent checker available: {self.verification_reason})"
        )

    def print_certificate(self, output: TextIO = sys.__stdout__) -> None:
        """Print every lasso in the found certificate, the independent-verification label
        (item 1's output gate), the boxed-subformula table with each guess, and each false
        box's witness history and position -- report 01 section 4.4's output shape. Prints
        the no-certificate case as an explicit non-validity-claim message (D8) instead."""
        print("Certificate:", file=output)
        if self.certificate is None:
            print(
                f"  No certificate found within the configured bounds "
                f"(back={self.semantics.back}, mid={self.semantics.mid}, "
                f"fwd={self.semantics.fwd}). This is not a validity claim "
                f"(docs/ADEQUACY.md section 7.4).\n",
                file=output,
            )
            return

        print(f"  Verification: {self._verification_label()}", file=output)
        for i, lasso in enumerate(self.certificate.lassos):
            role = "main" if i == 0 else f"witness {i}"
            print(f"  L{i} ({role}): {self._format_lasso(i, lasso)}", file=output)
        print(file=output)

        print("Boxed subformulas:", file=output)
        guesses = self.box_guesses()
        if not guesses:
            print("  (none)", file=output)
        for child, guess, witness in guesses:
            print(f"  Box({child!r}) = {guess}", file=output)
            if witness is not None:
                witness_index, position = witness
                witness_lasso = self.certificate.lassos[witness_index]
                print(
                    f"    Witness: L{witness_index} at position {position} "
                    f"({self._format_lasso(witness_index, witness_lasso)})",
                    file=output,
                )
        print(file=output)

    def print_evaluation(self, output: TextIO = sys.__stdout__) -> None:
        """Print the evaluation point: the main lasso and the extracted target time, or
        the explicit no-certificate message (D8: an unsatisfiable solve is rendered, never
        raised as an error -- it is not a validity claim, just a fact to report)."""
        if self.certificate is None:
            print(
                f"No certificate found within the configured bounds "
                f"(back={self.semantics.back}, mid={self.semantics.mid}, "
                f"fwd={self.semantics.fwd}). This is not a validity claim.\n",
                file=output,
            )
            return

        print(
            f"\nEvaluation Point:\n"
            f"  Main lasso: L{self.main_point['lasso']}\n"
            f"  Target position: {self.target_time}\n"
            f"  Verification: {self._verification_label()}\n",
            file=output,
        )

    def print_model_differences(self, output: TextIO = sys.stdout) -> None:
        """Print this model's label-bit/box-guess/target-time differences from the previous
        iterate step (`iterate.py`'s `_calculate_differences`, merged into
        `self.model_differences` by `BimodalModelIterator.iterate_generator`) in the shape
        `docs/ITERATE.md` documents. This is the method `builder/runner.py` calls on the live
        `iterate: N` path, so it must exist here and not only on the iterator; the framework
        default would print the generic structural-metrics block, which is meaningless for a
        theory whose model is a label/guess assignment."""
        differences = getattr(self, "model_differences", None)
        if not differences:
            return
        print_differences(differences, output, build_names(getattr(self, "syntax", None)))

    def print_all(
        self,
        default_settings: Dict[str, Any],
        example_name: str,
        theory_name: str,
        output: TextIO = sys.__stdout__,
    ) -> None:
        """Print complete model information: info header, the certificate (every lasso
        plus the boxed-subformula table), the evaluation point, the interpreted premises/
        conclusions, and the raw Z3 model if requested."""
        model_status = self.z3_model_status
        self.print_info(model_status, self.settings, example_name, theory_name, output)
        if model_status:
            self.print_certificate(output)
            self.print_evaluation(output)
            self.print_input_sentences(output)
            self.print_model(output)
            if output is sys.__stdout__:
                total_time = round(time.time() - self.start_time, 4)
                print(f"Total Run Time: {total_time} seconds\n", file=output)
            print(f"\n{'='*40}", file=output)
            return

    def print_to(
        self,
        default_settings: Dict[str, Any],
        example_name: str,
        theory_name: str,
        print_constraints: Optional[bool] = None,
        output: TextIO = sys.__stdout__,
    ) -> None:
        """Print all model elements to `output`, including a timeout notice if the solve
        timed out without finding a model."""
        if print_constraints is None:
            print_constraints = self.settings["print_constraints"]

        actual_timeout = hasattr(self, 'z3_model_runtime') and self.z3_model_runtime >= self.max_time
        if actual_timeout and (not hasattr(self, 'z3_model') or self.z3_model is None):
            print(f"\nTIMEOUT: Model search exceeded maximum time of {self.max_time} seconds", file=output)
            print(f"No model for example {example_name} found before timeout.", file=output)
            print(f"Try increasing max_time > {self.max_time}.\n", file=output)

        self.print_all(self.settings, example_name, theory_name, output)
        if print_constraints and self.unsat_core is not None:
            self.print_grouped_constraints(output)

    def save_to(
        self,
        example_name: str,
        theory_name: str,
        include_constraints: bool,
        output: TextIO,
    ) -> None:
        """Save all model elements to `output`. Fixes a pre-existing bug in the retired
        encoding's version of this method, which omitted `self.settings` as `print_all`'s
        first (required) argument -- matching the logos/exclusion theories' own
        `save_to` call shape."""
        constraints = self.model_constraints.all_constraints
        self.print_all(self.settings, example_name, theory_name, output)
        self.build_test_file(output)
        if include_constraints:
            print("# Satisfiable constraints", file=output)
            print(f"all_constraints = {constraints}", file=output)
