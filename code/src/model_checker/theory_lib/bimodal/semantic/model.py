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
"""

from __future__ import annotations

import sys
import time
from typing import Any, Dict, List, Optional, TextIO

from model_checker.models.structure import ModelDefaults
from model_checker.theory_lib.errors import ModelConstructionError

from .certificate import _box_window, recheck
from .formula import Atom, Box, Formula


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
            states["worlds"] = [f"lasso{i}" for i in range(len(self.certificate.lassos))]
        return states

    def extract_evaluation_world(self) -> Optional[str]:
        """The main lasso's name, or `None` if no certificate was found."""
        if self.certificate is None:
            return None
        return f"lasso{self.main_point['lasso']}"

    def extract_relations(self) -> Dict[str, Any]:
        """The task relation is the shift `(lasso, t) -> (lasso, t + d)` for every integer
        `d` -- true by construction of the certified `ShiftSet`
        (`docs/ADEQUACY.md` section 3, Corollary 2.1), not asserted by any Z3 constraint.
        Described structurally rather than enumerated, since it relates infinitely many
        pairs."""
        if self.certificate is None:
            return {}
        return {
            "shift": {
                "description": (
                    "(lasso, t) -> (lasso, t + d) for every integer d -- the shift action "
                    "on the certified ShiftSet (docs/ADEQUACY.md section 3)"
                ),
            }
        }

    def extract_propositions(self) -> Dict[Any, Dict[str, Optional[bool]]]:
        """`{sentence_letter: {"lasso{i}": truth_value_or_None}}`, read at `self.target_time`
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
                world_name = f"lasso{lasso_index}"
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

    def _first_missing_position(self, lasso: Any, formula: Formula) -> Optional[int]:
        """The first position (in `certificate.py`'s narrower, one-period `_box_window`)
        where `formula` is absent from `lasso`'s label -- the concrete witness position
        for a box guessed false."""
        for t in _box_window(lasso):
            if formula not in lasso.label(t):
                return t
        return None

    def print_certificate(self, output: TextIO = sys.__stdout__) -> None:
        """Print every lasso in the found certificate, the boxed-subformula table with
        each guess, and each false box's witness history and position -- report 01
        section 4.4's output shape. Prints the no-certificate case as an explicit
        non-validity-claim message (D8) instead."""
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

        for i, lasso in enumerate(self.certificate.lassos):
            role = "main" if i == 0 else f"witness {i}"
            print(f"  L{i} ({role}): {self._format_lasso(i, lasso)}", file=output)
        print(file=output)

        print("Boxed subformulas:", file=output)
        box_children = sorted(
            {f.child for f in self.semantics.witness_registry.closure if isinstance(f, Box)},
            key=repr,
        )
        if not box_children:
            print("  (none)", file=output)
        for child in box_children:
            guess = self.certificate.bx_of(child)
            print(f"  Box({child!r}) = {guess}", file=output)
            if not guess:
                witness_index = self.semantics.witness_registry._witness_lassos.get(child)
                if witness_index is not None and witness_index < len(self.certificate.lassos):
                    witness_lasso = self.certificate.lassos[witness_index]
                    position = self._first_missing_position(witness_lasso, child)
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
            f"  Target position: {self.target_time}\n",
            file=output,
        )

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
