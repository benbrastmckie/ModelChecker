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

## Printed output

`print_all` prints, in order: the framework header with `_print_model_details` overridden to
show `Search bounds: back=B, mid=M, fwd=F (N lassos: 1 main + K reserved witnesses)` in place
of the meaningless `Atomic States`; the `Histories:` block -- a one-line legend, then one row
per lasso, `L{i}`, a role column (`main` / `witness for □χ` / `reserved, unused`, derived from
the certificate scan in `box_guesses`, never from the registry's reserved index), and the
history as a time-labelled arrow chain `… (-2:B) ⟹ (-1:B) | (0:B) | (+1:B) ⟹ [+2:A] …`: one
`(t:atoms)` state per position of the registry's `target_window()`, `⟹` joining adjacent
states within the periodic back/fwd segments, `|` between the back/mid/fwd segments (an empty
`mid` collapses to a single `|`), `…` marking the periodic repetition, `[ ]` marking the
evaluation point, `∅` for an empty label, and each position's column padded to its widest cell
so times align across rows; a `Box guesses:` table (`formula  true|false  falsified at L{i}, t=±t`);
then `Evaluation point: L0 at t=-2` and exactly one `Verification:` line. Formulas render via
`semantic/render.py` in the user's notation; every non-ASCII glyph goes through
`utils/glyphs.py`; every color is gated by `output.color.use_colors` and never carries
information alone. See `docs/ARCHITECTURE.md`'s "Rendering policy".
"""

from __future__ import annotations

import sys
import time
from typing import Any, Dict, List, Optional, TextIO, Tuple

from model_checker.models.structure import ModelDefaults
from model_checker.output.color import use_colors
from model_checker.utils.glyphs import glyph
from model_checker.theory_lib.errors import ModelConstructionError

from .certificate import _box_window, recheck
from .checker import ProtocolFailure, check_certificate
from .formula import Atom, Box, Formula
from .render import build_names, print_differences, render, signed_time


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

    # ------------------------------------------------------------------
    # Printing
    # ------------------------------------------------------------------

    # ANSI palette (gated by `use_colors(output)` at every use):
    _BLUE = "\033[34m"    # the evaluation point (main-lasso row, `Evaluation point:` value)
    _GRAY = "\033[90m"    # reserved-but-unused witness rows
    _GREEN = "\033[32m"   # a box guessed true
    _RED = "\033[31m"     # a box guessed false
    _RESET = "\033[0m"

    def _names(self) -> Dict[Formula, str]:
        """Reverse-`translate` map over the example's sentences (`render.build_names`)."""
        return build_names(getattr(self, "syntax", None))

    def _lasso_count(self) -> int:
        """Lassos in the search: the certificate's when one was found, else the registry's
        allocation (`finalize_certificate`'s `_active_lassos`: main plus one reserved witness
        per boxed subformula)."""
        if self.certificate is not None:
            return len(self.certificate.lassos)
        return len(getattr(self.semantics, "_active_lassos", None) or [0])

    def _print_model_details(self, theory_name: str, output: TextIO) -> None:
        """`Search bounds: ...` in place of the framework's `Atomic States: N` -- the
        certificate encoding has no atomic-state count (`N` is meaningless here); the bounds
        and the lasso allocation are what actually shaped the search."""
        count = self._lasso_count()
        witnesses = count - 1
        if witnesses == 0:
            detail = "1 lasso: main only"
        else:
            plural = "es" if witnesses != 1 else ""
            detail = f"{count} lassos: 1 main + {witnesses} reserved witness{plural}"
        print(
            f"Search bounds: back={self.semantics.back}, mid={self.semantics.mid}, "
            f"fwd={self.semantics.fwd} ({detail})\n",
            file=output,
        )
        print(f"Semantic Theory: {theory_name}\n", file=output)

    def _format_label(self, label, output: TextIO) -> str:
        """A label over its atom valuation: a single atom bare (`A`), several as `{A,B}` so
        the slot separator stays unambiguous, none as the `∅` glyph."""
        atoms = sorted(f.base for f in label if isinstance(f, Atom))
        if not atoms:
            return glyph("EMPTY_SET", output)
        if len(atoms) == 1:
            return atoms[0]
        return "{" + ",".join(atoms) + "}"

    def _format_state(self, t: int, label, output: TextIO, marked: bool) -> str:
        """`(t:atoms)` -- the signed time and the label's atoms -- or `[t:atoms]` when this
        is the evaluation point (width-neutral: brackets swap for parentheses)."""
        body = f"{signed_time(t)}:{self._format_label(label, output)}"
        return f"[{body}]" if marked else f"({body})"

    def _history_cells(self, index: int, lasso: Any, output: TextIO) -> List[str]:
        """One rendered cell per position of the registry's `target_window()` (`-back ..
        mid+fwd-1`), the evaluation point marked on the main lasso. Fails fast if this
        lasso's segment lengths disagree with the registry's: cross-row alignment assumes
        every lasso shares `back`/`mid`/`fwd` (which `extract_certificate` guarantees)."""
        registry = self.semantics.witness_registry
        if (lasso.nb, lasso.nm, lasso.nf) != (registry.nb, registry.nm, registry.nf):
            raise ValueError(
                f"lasso L{index} has segments back={lasso.nb}, mid={lasso.nm}, fwd={lasso.nf} "
                f"but the search bounds are back={registry.nb}, mid={registry.nm}, "
                f"fwd={registry.nf}; histories cannot be aligned"
            )
        is_main = index == self.main_point.get("lasso") and self.target_time is not None
        return [
            self._format_state(t, lasso.label(t), output, is_main and t == self.target_time)
            for t in registry.target_window()
        ]

    def _join_history(self, cells: List[str], widths: List[int], output: TextIO) -> str:
        """`… back ⟹ back | mid | fwd ⟹ fwd …`: each cell left-justified to its position's
        column width (`widths[i]`, the widest cell at that position over all lassos, so the
        joiners line up across rows), ` ⟹ ` joining adjacent states within the back segment
        and within the fwd segment, ` | ` between segments -- an empty `mid` yields exactly one
        ` | ` between back and fwd, never `| |` -- and `…` bracketing the periodic back and fwd
        segments. Padding is internal; the last fwd cell is not padded, so rows never end in
        stray spaces."""
        registry = self.semantics.witness_registry
        arrow = f" {glyph('DOUBLE_ARROW', output)} "
        ellipsis = glyph("ELLIPSIS", output)
        padded = [f"{cell:<{width}}" for cell, width in zip(cells, widths)]
        padded[-1] = cells[-1]
        back = padded[:registry.nb]
        mid = padded[registry.nb:registry.nb + registry.nm]
        fwd = padded[registry.nb + registry.nm:]
        segments = [arrow.join(back)]
        if mid:
            segments.append(arrow.join(mid))
        segments.append(arrow.join(fwd))
        return f"{ellipsis} {' | '.join(segments)} {ellipsis}"

    def _print_history_lines(self, output: TextIO) -> None:
        """One aligned arrow-chain row per lasso: name, role, history. Column widths per
        position come from the rendered cells (ASCII glyph fallbacks included), so equal
        times align across rows."""
        roles = self._lasso_roles(output)
        colored = use_colors(output)
        lassos = self.certificate.lassos
        name_width = max(len(f"L{i}") for i in range(len(lassos)))
        role_width = max(len(role) for role in roles.values())
        cells = [self._history_cells(index, lasso, output) for index, lasso in enumerate(lassos)]
        widths = [max(len(row[i]) for row in cells) for i in range(len(cells[0]))]
        for index, row in enumerate(cells):
            color = ""
            if colored and index == self.main_point.get("lasso"):
                color = self._BLUE
            elif colored and roles[index] == "reserved, unused":
                color = self._GRAY
            reset = self._RESET if color else ""
            print(
                f"  {color}{f'L{index}':<{name_width}}  {roles[index]:<{role_width}}  "
                f"{self._join_history(row, widths, output)}{reset}",
                file=output,
            )

    def _lasso_roles(self, output: TextIO) -> Dict[int, str]:
        """`main` for index 0; `witness for □χ` for a lasso the certificate scan names as a
        falsifier (`box_witness`); `reserved, unused` otherwise. Never derived from the
        registry's reservation, which is capacity, not provenance."""
        names = self._names()
        witnessed: Dict[int, List[Formula]] = {}
        for child, _guess, witness in self.box_guesses():
            if witness is not None and witness[0] != 0:
                witnessed.setdefault(witness[0], []).append(child)
        roles = {0: "main"}
        for index in range(1, self._lasso_count()):
            if index in witnessed:
                boxes = ", ".join(render(Box(child), output, names) for child in witnessed[index])
                roles[index] = f"witness for {boxes}"
            else:
                roles[index] = "reserved, unused"
        return roles

    def _slot_name(self, t: int) -> str:
        """`back[i]` / `mid[i]` / `fwd[i]`: which segment slot position `t` reads
        (`LabelledLasso.label`'s decoding)."""
        registry = self.semantics.witness_registry
        if t < 0:
            return f"back[{t % registry.nb}]"
        if t < registry.nm:
            return f"mid[{t}]"
        return f"fwd[{(t - registry.nm) % registry.nf}]"

    def _print_history_table(self, output: TextIO) -> None:
        """The `align_vertically` view: one row per representative position
        (`target_window()`, `-back .. mid+fwd-1`) with its signed time and slot, one column
        per lasso headed by `L{i} {role}`; the main lasso's cell at the target is bracketed,
        and that row is bold when colors are on. Column widths come from the rendered cells,
        so ASCII glyph fallbacks never break alignment."""
        lassos = self.certificate.lassos
        roles = self._lasso_roles(output)
        colored = use_colors(output)
        main_index = self.main_point.get("lasso")
        positions = list(self.semantics.witness_registry.target_window())

        headers = [f"L{index} {roles[index]}" for index in range(len(lassos))]
        cells: List[List[str]] = []
        for t in positions:
            row = []
            for index, lasso in enumerate(lassos):
                text = self._format_label(lasso.label(t), output)
                if index == main_index and t == self.target_time:
                    text = f"[{text}]"
                row.append(text)
            cells.append(row)
        widths = [
            max([len(headers[column])] + [len(row[column]) for row in cells])
            for column in range(len(lassos))
        ]
        time_width = max(len("t"), *(len(signed_time(t)) for t in positions))
        slot_width = max(len("slot"), *(len(self._slot_name(t)) for t in positions))

        def line(time_text: str, slot_text: str, row: List[str]) -> str:
            body = " | ".join(f"{cell:<{widths[i]}}" for i, cell in enumerate(row))
            return f"  {time_text:>{time_width}}  {slot_text:<{slot_width}}  | {body}".rstrip()

        print(line("t", "slot", headers), file=output)
        rule_width = 2 + time_width + 2 + slot_width + 2
        print("  " + "-" * (rule_width - 2) + "+" + "-" * (sum(widths) + 3 * len(widths) - 1), file=output)
        bold, reset = ("\033[1m", self._RESET) if colored else ("", "")
        for t, row in zip(positions, cells):
            text = line(signed_time(t), self._slot_name(t), row)
            if t == self.target_time:
                text = f"{bold}{text}{reset}"
            print(text, file=output)

    def _print_box_guesses(self, output: TextIO) -> None:
        """`Box guesses:` table: formula (user notation), guess, and for a false guess the
        certificate-derived falsifier `falsified at L{i}, t=±t`."""
        print("Box guesses:", file=output)
        guesses = self.box_guesses()
        if not guesses:
            print("  (none)", file=output)
            return
        names = self._names()
        colored = use_colors(output)
        rows = []
        for child, guess, witness in guesses:
            detail = ""
            if witness is not None:
                detail = f"falsified at L{witness[0]}, t={signed_time(witness[1])}"
            rows.append((render(Box(child), output, names), guess, detail))
        formula_width = max(len(text) for text, _, _ in rows)
        for text, guess, detail in rows:
            value = f"{'true' if guess else 'false':<5}"
            color = (self._GREEN if guess else self._RED) if colored else ""
            reset = self._RESET if colored else ""
            print(f"  {text:<{formula_width}}  {color}{value}{reset}  {detail}".rstrip(), file=output)

    def _verification_label(self) -> str:
        """One-line rendering of item 1's output gate state -- see the module docstring's
        "The output gate" and "Wording discipline (F2)" sections for the contract this
        wording follows. Never says "kernel-checked proof": that phrase names the reserved
        third `Acceptance` value (per-certificate kernel checking), which nothing this
        checker produces today. The checkout hash is shortened to 12 hex characters."""
        if self.verify_mode == "off":
            return (
                "independent check skipped ('verify': 'off'); re-checked by this "
                "repository's own pure-Python decision procedures only"
            )
        if self.verification_checked:
            acceptance = self.verification_acceptance or "unknown"
            provenance = (
                f", checkout {self.verification_provenance[:12]}"
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
        """Print the `Histories:` block: the legend, one arrow-chain row per lasso (name,
        role, history with the evaluation point marked) -- or the `-a` time-aligned table --
        and the `Box guesses:` table with each false box's certificate-derived witness. Prints
        the no-certificate case as an explicit non-validity-claim message (D8) instead. The
        method keeps its name (the framework calls it): it prints the certificate's
        histories."""
        if self.certificate is None:
            print("Histories:", file=output)
            print(
                f"  No certificate found within the configured bounds "
                f"(back={self.semantics.back}, mid={self.semantics.mid}, "
                f"fwd={self.semantics.fwd}). This is not a validity claim "
                f"(docs/ADEQUACY.md section 7.4).\n",
                file=output,
            )
            return

        if self.settings.get("align_vertically", False):
            print(
                "Histories:  (rows are representative positions; back repeats leftward, "
                "fwd rightward; [ ] marks the evaluation point)",
                file=output,
            )
            self._print_history_table(output)
        else:
            arrow = glyph("DOUBLE_ARROW", output)
            ellipsis = glyph("ELLIPSIS", output)
            print(
                f"Histories:  (one row per lasso: (t:atoms) states joined by {arrow}, "
                f"{ellipsis} marks the periodic back/fwd segments, | separates back | mid | fwd, "
                "[ ] marks the evaluation point)",
                file=output,
            )
            self._print_history_lines(output)
        print(file=output)
        self._print_box_guesses(output)
        print(file=output)

    def print_evaluation(self, output: TextIO = sys.__stdout__) -> None:
        """Print the evaluation point (`L0 at t=-2`) and the single `Verification:` line, or
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

        colored = use_colors(output)
        blue, reset = (self._BLUE, self._RESET) if colored else ("", "")
        point = f"L{self.main_point['lasso']} at t={signed_time(self.target_time)}"
        print(f"Evaluation point: {blue}{point}{reset}", file=output)
        print(f"Verification: {self._verification_label()}\n", file=output)

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
        """Print complete model information: info header, the certificate block (every
        lasso plus the box-guess table -- or the D8 no-certificate message), the evaluation
        point and verification line, the interpreted premises/conclusions, and the raw Z3
        model if requested."""
        model_status = self.z3_model_status
        self.print_info(model_status, self.settings, example_name, theory_name, output)
        # The certificate block handles both cases: with no certificate it prints the D8
        # non-validity-claim message exactly once (print_evaluation is skipped, since its
        # own no-certificate wording exists only for standalone callers).
        self.print_certificate(output)
        if self.certificate is None:
            print(f"\n{'='*40}", file=output)
            return
        self.print_evaluation(output)
        self.print_input_sentences(output)
        self.print_model(output)
        if output is sys.__stdout__:
            total_time = round(time.time() - self.start_time, 4)
            print(f"Total Run Time: {total_time} seconds\n", file=output)
        print(f"\n{'='*40}", file=output)

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
