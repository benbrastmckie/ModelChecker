"""Proposition implementation for the bimodal theory: certificate-encoding labels.

This module contains `BimodalProposition`, representing propositional content at
`(lasso, position)` evaluation points over a found `WitnessFamily` certificate.

## Change of meaning

The retired encoding evaluated propositions over `(world_id, time)` points drawn from a
bounded `(-M, M)` time domain and a `BitVec[N]`-valued world-state array, with `contingent`/
`disjoint` settings gating extra Z3 constraints on sentence letters. That encoding is retired
(see `semantic/core.py`'s own module docstring); `BimodalProposition` is rewritten against the
certificate encoding's own world-state shape: a world state is a `(lasso, position)` pair
directly (there is no separate finite "state" abstraction underneath it -- see
`docs/ADEQUACY.md` section 3, `W := {0, ..., k} x Z`), and truth values come from **labels**,
not from a Z3-evaluated `truth_condition` function.

## Labels already decide every closure member, not just atoms

`BimodalSemantics.extract_certificate` (Phase 10) reads *every* closure formula's label bit
into the extracted `WitnessFamily`'s labels -- compounds included, not only atoms -- because
local coherence (`finalize_certificate`'s constraints) ties every compound's bit to its
constituents' bits. So `truth_value_at` for *any* sentence in scope (atomic or compound) is a
single membership test, `translate(sentence) in family.lassos[lasso].label(position)`; no
recursive per-operator evaluation and no Z3 re-evaluation is needed here at all -- the atomic
and complex cases coincide.

## `proposition_constraints` is empty

D4 removes `contingent`/`disjoint` from the settings entirely, and atoms are deliberately
unconstrained by design (`docs/ADEQUACY.md` Lemma 4's atom case: `M, tau_i, t |= p` iff
`atom p in L_i(t)` is an identity, not an appeal to a valuation clause). So there is nothing
left for `proposition_constraints` to assert.

## No certificate: propositions are unevaluated, not false

When the search reports no certificate (`model_structure.certificate is None` -- D8, never a
validity claim), a proposition's truth value is `None` at every point, matching the framework's
own `set_colors` convention for "neither true nor false" (rendered as a warning, not silently
coerced to `False`).
"""

from __future__ import annotations

import sys
from typing import Any, Dict, List, Optional, Set, Tuple

from model_checker.models.proposition import PropositionDefaults
from model_checker.utils import pretty_set_print

from .formula import Formula, translate


class BimodalProposition(PropositionDefaults):
    """Propositional content over the certificate encoding: truth values are label
    membership tests at `(lasso, position)` points on a found `WitnessFamily`. See the
    module docstring for the change of meaning from the retired encoding.
    """

    def __init__(
        self,
        sentence: Any,
        model_structure: Any,
        eval_lasso: Any = 'main',
        eval_position: Any = 'now',
    ) -> None:
        """Initialize a BimodalProposition.

        Args:
            sentence: The sentence this proposition represents.
            model_structure: The `BimodalStructure` (a later phase) this proposition is
                interpreted in. Duck-typed here on `.certificate`, `.target_time`, and the
                base class's own `.semantics`/`.main_point`/`.model_constraints` contract,
                since Phase 11 precedes the Phase 12 structure rewrite.
            eval_lasso: `'main'` uses `model_structure.main_point["lasso"]`; an `int` is
                used directly as a lasso index.
            eval_position: `'now'` uses `model_structure.main_point["position"]` (the
                certificate's extracted target time, or `None` before/without a solve);
                an `int` is used directly.
        """
        super().__init__(sentence, model_structure)

        self.formula: Formula = translate(sentence)

        if eval_lasso == 'main':
            self.eval_lasso = self.model_structure.main_point["lasso"]
        elif isinstance(eval_lasso, int):
            self.eval_lasso = eval_lasso
        else:
            raise ValueError("eval_lasso must be 'main' or an integer lasso index")

        if eval_position == 'now':
            self.eval_position = self.model_structure.main_point["position"]
        elif isinstance(eval_position, int):
            self.eval_position = eval_position
        else:
            raise ValueError("eval_position must be 'now' or an integer position")

        # {lasso_index: (true_positions, false_positions)} over the representative window
        # (see find_extension's docstring for why that window suffices).
        self.extension: Dict[int, Tuple[List[int], List[int]]] = self.find_extension()

        self.truth_set, self.false_set = self._find_proposition_at(self.eval_position)

    def __eq__(self, other: Any) -> bool:
        return self.extension == other.extension and self.name == other.name

    def __repr__(self) -> str:
        return f"< {pretty_set_print(self.truth_set)}, {pretty_set_print(self.false_set)} >"

    def proposition_constraints(self, sentence_letter: Any) -> List[Any]:
        """No constraints: atoms are deliberately unconstrained (see the module
        docstring), and `contingent`/`disjoint` no longer exist as settings (D4)."""
        return []

    def find_extension(self) -> Dict[int, Tuple[List[int], List[int]]]:
        """Compute `{lasso_index: (true_positions, false_positions)}` over the
        certificate's representative position window.

        The certified carrier is infinite (`(lasso, t)` for every integer `t`), but every
        label is periodic (`LabelledLasso.label`), so the finitely many representative
        positions `self.semantics.witness_registry.target_window()` already enumerates --
        one per slot, `back`-then-`mid`-then-`fwd` -- determine the truth value at every
        integer position sharing that slot. This mirrors `extract_certificate`'s own use of
        the same window (Phase 10).

        Returns `{}` if no certificate was found (D8: nothing here claims validity or
        constructs a phantom model).
        """
        certificate = getattr(self.model_structure, 'certificate', None)
        if certificate is None:
            return {}

        window = list(self.semantics.witness_registry.target_window())
        extension: Dict[int, Tuple[List[int], List[int]]] = {}
        for lasso_index, lasso in enumerate(certificate.lassos):
            true_positions: List[int] = []
            false_positions: List[int] = []
            for t in window:
                if self.formula in lasso.label(t):
                    true_positions.append(t)
                else:
                    false_positions.append(t)
            extension[lasso_index] = (true_positions, false_positions)
        return extension

    def truth_value_at(self, eval_lasso: int, eval_position: int) -> Optional[bool]:
        """Whether this proposition is true at `(eval_lasso, eval_position)`.

        Returns `None` (neither true nor false) if no certificate was found, or if
        `eval_lasso` is not one of the certificate's lassos -- matching the framework's own
        `set_colors` convention for an unevaluated proposition, rather than silently
        defaulting to `False`.
        """
        certificate = getattr(self.model_structure, 'certificate', None)
        if certificate is None:
            return None
        if not (0 <= eval_lasso < len(certificate.lassos)):
            return None
        return self.formula in certificate.lassos[eval_lasso].label(eval_position)

    def _find_proposition_at(self, eval_position: Optional[int]) -> Tuple[Set[int], Set[int]]:
        """The set of lasso indices where this proposition is true/false at
        `eval_position` -- the certificate encoding's analogue of the retired encoding's
        per-world-state truth/falsity sets, with "lasso index" standing in for "world
        state" (there is no separate finite state abstraction here; see the module
        docstring). Returns two empty sets if there is no certificate or no evaluation
        position (D8's no-certificate case)."""
        if eval_position is None:
            return set(), set()

        truth_lassos: Set[int] = set()
        false_lassos: Set[int] = set()
        for lasso_index, (true_positions, false_positions) in self.extension.items():
            if eval_position in true_positions:
                truth_lassos.add(lasso_index)
            if eval_position in false_positions:
                false_lassos.add(lasso_index)
        return truth_lassos, false_lassos

    def print_proposition(self, eval_point: Dict[str, Any], indent_num: int, use_colors: bool) -> None:
        """Print this proposition and its truth value at `eval_point`.

        `eval_point` carries `{"lasso": int, "position": int}` (D5's eval-point shape).
        """
        lasso = eval_point["lasso"]
        position = eval_point["position"]

        truth_value = self.truth_value_at(lasso, position)

        RESET, FULL, PART = self.set_colors(
            self.name,
            indent_num,
            truth_value,
            f"lasso {lasso}",
            use_colors,
        )

        print(
            f"{'  ' * indent_num}{FULL}|{self.name}| = {self}{RESET}"
            f"  {PART}({truth_value} in lasso {lasso} at position {position}){RESET}"
        )
