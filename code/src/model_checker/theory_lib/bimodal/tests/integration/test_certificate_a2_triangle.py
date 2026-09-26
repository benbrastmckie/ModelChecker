"""The A2-triangle encoding-completeness test (`docs/ADEQUACY.md` section 7.3).

A2 holds iff the Z3 constraint set is exactly the conjunction of (C1)-(C4) over windows at
least as wide as section 5.2's, with no extra constraint. Section 7.3 names the deciding test:
fix a closure `C` with `|C| <= 4`, exhaustively enumerate every candidate `(bx, L_0, ..., L_k)`
over subsets of `C` at the grid's lengths, and compare three verdicts per closure:

- (i) the pure-Python re-checker, `certificate.recheck`;
- (ii) `lake exe check_certificate`;
- (iii) whether the real Z3 encoding, run at the same lengths on the same premises/conclusions,
  reports SAT.

The grid now covers two sizes: `back = mid = fwd = 1` (the historical minimum) and
`back = 2, mid = 1, fwd = 2` (production's `DEFAULT_EXAMPLE_SETTINGS`). The wider grid matters
because it is the one A2 violation known to have actually occurred: `witness_constraints.py`'s
module docstring records that local coherence was once generated over the narrow
`WitnessRegistry.target_window()` instead of the proved wide `_coherence_window`, and the
counterexample that caught it required `nb = 2`, since slot `back[1]` recurs at every
odd-magnitude position -- a defect the `back = mid = fwd = 1` grid alone cannot see.

**What is novel here.** `test_certificate_lean_agreement.py` already compares (i) against (ii)
on the fixture corpus -- that module's own docstring names this as discharging section 7.3's
re-checker leg. Leg (iii), the encoding-*completeness* direction, is what this module adds: it
is the only place in the suite that builds the real `BimodalStructure`/Z3 search and compares its
aggregate verdict against the exhaustive enumeration's. A disagreement localizes a specific
defect (section 7.3): accepted candidates with Z3 UNSAT is an **encoding incompleteness** (a
real countermodel the encoder's constraints cannot find); no accepted candidates with Z3 SAT is
an **encoding unsoundness** (the encoder accepts something the re-checker would reject) -- caught
at run time by section 6.2's fail-fast guard, but this test finds it here instead.

Two tiers:

- **Tier 1** (`TestExhaustiveTriangleBoxFree`, `TestExhaustiveTriangleWithBox`): exhaustive over
  every candidate at both grid sizes, comparing legs (i) and (iii) only -- affordable
  unconditionally at `back = mid = fwd = 1` for every closure and at `back = 2, mid = 1, fwd = 2`
  for the box-free closures (measured at plan time: <0.1s for a box-free closure at the smaller
  grid, ~1.06s combined for both box-free closures at the wider grid); the single-box closures
  are `slow`-marked at both grid sizes (~11s at `back = mid = fwd = 1`, ~64.5s at
  `back = 2, mid = 1, fwd = 2` -- see `TestExhaustiveTriangleWithBox`'s own comment). The
  pre-existing size-3 boxed closure stays `back = mid = fwd = 1`-only: its `nb=nf=2` enumeration
  is ~10.7 billion candidates (~19h extrapolated), well past what `slow` can afford under CI's
  300s per-test ceiling.
- **Tier 2** (`TestBoundedLeanCrossCheck`): leg (ii) on a small, deterministic, named sample of
  candidates plus the live Z3-extracted certificate, reusing `_lean_check.py`'s skip discipline
  so it degrades to a clean skip (never a failure) without a BimodalLogic checkout. Unchanged by
  the wider grid -- still exercised only at `back = mid = fwd = 1`.
"""

from __future__ import annotations

import itertools
from typing import Any, Dict, Iterator, List, Tuple

import pytest

from model_checker.models.constraints import ModelConstraints
from model_checker.syntactic import Syntax
from model_checker.theory_lib.bimodal.operators import bimodal_operators
from model_checker.theory_lib.bimodal.semantic.certificate import (
    LabelledLasso,
    WitnessFamily,
    recheck,
)
from model_checker.theory_lib.bimodal.semantic.core import BimodalSemantics
from model_checker.theory_lib.bimodal.semantic.formula import Box, Formula
from model_checker.theory_lib.bimodal.semantic.model import BimodalStructure
from model_checker.theory_lib.bimodal.semantic.proposition import BimodalProposition
from model_checker.theory_lib.bimodal.tests._lean_check import SKIP_REASON, run_check_certificate

Candidate = Tuple[WitnessFamily, int]
SampledCandidate = Tuple[WitnessFamily, int, Dict[str, Any]]


def _settings(**overrides: Any) -> Dict[str, Any]:
    settings = dict(BimodalSemantics.DEFAULT_EXAMPLE_SETTINGS)
    settings.update(overrides)
    return settings


def _build(premises: List[str], conclusions: List[str], **setting_overrides: Any) -> BimodalStructure:
    """Build one example through the real `Syntax -> ModelConstraints -> BimodalStructure`
    pipeline -- the same construction order `builder/example.py`'s `BuildExample` drives,
    without needing its `BuildModule` scaffolding. Matches `tests/unit/test_structure.py`'s own
    `_build` helper."""
    settings = _settings(**setting_overrides)
    syntax = Syntax(premises, conclusions, bimodal_operators)
    model_constraints = ModelConstraints(
        settings, syntax, BimodalSemantics(settings), BimodalProposition
    )
    return BimodalStructure(model_constraints, settings)


def _subsets(items: List[Formula]) -> Iterator[frozenset]:
    """Every subset of `items`, as a `frozenset` -- a candidate label."""
    items = list(items)
    for r in range(len(items) + 1):
        for combo in itertools.combinations(items, r):
            yield frozenset(combo)


def _candidates(structure: BimodalStructure) -> Iterator[Candidate]:
    """Every `(WitnessFamily, target_time)` candidate over subsets of `structure`'s closure, at
    the lengths `structure` was built with.

    Reads the candidate space's shape from the live search object rather than re-deriving it,
    so this generator cannot silently drift from what the encoder actually built:

    - the closure and the active lasso indices from `structure.semantics.witness_registry` /
      `structure.semantics._active_lassos` (post `finalize_certificate`, already run by the time
      `_build` returns -- see `test_structure.py`'s
      `test_setup_solver_finalizes_the_certificate_before_solving`);
    - the box guess keys (`bx`) from the closure's `Box` children, matching both
      `extract_certificate` and `certificate._box_faithful`'s `family.bx_of(f.child)`;
    - the target-time range from `witness_registry.target_window()`;
    - each lasso's segment lengths (`nb`/`nm`/`nf`) from `witness_registry`, rather than
      assuming length-1 segments -- at `nb = nm = nf = 1` this reduces to exactly the previous
      length-1 construction.

    Asserts `len(closure) <= 4` on every call -- ADEQUACY section 7.3's literal bound, made
    machine-checked rather than trusted to stay true as examples are added or changed.
    """
    semantics = structure.semantics
    closure = sorted(semantics.witness_registry.closure, key=repr)
    assert len(closure) <= 4, (
        f"closure size {len(closure)} exceeds ADEQUACY section 7.3's |C| <= 4 bound for the "
        "A2-triangle test -- re-scope this example rather than enumerating past the bound"
    )
    lasso_indices = semantics._active_lassos
    boxes = sorted((f for f in closure if isinstance(f, Box)), key=repr)
    target_window = list(semantics.witness_registry.target_window())
    labels = list(_subsets(closure))
    nb = semantics.witness_registry.nb
    nm = semantics.witness_registry.nm
    nf = semantics.witness_registry.nf

    # Materialize once: passing the same list object to `itertools.product` multiple times is
    # safe (each positional argument is independently converted to a tuple internally), unlike
    # passing the same *generator* object multiple times, which would be exhausted after the
    # first use.
    back_choices = list(itertools.product(labels, repeat=nb))
    mid_choices = list(itertools.product(labels, repeat=nm))
    fwd_choices = list(itertools.product(labels, repeat=nf))
    per_lasso_label_choices = list(itertools.product(back_choices, mid_choices, fwd_choices))

    for bx_bits in itertools.product((False, True), repeat=len(boxes)):
        bx = {boxes[i].child: bx_bits[i] for i in range(len(boxes))}
        for lasso_labels in itertools.product(*([per_lasso_label_choices] * len(lasso_indices))):
            lassos = tuple(
                LabelledLasso(back=back_labels, mid=mid_labels, fwd=fwd_labels)
                for (back_labels, mid_labels, fwd_labels) in lasso_labels
            )
            family = WitnessFamily(bx=bx, lassos=lassos)
            for t in target_window:
                yield family, t


def _run_exhaustive_triangle(structure: BimodalStructure) -> Tuple[int, int]:
    """Enumerate every candidate for `structure`'s closure, re-check each against leg (i), and
    return `(total_candidates, accepted_candidates)`."""
    total = 0
    accepted = 0
    for family, target_time in _candidates(structure):
        total += 1
        verdict = recheck(
            family,
            structure.semantics._premise_formulas,
            structure.semantics._conclusion_formulas,
            target_time,
        )
        if verdict["status"] == "countermodel":
            accepted += 1
    return total, accepted


def _expected_candidate_count(structure: BimodalStructure, closure_size: int) -> int:
    """The closed-form candidate count: `(2**|C|)**(slots_per_lasso*lassos) * 2**boxes *
    len(target_window)` (ADEQUACY section 7.3's Testing & Validation cross-check).

    `slots_per_lasso` (`nb+nm+nf`) is the number of independent label-choice slots each lasso
    contributes -- one factor of `2**|C|` per slot, since `_candidates()` draws each of a
    lasso's `back`/`mid`/`fwd` positions independently from the same `2**|C|` labels. The
    identity `target_window_len == slots_per_lasso` holds because both equal `nb+nm+nf`
    (`target_window()` is `range(-nb, nm+nf)`, width `nb+nm+nf`) -- the previous literal `3`
    exponent relied on this silently, being correct only at `nb=nm=nf=1`, where
    `slots_per_lasso == 3`.
    """
    semantics = structure.semantics
    lassos = len(semantics._active_lassos)
    boxes = sum(1 for f in semantics.witness_registry.closure if isinstance(f, Box))
    target_window_len = len(list(semantics.witness_registry.target_window()))
    slots_per_lasso = semantics.witness_registry.slots_per_lasso
    return (2 ** closure_size) ** (slots_per_lasso * lassos) * (2 ** boxes) * target_window_len


def _assert_exhaustive_triangle_agrees(
    premises: List[str],
    conclusions: List[str],
    expected_closure_size: int,
    expected_total: int,
    expected_accepted: int,
    expected_sat: bool,
    back: int = 1,
    mid: int = 1,
    fwd: int = 1,
) -> None:
    """Shared Tier 1 body: build `structure` at the given `back`/`mid`/`fwd` grid, enumerate
    every candidate, and assert the enumeration's aggregate (leg i) agrees with the real Z3
    verdict (leg iii) -- used by both `TestExhaustiveTriangleBoxFree` (box-free closures) and
    `TestExhaustiveTriangleWithBox` (the single-box closure, which additionally carries the
    `slow` marker at its call site). `back = mid = fwd = 1` is the historical default; callers
    covering the wider `nb=nf=2` grid pass it explicitly."""
    structure = _build(premises, conclusions, back=back, mid=mid, fwd=fwd)
    closure = structure.semantics.witness_registry.closure
    assert len(closure) == expected_closure_size, (
        f"closure size changed: expected {expected_closure_size}, got {len(closure)} for "
        f"premises={premises!r} conclusions={conclusions!r} -- re-derive the expected "
        "candidate/accepted counts below from the test's own run output rather than "
        "editing them blind (Scope Hypothesis, plan Phases 2-3)"
    )

    total, accepted = _run_exhaustive_triangle(structure)

    expected_formula_total = _expected_candidate_count(structure, expected_closure_size)
    assert total == expected_formula_total == expected_total, (
        "candidate count mismatch", total, expected_formula_total, expected_total
    )
    assert accepted == expected_accepted, (
        f"accepted candidate count changed: expected {expected_accepted}, got {accepted} for "
        f"premises={premises!r} conclusions={conclusions!r}"
    )

    assert (accepted > 0) == structure.z3_model_status == expected_sat, (
        f"A2-triangle disagreement for premises={premises!r} conclusions={conclusions!r}: "
        f"{accepted}/{total} candidates accepted by the re-checker, Z3 reports "
        f"z3_model_status={structure.z3_model_status!r} -- ADEQUACY.md section 7.3: if "
        "accepted > 0 and Z3 is UNSAT this is an ENCODING INCOMPLETENESS (a real "
        "countermodel the encoder's constraints cannot find); if accepted == 0 and Z3 is "
        "SAT this is an ENCODING UNSOUNDNESS (the encoder accepts something the re-checker "
        "would reject). Report this as a finding -- do not weaken this assertion or drop "
        "the closure."
    )

    if expected_sat:
        # The extracted certificate is itself one of the accepted candidates -- re-check it
        # directly rather than searching for it inside the enumeration.
        assert structure.certificate is not None
        assert structure.target_time is not None
        extracted_verdict = recheck(
            structure.certificate,
            structure.semantics._premise_formulas,
            structure.semantics._conclusion_formulas,
            structure.target_time,
        )
        assert extracted_verdict["status"] == "countermodel", extracted_verdict


class TestExhaustiveTriangleBoxFree:
    """Legs (i) vs. (iii), exhaustive, over two box-free closures, each at two grid sizes:
    `back = mid = fwd = 1` (the historical minimum) and `back = 2, mid = 1, fwd = 2`
    (production's `DEFAULT_EXAMPLE_SETTINGS`) -- one expected SAT, one expected UNSAT at each
    grid, so a defect that only shows up in one direction (encoding incompleteness vs.
    unsoundness) cannot hide behind the other case, and a defect that only shows up at `nb = 2`
    (see this module's docstring) cannot hide behind the narrower grid either.

    Measured wall clock for the two new `nb=nf=2` cases on this host: ~1.06s combined
    (`box_free_until_conclusion_sat_nb2_nf2` ~1.06s SAT at 163,840 candidates / 926 accepted;
    `box_free_contradiction_unsat_nb2_nf2` ~0s UNSAT at 160 candidates / 0 accepted) -- both
    left unconditional (no `slow` marker), well inside a non-`slow` local run's budget."""

    @pytest.mark.parametrize(
        "premises, conclusions, expected_closure_size, expected_total, expected_accepted, "
        "expected_sat, back, mid, fwd",
        [
            pytest.param(
                [], ["(q \\Until p)"], 3, 1536, 52, True, 1, 1, 1,
                id="box_free_until_conclusion_sat",
            ),
            pytest.param(
                ["A"], ["A"], 1, 24, 0, False, 1, 1, 1,
                id="box_free_contradiction_unsat",
            ),
            pytest.param(
                [], ["(q \\Until p)"], 3, 163_840, 926, True, 2, 1, 2,
                id="box_free_until_conclusion_sat_nb2_nf2",
            ),
            pytest.param(
                ["A"], ["A"], 1, 160, 0, False, 2, 1, 2,
                id="box_free_contradiction_unsat_nb2_nf2",
            ),
        ],
    )
    def test_enumeration_agrees_with_z3(
        self,
        premises,
        conclusions,
        expected_closure_size,
        expected_total,
        expected_accepted,
        expected_sat,
        back,
        mid,
        fwd,
    ):
        _assert_exhaustive_triangle_agrees(
            premises, conclusions, expected_closure_size, expected_total, expected_accepted,
            expected_sat, back=back, mid=mid, fwd=fwd,
        )


class TestExhaustiveTriangleWithBox:
    """Leg (i) vs. (iii) over a closure containing a `Box`, exercising the witness-lasso and
    `bx` dimensions of the candidate space that the box-free closures above cannot reach: two
    active lassos (main plus one witness lasso for the boxed subformula) and one `bx` guess.

    Measured at plan/implementation time on this host: 1,572,864 candidate re-checks
    (`512**2 * 2 * 3` -- 512 labels-per-lasso-slot choices squared for two lassos, 2 box-guess
    assignments, 3 target-window positions), 96 accepted, Z3 verdict SAT, ~11s wall clock. Marked
    `slow` (already registered in `code/pyproject.toml`) so a `-m "not slow"` local run
    deselects it while keeping the box-free cases above.

    A second case, `test_boxed_closure_enumeration_agrees_with_z3_nb2_nf2`, covers the same
    box/witness-lasso dimensions at `back = 2, mid = 1, fwd = 2` (production's
    `DEFAULT_EXAMPLE_SETTINGS`) for a closure of size 2 (`[] |- [\\Box A]`): 10,485,760 candidate
    re-checks, 5,115 accepted, Z3 verdict SAT, ~64.5s wall clock on this host (selected by an
    implementation-time measurement gate over two closure-size-2 candidates, both `slow`-marked;
    see the task's implementation summary for the full gate record). Also `slow`-marked for the
    same reason. The pre-existing size-3 closure above stays at `back = mid = fwd = 1` only: its
    `nb=nf=2` enumeration is ~10.7 billion candidates (~19h extrapolated), well past what `slow`
    can afford under CI's 300s per-test ceiling -- `slow` controls local `-m "not slow"`
    deselection only, it grants no per-test timeout exemption."""

    @pytest.mark.slow
    def test_boxed_closure_enumeration_agrees_with_z3(self):
        _assert_exhaustive_triangle_agrees(
            ["\\Box A"], ["B"],
            expected_closure_size=3,
            expected_total=1_572_864,
            expected_accepted=96,
            expected_sat=True,
            back=1, mid=1, fwd=1,
        )

    @pytest.mark.slow
    def test_boxed_closure_enumeration_agrees_with_z3_nb2_nf2(self):
        _assert_exhaustive_triangle_agrees(
            [], ["\\Box A"],
            expected_closure_size=2,
            expected_total=10_485_760,
            expected_accepted=5_115,
            expected_sat=True,
            back=2, mid=1, fwd=2,
        )


# ---------------------------------------------------------------------------
# Tier 2: bounded Lean cross-check (leg ii)
# ---------------------------------------------------------------------------
#
# `~2.2s` per `lake exe check_certificate` invocation (measured at plan time), against which
# `test_certificate_lean_agreement.py`'s existing ~10-test module takes ~15-22s total. Exhaustive
# Lean cross-checking of every accepted candidate across the two SAT closures (148 candidates)
# would cost ~5.5 minutes, so this samples instead: a small, fixed, named per-class count,
# reproducible across runs (fixed enumeration order, fixed stride -- no unseeded randomness).
# Measured at implementation time on this host: the three parametrized cases below (two
# box-free plus the single-box closure) take ~6s / ~15s / ~36s respectively, ~58s total for
# this class alone -- most of the single-box case's cost is the two Python-side enumeration
# passes `_sampled_candidates` needs over its 1,572,864 candidates, not the ~11 Lean
# invocations themselves. Within the plan's own ~50-60s estimate; not lowered further.
LEAN_SAMPLE_PER_CLASS = 5

# This module's own per-invocation timeout, matching `test_certificate_lean_agreement.py`'s
# `PER_FIXTURE_TIMEOUT_SECONDS`.
LEAN_INVOCATION_TIMEOUT_SECONDS = 30


def _sampled_candidates(
    structure: BimodalStructure, per_class: int
) -> Tuple[List[SampledCandidate], List[SampledCandidate]]:
    """Deterministically select up to `per_class` accepted candidates (the first `per_class`,
    in enumeration order) and up to `per_class` rejected candidates (a fixed stride over the
    rejected ones) from `structure`'s exhaustive enumeration.

    Two passes over `_candidates`: the first counts how many candidates are rejected (needed to
    fix the stride before any candidate is chosen, so the choice does not depend on how many
    accepted candidates happened to come first); the second makes the actual selection. Each
    pass is exactly as cheap as one `TestExhaustiveTriangleWithBox` run (`recheck` alone, no
    Z3), so this doubles that closure's own enumeration cost, not the Lean cost -- the Lean
    subprocess invocations dominate this Tier's budget regardless.

    Returns `(accepted_samples, rejected_samples)`, each a list of `(family, target_time,
    verdict)`.
    """

    def _verdict_for(family: WitnessFamily, target_time: int) -> Dict[str, Any]:
        return recheck(
            family,
            structure.semantics._premise_formulas,
            structure.semantics._conclusion_formulas,
            target_time,
        )

    total_rejected = 0
    for family, target_time in _candidates(structure):
        if _verdict_for(family, target_time)["status"] != "countermodel":
            total_rejected += 1
    stride = max(total_rejected // per_class, 1) if total_rejected else 0

    accepted: List[SampledCandidate] = []
    rejected: List[SampledCandidate] = []
    rejected_seen = 0
    for family, target_time in _candidates(structure):
        verdict = _verdict_for(family, target_time)
        if verdict["status"] == "countermodel":
            if len(accepted) < per_class:
                accepted.append((family, target_time, verdict))
        else:
            if stride and rejected_seen % stride == 0 and len(rejected) < per_class:
                rejected.append((family, target_time, verdict))
            rejected_seen += 1
        # Both quotas are filled in a fixed, deterministic prefix of the enumeration (accepted:
        # the first `per_class` in order; rejected: a fixed stride computed from the exact
        # `total_rejected` counted above) -- stopping here changes nothing about which
        # candidates are chosen, only how much of the remainder is scanned needlessly.
        if len(accepted) >= per_class and len(rejected) >= per_class:
            break
    return accepted, rejected


def _assert_lean_agrees(payload: Dict[str, Any], python_verdict: Dict[str, Any], label: str) -> None:
    """Assert `lake exe check_certificate` agrees with `python_verdict` on `payload`, matching
    `test_certificate_lean_agreement.py`'s `TestPythonRecheckerAgreesWithLean` convention: on a
    `rejected` disagreement, the two sides' failed `condition` sets must intersect. The Lean
    predicates are the contract (ADEQUACY.md section 5.3), so a status disagreement is
    attributed Python-side by default."""
    lean_verdict = run_check_certificate(payload, LEAN_INVOCATION_TIMEOUT_SECONDS)
    assert lean_verdict is not None, (
        f"{label}: lake exe check_certificate did not respond within "
        f"{LEAN_INVOCATION_TIMEOUT_SECONDS}s"
    )
    assert lean_verdict["status"] == python_verdict["status"], (
        f"{label}: recheck says {python_verdict['status']!r}, lake exe check_certificate says "
        f"{lean_verdict['status']!r} -- the Lean predicates are the contract (ADEQUACY.md "
        "section 5.3), so this is a Python-side defect, not a Lean-side one"
    )
    if lean_verdict["status"] == "rejected":
        python_conditions = {entry.get("condition") for entry in python_verdict.get("failed", [])}
        lean_conditions = {entry.get("condition") for entry in lean_verdict.get("failed", [])}
        assert python_conditions & lean_conditions, (
            f"{label}: recheck's failed condition(s) {python_conditions!r} share nothing with "
            f"Lean's {lean_conditions!r}"
        )


@pytest.mark.skipif(SKIP_REASON is not None, reason=SKIP_REASON or "")
class TestBoundedLeanCrossCheck:
    """Leg (ii) on a bounded, deterministic sample of candidates, plus the live Z3-extracted
    certificate for each SAT closure -- closing the gap the production fail-fast guard leaves
    (it calls the Python `recheck` only, never Lean). Skips cleanly, with a named reason, never
    a failure, without a BimodalLogic checkout or `lake` -- the same discipline
    `test_certificate_lean_agreement.py` uses, via the shared `_lean_check` helper. This
    `skipif` is applied at the class level, not the module level, so Tier 1's exhaustive
    completeness comparison above keeps running (and still passing) even when this class skips."""

    @pytest.mark.parametrize(
        "premises, conclusions, is_sat",
        [
            pytest.param([], ["(q \\Until p)"], True, id="box_free_until_conclusion_sat"),
            pytest.param(["A"], ["A"], False, id="box_free_contradiction_unsat"),
            pytest.param(
                ["\\Box A"], ["B"], True,
                id="boxed_closure_sat", marks=pytest.mark.slow,
            ),
        ],
    )
    def test_sampled_candidates_and_extracted_certificate_agree_with_lean(
        self, premises, conclusions, is_sat
    ):
        structure = _build(premises, conclusions, back=1, mid=1, fwd=1)
        accepted_samples, rejected_samples = _sampled_candidates(structure, LEAN_SAMPLE_PER_CLASS)

        for index, (family, target_time, verdict) in enumerate(accepted_samples):
            payload = family.to_json(
                structure.semantics._premise_formulas,
                structure.semantics._conclusion_formulas,
                target_time,
            )
            _assert_lean_agrees(
                payload, verdict,
                f"premises={premises!r} conclusions={conclusions!r} accepted[{index}]",
            )

        for index, (family, target_time, verdict) in enumerate(rejected_samples):
            payload = family.to_json(
                structure.semantics._premise_formulas,
                structure.semantics._conclusion_formulas,
                target_time,
            )
            _assert_lean_agrees(
                payload, verdict,
                f"premises={premises!r} conclusions={conclusions!r} rejected[{index}]",
            )

        if is_sat:
            # The production fail-fast guard (`semantic/model.py`) re-checks the extracted
            # certificate against the Python `recheck` only; this closes that gap by also
            # checking it against the live Lean binary.
            assert structure.certificate is not None
            assert structure.target_time is not None
            wire = structure.semantics.export_certificate_json(
                structure.certificate, structure.target_time
            )
            python_verdict = recheck(
                structure.certificate,
                structure.semantics._premise_formulas,
                structure.semantics._conclusion_formulas,
                structure.target_time,
            )
            assert python_verdict["status"] == "countermodel", python_verdict
            _assert_lean_agrees(
                wire, python_verdict,
                f"premises={premises!r} conclusions={conclusions!r} extracted certificate",
            )
