"""AST-based regression guard for example solve budgets (see
`code/docs/core/TESTING_GUIDE.md` section 8.6, "Set budgets generously, not tightly").

**The gap this closes.** `test_timing_marker_coverage.py` guards the *explicit* wall-clock
class: a test that reads `time.time()` and asserts a bound on the delta. It has no notion of
the far larger *implicit* class -- an example whose `max_time` setting is itself the clock. A
`max_time` that sits near an example's typical solve time turns ordinary CPU contention into a
test failure: Z3 returns UNKNOWN, `ModelDefaults.check_result()` reports `"inconclusive"`, and
`utils.testing.run_test()` maps that to `False`, which the theory-level example tests assert on.
The failure text ("Model result did not match expectation value in settings") reads as a
semantic regression while being nothing of the sort.

That is not hypothetical. `CL_TH_12` and `CL_TH_13` in
`theory_lib/logos/subtheories/constitutive/examples.py` were both set to `'max_time': 1`
against measured solve times of 0.267s and 0.350s on a 12-core AMD Ryzen AI 9 HX 370 -- ~3x
headroom locally, but under 1x on a 4-vCPU `ubuntu-latest` runner running six xdist workers.
They failed on all three Python versions and under `nix flake check` on the v1.3.5 release
pushes. Earlier runs failed the same way on different victims
(`test_iterate_example_generator_yields_models`, `test_iteration_via_iterate_api`).

**Why a floor rather than a per-example calibration.** Section 8.6's own guidance is that a
budget must NOT be derived from a measured solve plus a small margin -- an observed ~1.7s solve
given a 10s budget still failed at 10.11s under full-suite load. A blanket floor is the shape
that guidance implies. The floor costs nothing at runtime: a solve that finishes in 0.3s never
consumes its budget, so raising it only changes what happens on a machine slow enough to have
produced a false negative anyway.

**Why 10 and not 30.** 10 is already the in-tree convention for 81 of the 129 budgeted examples
across `theory_lib/`, including 25 in `logos/subtheories/counterfactual/examples.py` -- a
sibling of the three files this guard's floor was introduced to correct. It gives ~29x headroom
over the worst solve measured in the covered files. Section 8.6 cites a 30s convention for the
bimodal examples; that remains available and is not capped here (this is a floor, not an
equality), but 30 as a blanket minimum would make a genuinely-hung example cost 30s per failure
across ~100 examples, and the evidence does not support needing it.

**Scope is seven files**: the four `logos/subtheories/*/examples.py` files whose budgets were
originally recalibrated with this guard, plus `bimodal/examples.py`, `exclusion/examples.py`,
and `imposition/examples.py`, added in a second widening once those three files' below-floor
budgets were directly measured rather than pattern-matched from the logos incident. **What was
measured and what it found.** An AST re-scan of the three files (identical method to `_budgets()`
above) found 57 below-floor `max_time` dicts -- bimodal 21, exclusion 26, imposition 10 -- not
the 22 (20 at `max_time: 2`, 2 at `3`) an earlier research pass had enumerated; the remaining 35
sit at `max_time: 5` and had never been measured before this widening. The 22-item `2`/`3` cohort
was measured isolated at 0.01s-0.37s and under `taskset -c 0,1,2,3`/`-n 6` contention at
0.06s-0.80s (5x-300x headroom over the 10s floor). The 35-item `max_time: 5` cohort was then
separately measured, isolated, single-process (mirroring the same method): 0.012s-1.549s, a
6.5x-800x headroom over the 10s floor -- comfortably clear of the ~3x-headroom regime that
produced the `CL_TH_12`/`CL_TH_13` logos failures this guard exists to catch. All 57 flagged
budgets were raised to exactly `_MIN_MAX_TIME` (10); no budget was raised above 10 and no
above-floor value (including bimodal's `BM_CM_1` at 60 and `BM_CM_4` at 120) was touched --
raising a floor never lowers an existing higher value. **This does not conflict with bimodal's
per-example recalibration record.** `BM_CM_1`/`BM_CM_4` were deliberately calibrated above 10
for a documented heavy-tailed Z3 solve distribution (see that record in
`theory_lib/bimodal/examples.py`); this floor only raises values that sat *below* 10, so the two
mechanisms operate on disjoint value ranges and neither overrides the other. **One measured
example is not exercised by CI's collected suite regardless of its raised budget:** `MD_TH_2` in
`bimodal/examples.py` is separately excluded from `test_bimodal.py`'s collection via
`KNOWN_TIMEOUT_EXAMPLES`, for reasons unrelated to its `max_time` (a known non-theorem under
current bimodal semantics) -- the same is true of `TN_CM_1` and `MF_MODAL_FUTURE_TH` (also in
`KNOWN_TIMEOUT_EXAMPLES`) and of `BM_TH_5` (present in `example_range` but never added to
`unit_tests`, so it is not collected at all); all four were still measured and raised here
because this guard reads the source file directly, independent of what pytest collects.
"""

from __future__ import annotations

import ast
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
_SUBTHEORIES = REPO_ROOT / "code" / "src" / "model_checker" / "theory_lib" / "logos" / "subtheories"

# Minimum solve budget, in seconds, for any example settings dict in a covered file.
_MIN_MAX_TIME = 10

_THEORY_LIB = REPO_ROOT / "code" / "src" / "model_checker" / "theory_lib"

_COVERED = [
    _SUBTHEORIES / "constitutive" / "examples.py",
    _SUBTHEORIES / "counterfactual" / "examples.py",
    _SUBTHEORIES / "extensional" / "examples.py",
    _SUBTHEORIES / "modal" / "examples.py",
    _THEORY_LIB / "bimodal" / "examples.py",
    _THEORY_LIB / "exclusion" / "examples.py",
    _THEORY_LIB / "imposition" / "examples.py",
]

# `flake.nix`'s checks.default derivation sets `src = ./code`, so REPO_ROOT resolves to /build
# there and the theory_lib tree IS present (it lives under code/). No skip guard is needed --
# unlike test_workflow_parity.py, this module reads nothing outside code/.


def _budgets(path: Path):
    """Yield (lineno, value) for every `'max_time': <literal>` entry in a dict literal.

    A non-literal value (a name, an expression) yields `None` as its value and is reported as a
    violation rather than silently skipped: the point of the floor is that the budget is
    readable from the source, and an indirected budget defeats that.
    """
    tree = ast.parse(path.read_text(), filename=str(path))
    for node in ast.walk(tree):
        if not isinstance(node, ast.Dict):
            continue
        for key, value in zip(node.keys, node.values):
            if isinstance(key, ast.Constant) and key.value == "max_time":
                literal = value.value if isinstance(value, ast.Constant) else None
                yield key.lineno, literal


@pytest.mark.parametrize("path", _COVERED, ids=lambda p: p.parent.name)
def test_example_max_time_meets_floor(path):
    """Every example settings dict in a covered file budgets at least `_MIN_MAX_TIME` seconds."""
    assert path.exists(), f"covered file is missing: {path}"

    violations = [
        f"{path.relative_to(REPO_ROOT)}:{lineno}: max_time={value!r}"
        for lineno, value in _budgets(path)
        if not isinstance(value, int) or value < _MIN_MAX_TIME
    ]

    assert not violations, (
        f"{len(violations)} example settings dict(s) budget below the {_MIN_MAX_TIME}s floor. "
        f"A budget near an example's typical solve time turns CPU contention on a 4-vCPU CI "
        f"runner into a spurious 'Model result did not match expectation value in settings' "
        f"failure -- see this module's docstring and TESTING_GUIDE.md section 8.6. Raise the "
        f"budget; do not lower this floor.\n  " + "\n  ".join(violations)
    )


def test_floor_guard_detects_a_below_floor_budget(tmp_path):
    """The guard's own detection is live -- a synthetic below-floor budget is flagged.

    Without this, a refactor that broke `_budgets()` (e.g. by walking only module-level
    assignments) would leave `test_example_max_time_meets_floor` passing vacuously.
    """
    sample = tmp_path / "examples.py"
    sample.write_text(
        "OK_settings = {'N': 4, 'max_time': 10}\n"
        "TIGHT_settings = {'N': 4, 'max_time': 1}\n"
        "INDIRECT_settings = {'N': 4, 'max_time': SOME_NAME}\n"
    )

    found = {lineno: value for lineno, value in _budgets(sample)}
    assert found == {1: 10, 2: 1, 3: None}

    below = [v for v in found.values() if not isinstance(v, int) or v < _MIN_MAX_TIME]
    assert below == [1, None]
