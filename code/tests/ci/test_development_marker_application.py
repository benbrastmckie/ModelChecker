"""Executable contract for the theory-level application of the `development` marker to the
bimodal test tree (see `code/docs/core/TESTING_GUIDE.md` section 8.14).

The `development` marker's registration, gating-driver deselection, classifier support, and
documentation all landed without any test claiming the marker. This contract covers the
application half: bimodal -- the one theory currently declared in active construction -- claims
`development` on every test it collects, and no other tree claims it at all.

Two properties are asserted, and the second matters as much as the first:

1. **Complete coverage of bimodal.** Every item collected under
   `src/model_checker/theory_lib/bimodal/tests/` carries `development`, so a bimodal failure
   cannot turn a release-gating run red (all ten gating invocations already carry
   `and not development`; see `test_unstable_deselection_wiring.py`).
2. **Containment to bimodal.** No item outside that tree acquires the marker. A theory-level
   blanket is the marker application most capable of over-reaching, so the blast radius is
   pinned down here rather than left to the reviewer to notice.

Assertions run pytest in a subprocess with `--collect-only` rather than introspecting
`item.own_markers` from inside the current session: the marker is applied by a
`pytest_collection_modifyitems` hook in bimodal's own `tests/conftest.py`, and only a real
collection exercises that hook the way a gating driver's `-m` expression does. Collection-only
runs cost well under a second per invocation (no solver work is performed), so the four
subprocesses here are cheap despite covering the whole `src/model_checker` tree.
"""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

import pytest

CODE_DIR = Path(__file__).resolve().parents[2]
SRC_DIR = CODE_DIR / "src"
BIMODAL_TESTS = "src/model_checker/theory_lib/bimodal/tests"

# Every theory_lib tree except bimodal, plus the package-level suite. Used for the containment
# assertion; listed explicitly rather than derived by "everything minus bimodal" so that a new
# theory added to the repository does not silently fall outside this guard's scope without a
# deliberate edit here.
NON_BIMODAL_ROOTS = [
    "src/model_checker/theory_lib/logos",
    "src/model_checker/theory_lib/exclusion",
    "src/model_checker/theory_lib/imposition",
    "tests",
]

# Explicit, enumerated allowlist of node ids outside the bimodal tree that are authorized to
# carry `development`, per TESTING_GUIDE.md section 8.14's per-test granularity (not a new
# blanket). Each entry's subject is genuinely bimodal, but its claim is one of *completeness*
# ("bimodal's example set runs to completion", "bimodal finds a countermodel within budget")
# rather than *soundness* -- exactly the boundary 8.14 draws. Node ids (including parametrize
# suffixes) were taken verbatim from a real `-m development` collection run, per this contract's
# own Pre-Edit Verification Gate obligation, not hand-written.
#
# Three entries, not the two this task's plan initially hypothesized: a fourth file
# (`test_generate_then_execute_cp1252`) was added by concurrent work in the same repository
# between the plan being written and this phase landing, reusing the identical
# parametrize-over-registry pattern and therefore requiring the identical marking -- recorded
# here as the actual, confirmed scope rather than silently forced to match the original count.
_AUTHORIZED_NON_BIMODAL_DEVELOPMENT = [
    # Completeness claim: bimodal's full default generated examples.py runs to completion
    # through the real installed console script. Measured 81.06s, the single most expensive
    # bimodal-coupled gating test found in the audit.
    "tests/packaging/test_generate_then_execute.py::test_generate_then_execute[bimodal]",
    # Same claim, same theory, under the cp1252-constrained stdout-encoding leg added for
    # Windows-encoding coverage (see test_generate_then_execute.py's own module docstring).
    "tests/packaging/test_generate_then_execute.py::test_generate_then_execute_cp1252[bimodal]",
    # Completeness claim: BuildExample finds a countermodel for bimodal within its (unchanged)
    # 30s budget. Not a bimodal-specific semantic claim -- the task description's own framing
    # already agrees the assertion is generic BuildExample-integration plumbing -- but the
    # example's cost is genuinely bimodal-coupled while the frame-axiom cost is unsettled.
    "src/model_checker/builder/tests/unit/test_example.py::"
    "TestBuildExampleIntegration::test_build_example_bimodal_theory_countermodel",
]

# Set form, used by the containment assertions below for membership subtraction/comparison.
_AUTHORIZED_SET = set(_AUTHORIZED_NON_BIMODAL_DEVELOPMENT)


def _collect(*args: str) -> list[str]:
    """Return the collected node ids from `pytest --collect-only -q <args>`, run in a
    subprocess rooted at `code/`.

    Node-id lines are identified by the `::` separator, which `-q` collection output uses for
    every collected item and for nothing else (the trailing summary line, the plugin banner,
    and any warning block carry no `::`).

    `-o addopts=--import-mode=importlib` replaces `code/pyproject.toml`'s own `addopts` for the
    subprocess. The override is needed because that value's `-v` and this call's `-q` cancel each
    other out (both adjust the same verbosity counter), leaving `--collect-only` at default
    verbosity -- which prints an indented `<Function ...>` tree carrying no `::` at all, so every
    assertion below would silently see an empty list and pass vacuously. `--import-mode=importlib`
    is carried over deliberately rather than dropped: without it, collecting the full
    `src/model_checker` tree fails with 18 import errors from same-named test modules in sibling
    packages. The other ini keys (`pythonpath`, `markers`, `testpaths`) are unaffected by this
    override and still apply.
    """
    env = os.environ.copy()
    env["PYTHONPATH"] = str(SRC_DIR)
    completed = subprocess.run(
        [
            sys.executable, "-m", "pytest",
            "-o", "addopts=--import-mode=importlib",
            "--collect-only", "-q", *args,
        ],
        cwd=CODE_DIR,
        env=env,
        capture_output=True,
        text=True,
    )
    # Exit code 5 ("no tests collected") is an expected, legitimate outcome for the
    # deselect-everything invocations below, so it is not treated as a failure here. Any other
    # non-zero code means collection itself broke, which would make these assertions vacuous.
    if completed.returncode not in (0, 5):
        pytest.fail(
            f"pytest --collect-only failed (exit {completed.returncode}) for args {args!r}\n"
            f"--- stdout ---\n{completed.stdout}\n--- stderr ---\n{completed.stderr}"
        )
    return [line.strip() for line in completed.stdout.splitlines() if "::" in line]


class TestBimodalClaimsDevelopment:
    """Bimodal's whole test tree carries `development`, so no bimodal failure gates a release."""

    def test_every_bimodal_test_is_development_marked(self):
        """`-m development` over the bimodal tree collects exactly what an unfiltered run
        collects -- i.e. the marker covers every item, with none left unmarked and therefore
        still gating."""
        unfiltered = _collect(BIMODAL_TESTS)
        assert unfiltered, (
            f"expected the bimodal test tree at {BIMODAL_TESTS} to collect at least one test; "
            f"collecting none means this guard is vacuous"
        )

        development_marked = _collect("-m", "development", BIMODAL_TESTS)
        missing = sorted(set(unfiltered) - set(development_marked))
        assert not missing, (
            f"{len(missing)} bimodal test(s) do not carry the `development` marker and would "
            f"therefore still fail a release-gating run: {missing[:10]}"
        )

    def test_gating_expression_deselects_the_entire_bimodal_tree(self):
        """The complement of the assertion above, phrased the way the gating drivers actually
        select: `-m "not development"` over bimodal must collect nothing at all."""
        remaining = _collect("-m", "not development", BIMODAL_TESTS)
        assert remaining == [], (
            f"{len(remaining)} bimodal test(s) survive the gating drivers' `not development` "
            f"filter and can still turn a release-gating run red: {remaining[:10]}"
        )

    def test_bimodal_is_still_runnable_on_explicit_opt_in(self):
        """The marker must quarantine bimodal from gating runs without making it unrunnable --
        `-m development` is the documented opt-in invocation (see bimodal's `tests/README.md`
        and TESTING_GUIDE.md section 8.14)."""
        opted_in = _collect("-m", "development", BIMODAL_TESTS)
        assert len(opted_in) > 0, (
            "`-m development` collected no bimodal tests -- the opt-in path documented in "
            "bimodal's tests/README.md is broken, leaving the theory unobservable"
        )


class TestDevelopmentMarkerIsContainedToBimodal:
    """No tree outside bimodal claims `development`, except an explicit, enumerated allowlist.

    A theory-level blanket must not leak beyond bimodal -- and beyond the small, audited set of
    per-test markings `_AUTHORIZED_NON_BIMODAL_DEVELOPMENT` above records. Every assertion below
    subtracts that allowlist rather than asserting a bare empty set, but the allowlist itself is
    pinned exactly (see test_authorized_allowlist_is_exactly_matched below) so it cannot silently
    grow into a wider exemption.
    """

    @pytest.mark.parametrize("root", NON_BIMODAL_ROOTS)
    def test_no_development_marked_tests_outside_bimodal(self, root):
        leaked = sorted(set(_collect("-m", "development", root)) - _AUTHORIZED_SET)
        assert leaked == [], (
            f"{len(leaked)} test(s) under {root} carry the `development` marker, which is "
            f"reserved for theories under active construction (bimodal only, today) or the "
            f"explicit _AUTHORIZED_NON_BIMODAL_DEVELOPMENT allowlist. These would be silently "
            f"dropped from every release-gating run: {leaked[:10]}"
        )

    def test_no_leakage_when_bimodal_is_collected_alongside_the_rest_of_the_tree(self):
        """The case the per-root assertions above cannot see, and the one that matters.

        A `pytest_collection_modifyitems` implementation is handed the *entire* session's item
        list once its conftest has been loaded -- it is not scoped to that conftest's directory
        by pytest. So a marker-applying hook that loops over `items` without a path check marks
        every test in the repository, but only in a run that collects bimodal *and* something
        else. Each per-root subprocess above collects a single root, never loads bimodal's
        conftest, and therefore passes even against a fully-leaking hook.

        `pytest tests src/model_checker` is precisely the mixed-root shape both gating drivers
        (`.github/workflows/tests.yml` and `flake.nix`) invoke, so a leak here would deselect
        the entire suite from every gating run while every other assertion in this file stayed
        green.
        """
        marked = _collect("-m", "development", "tests", "src/model_checker")
        outside = sorted(
            nodeid
            for nodeid in marked
            if not nodeid.startswith(BIMODAL_TESTS) and nodeid not in _AUTHORIZED_SET
        )
        assert not outside, (
            f"{len(outside)} test(s) outside the bimodal tree and outside the explicit "
            f"_AUTHORIZED_NON_BIMODAL_DEVELOPMENT allowlist acquired the `development` marker "
            f"in a mixed-root collection -- bimodal's conftest hook is marking items it does "
            f"not own, silently removing them from every release-gating run. "
            f"First offenders: {outside[:10]}"
        )
        assert marked, (
            "the mixed-root collection found no development-marked tests at all, so this "
            "assertion proved nothing -- bimodal's conftest hook did not run"
        )

    def test_authorized_allowlist_is_exactly_matched(self):
        """Every `_AUTHORIZED_NON_BIMODAL_DEVELOPMENT` entry is actually collected as
        `development`-marked, and nothing outside bimodal is `development`-marked beyond exactly
        this set -- so a stale allowlist entry (e.g. after a rename or an un-marking) fails
        loudly instead of silently widening the exemption by no longer being checked against
        anything real."""
        marked = _collect("-m", "development", "tests", "src/model_checker")
        outside = {nodeid for nodeid in marked if not nodeid.startswith(BIMODAL_TESTS)}
        assert outside == _AUTHORIZED_SET, (
            f"the non-bimodal `development`-marked set does not exactly match "
            f"_AUTHORIZED_NON_BIMODAL_DEVELOPMENT.\n"
            f"Missing from collection (stale allowlist entry): {sorted(_AUTHORIZED_SET - outside)}\n"
            f"Collected but not allowlisted (new leak): {sorted(outside - _AUTHORIZED_SET)}"
        )

    def test_gating_expression_still_collects_the_non_bimodal_suite(self):
        """Positive complement of the leak check: the gating drivers' own parallel `-m`
        expression must still collect a substantial suite. A leaking marker application shows up
        here as a near-total collapse in collected count, independent of how the marker got
        applied."""
        gating_expr = (
            "not packaging and not performance and not unstable "
            "and not xdist_serial and not development"
        )
        gated = _collect("-m", gating_expr, "tests", "src/model_checker")
        assert len(gated) > 1000, (
            f"the gating parallel expression collected only {len(gated)} tests across "
            f"`tests src/model_checker`, which is far below the expected suite size -- the "
            f"`development` marker is being applied beyond bimodal and is emptying the gate"
        )
        bimodal_survivors = [n for n in gated if n.startswith(BIMODAL_TESTS)]
        assert bimodal_survivors == [], (
            f"{len(bimodal_survivors)} bimodal test(s) survive the gating parallel expression "
            f"in a mixed-root collection: {bimodal_survivors[:10]}"
        )
