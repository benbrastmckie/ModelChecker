"""Executable contract: no *new* bimodal-coupled example fixture can silently enter a
release-gating selection unclassified.

This is the standing guard the audit behind this contract exists to leave in place: for every
file textually referencing bimodal as an example fixture (`from model_checker.theory_lib import
bimodal` or `from model_checker.theory_lib.bimodal import ...`) that also has at least one test
item collected by a gating selection -- the main gating expression over `tests
src/model_checker`, or the packaging expression over `tests/packaging/` -- and that lies outside
`src/model_checker/theory_lib/bimodal/tests/` (the theory's own tree, already fully quarantined
by its `development` blanket; see `test_development_marker_application.py`), the file must appear
in exactly one of two enumerated, commented constants below:

- `_SOLVE_FREE_BIMODAL_REFERENCES`: files the audit classified as construct-only, mocked, or
  string/registry-only -- no `BuildExample`/`ModelDefaults` construction is reachable through
  the gating selection, so there is no bimodal solve cost to decouple.
- `_DELIBERATE_BIMODAL_GATING`: the single authorized real-solve retention,
  `builder/tests/e2e/test_full_pipeline.py::test_theory_library_execution`, whose `"World
  Histories"` assertion is bimodal's own model-rendering label and is not reproducible under any
  other theory (see that test's own deliberate-retention comment and TESTING_GUIDE.md section
  8.14).

A file matching neither list is new, unclassified bimodal coupling -- this test goes RED and
names it, forcing a deliberate classification (fix it, mark it `development`, or add it to the
solve-free list with a reason) rather than letting it silently re-couple the gate to bimodal's
solve cost.

**Known, honest blind spot**: this is a *static source* check at file granularity, not a runtime
solve-cost measurement. It catches a newly introduced `from model_checker.theory_lib import
bimodal`-style fixture, but it cannot catch a bimodal solve reached through an indirection it
does not textually see -- the concrete instance of this already known to exist is
`tests/packaging/test_generate_then_execute.py`, which constructs `BuildProject(theory_name)` for
every `registry.get_registered()` entry (including `"bimodal"`) without ever spelling the word
"bimodal" in its own source. That file's bimodal-coupled cost is real and is handled by a
different mechanism -- a per-parametrize `@pytest.mark.development` marking (see that file and
`test_development_marker_application.py`'s allowlist) -- not by this contract, and this contract
does not claim to cover it. The complementary evidence for "the decoupling actually happened" is
the paired before/after wall-clock record this task also produces, not this contract alone.
"""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

import pytest

CODE_DIR = Path(__file__).resolve().parents[2]
SRC_DIR = CODE_DIR / "src"
BIMODAL_TESTS_PREFIX = "src/model_checker/theory_lib/bimodal/tests"

# This contract's own source file, excluded from the candidate scan below: it necessarily
# quotes the reference snippets it is searching for (as string literals in
# _BIMODAL_REFERENCE_RE_SNIPPETS and in this docstring/comments), which would otherwise make it
# match its own pattern as a false positive on every run.
_THIS_FILE_RELPATH = str(Path(__file__).resolve().relative_to(CODE_DIR))

_BIMODAL_REFERENCE_RE_SNIPPETS = (
    "from model_checker.theory_lib import bimodal",
    "from model_checker.theory_lib.bimodal import",
)

# Files whose only reachable-via-gating bimodal reference is construct-only, mocked, string/
# registry-only, or otherwise carries no Z3 solve cost. One reason per entry, per this contract's
# own module docstring.
_SOLVE_FREE_BIMODAL_REFERENCES = {
    # BuildModule.__init__ parses/loads but never solves (no BuildExample/get_result()/
    # run_examples() call anywhere in the file) -- confirmed by reading builder/module.py's
    # loading path and this file's own assertions (attribute presence only).
    "src/model_checker/builder/tests/integration/test_build_module_theories.py":
        "BuildModule construction only; no BuildExample/run_examples() call in the file",
    "src/model_checker/builder/tests/integration/test_component_integration.py":
        "BuildModule construction only; no BuildExample/run_examples() call in the file",
    # The file's one bimodal reference lives entirely inside
    # test_build_example_bimodal_theory_countermodel, which carries @pytest.mark.development
    # (see TESTING_GUIDE.md section 8.14's "Per-test markings" record) -- its real solve is
    # therefore never reachable through any `-m "not development"` gating selection.
    "src/model_checker/builder/tests/unit/test_example.py":
        "the file's only bimodal reference is inside a per-test development-marked test, "
        "unreachable via any gating selection",
    # get_theory() is inspected for dict shape / module attribution only; no example is run.
    "src/model_checker/builder/tests/unit/test_loader.py":
        "bimodal.get_theory() used only to inspect dict shape; no example is run",
    # Serializes the theory dict (class references, module paths); never constructs a
    # BuildExample/ModelDefaults, no Z3 solve.
    "src/model_checker/builder/tests/unit/test_serialize.py":
        "serializes the theory dict only; no BuildExample/ModelDefaults construction",
    # Remaining bimodal references, after this task's create_test_model() default-to-logos fix,
    # are Syntax-parsing-only helpers (Syntax([], [formula], operators), no ModelDefaults/
    # BuildExample construction) or a CLI-subprocess content string whose module fails to
    # validate before any example is run.
    "tests/integration/test_error_handling.py":
        "remaining references are Syntax-parsing-only helpers and a "
        "missing-required-attributes CLI-subprocess probe; no real solve",
    "tests/integration/test_performance.py":
        "remaining references are Syntax-parsing-only and theory-cache-identity checks; "
        "no real solve",
    # Pure import-availability smoke test: `assert bimodal is not None`. No solve.
    "tests/integration/test_system_imports.py":
        "import-availability smoke test only (`assert bimodal is not None`); no solve",
    # Remaining bimodal references are CLI-subprocess content strings at bounded/tiny cost
    # (N=2 x3 iterations, and N=64 with max_time=0.01 which fails fast) -- audited directly in
    # this task's create_test_model() fix phase; no real BuildExample/ModelDefaults construction
    # happens in this test process itself.
    "tests/integration/test_timeout_resources.py":
        "remaining references are bounded/tiny CLI-subprocess content strings "
        "(N=2 or N=64-with-max_time=0.01); no material gating cost",
}

# The single authorized real-solve retention: subject and reason recorded per this contract's
# own module docstring.
_DELIBERATE_BIMODAL_GATING = {
    "src/model_checker/builder/tests/e2e/test_full_pipeline.py":
        'test_theory_library_execution asserts "World Histories" -- bimodal\'s own '
        "model-rendering label, not reproducible under any other theory; retains its "
        "existing max_time=10",
}


def _collect_node_ids(*args: str) -> list[str]:
    """Return collected node ids from `pytest --collect-only -q <args>`, run in a subprocess
    rooted at `code/`. Mirrors `test_development_marker_application.py::_collect`'s shape and
    `--import-mode=importlib` rationale (mixed-root same-named-module collisions)."""
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
    if completed.returncode not in (0, 5):
        pytest.fail(
            f"pytest --collect-only failed (exit {completed.returncode}) for args {args!r}\n"
            f"--- stdout ---\n{completed.stdout}\n--- stderr ---\n{completed.stderr}"
        )
    return [line.strip() for line in completed.stdout.splitlines() if "::" in line]


# The two gating selections this contract covers, in the same shape the real drivers use.
_MAIN_GATING_EXPR = (
    "not packaging and not performance and not unstable and not xdist_serial and not development"
)
_PACKAGING_GATING_EXPR = "packaging and not unstable and not development"


def _gating_collected_files() -> set[str]:
    """File paths (relative to `code/`, `::`-prefix stripped) collected by either gating
    selection."""
    main_ids = _collect_node_ids("-m", _MAIN_GATING_EXPR, "tests", "src/model_checker")
    packaging_ids = _collect_node_ids("-m", _PACKAGING_GATING_EXPR, "tests/packaging/")
    files = set()
    for nodeid in main_ids + packaging_ids:
        files.add(nodeid.split("::", 1)[0])
    return files


def _assert_gating_collection_nonvacuous(gated_files: set) -> None:
    """Raises AssertionError if `gated_files` is empty. Factored out of the test body so the
    anti-vacuity test below can exercise this exact assertion against a deliberately empty
    input and confirm it actually fires, per this contract's own Pre-Edit Verification Gate
    obligation not to leave an anti-vacuity claim unexercised."""
    assert gated_files, (
        "the gating collection (main + packaging expressions) returned no files at all -- "
        "collection itself is broken, which would make this contract vacuous"
    )


def _file_references_bimodal(relpath: str) -> bool:
    path = CODE_DIR / relpath
    if not path.exists():
        return False
    text = path.read_text()
    return any(snippet in text for snippet in _BIMODAL_REFERENCE_RE_SNIPPETS)


class TestGatingSelectionBimodalDecoupling:
    """No new, unclassified bimodal-coupled fixture can enter a gating selection."""

    def test_every_bimodal_referencing_gating_file_is_classified(self):
        gated_files = _gating_collected_files()
        _assert_gating_collection_nonvacuous(gated_files)

        candidates = sorted(
            f for f in gated_files
            if f != _THIS_FILE_RELPATH
            and not f.startswith(BIMODAL_TESTS_PREFIX)
            and _file_references_bimodal(f)
        )
        assert candidates, (
            "the bimodal-reference scan found no candidate files at all across the gating "
            "selections -- this would make the classification assertion below vacuous; if "
            "this is genuinely expected (e.g. every reference was removed), the enumerated "
            "constants above should be emptied deliberately, not left stale"
        )

        known = set(_SOLVE_FREE_BIMODAL_REFERENCES) | set(_DELIBERATE_BIMODAL_GATING)
        unclassified = sorted(set(candidates) - known)
        assert not unclassified, (
            f"{len(unclassified)} file(s) collected by a gating selection reference bimodal as "
            f"an example fixture but are not classified in _SOLVE_FREE_BIMODAL_REFERENCES or "
            f"_DELIBERATE_BIMODAL_GATING: {unclassified}. Classify each: fix it (swap to a "
            f"cheap theory or mark the specific test `development`), or add it to "
            f"_SOLVE_FREE_BIMODAL_REFERENCES with a one-line reason if it genuinely carries no "
            f"solve cost."
        )

    def test_solve_free_allowlist_entries_still_exist_and_still_reference_bimodal(self):
        stale = [
            path for path in _SOLVE_FREE_BIMODAL_REFERENCES if not _file_references_bimodal(path)
        ]
        assert not stale, (
            f"{len(stale)} _SOLVE_FREE_BIMODAL_REFERENCES entry(ies) no longer exist or no "
            f"longer reference bimodal (stale after a rename/fix) -- remove them rather than "
            f"leaving a dead entry that silently widens what this contract does not check: "
            f"{stale}"
        )

    def test_deliberate_gating_allowlist_entries_still_exist_and_still_reference_bimodal(self):
        stale = [
            path for path in _DELIBERATE_BIMODAL_GATING if not _file_references_bimodal(path)
        ]
        assert not stale, (
            f"{len(stale)} _DELIBERATE_BIMODAL_GATING entry(ies) no longer exist or no longer "
            f"reference bimodal: {stale}"
        )

    def test_no_entry_is_listed_in_both_allowlists(self):
        overlap = sorted(set(_SOLVE_FREE_BIMODAL_REFERENCES) & set(_DELIBERATE_BIMODAL_GATING))
        assert not overlap, (
            f"{len(overlap)} file(s) are listed in both allowlists, which is ambiguous: "
            f"{overlap}"
        )

    def test_empty_collection_root_actually_returns_nothing(self):
        """Precondition for the anti-vacuity check below: a real, existing root that holds no
        test files at all (`code/docs/core/`, a documentation directory) must collect zero node
        ids (exit code 5, "no tests collected"), not silently succeed with unrelated items. If
        this failed, the anti-vacuity test below would be probing the wrong scenario. A genuinely
        nonexistent path is deliberately not used here -- pytest treats that as a usage error
        (exit 4), a different failure mode than the "collected nothing real" scenario this
        contract's anti-vacuity guard exists to catch."""
        empty_root_ids = _collect_node_ids("-m", _MAIN_GATING_EXPR, "docs/core")
        assert empty_root_ids == [], (
            "collecting a documentation-only root unexpectedly returned node ids -- the "
            "collection helper itself is behaving unexpectedly"
        )

    def test_anti_vacuity_guard_actually_fails_on_an_empty_collection(self):
        """Exercises the anti-vacuity assertion directly against a deliberately empty
        collection, confirming it fails rather than passes -- so the non-empty check in
        test_every_bimodal_referencing_gating_file_is_classified is proven to be a real guard,
        not a tautology that could never fire."""
        with pytest.raises(AssertionError, match="returned no files at all"):
            _assert_gating_collection_nonvacuous(set())
