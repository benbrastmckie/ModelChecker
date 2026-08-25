"""AST-based regression guard for the D3 marker taxonomy (see
`code/docs/core/TESTING_GUIDE.md` and `code/pyproject.toml`'s `xdist_serial` marker
registration): any test function that both reads a real wall-clock and asserts a bound
comparison on the value it derives from that read must carry `@pytest.mark.performance` or
`@pytest.mark.xdist_serial`, so it cannot land in the contended `-n 6` pool unmarked and
silently reintroduce a wall-clock flake.

**Detection is a structural AST scan, not full dataflow analysis.** A test function is flagged
when, within its own body OR a same-module helper function it calls (the one-hop case --
`code/src/model_checker/builder/tests/e2e/test_project_edge_cases.py`'s
`assert_warm_iterations_consistent(self, operation_times)` helper is exactly this shape: the
clock read is in the test, the bound assertion is in the helper it calls), both of the following
hold:

1. A call to `time.time()`, `time.perf_counter()`, or `time.monotonic()` appears somewhere in
   the scanned code (these three, matching the phase's own named scope -- `time.sleep()` is
   deliberately NOT treated as a clock *read* here, since a test that only sleeps and asserts on
   a value some other layer computed from its own internal clock is one hop further removed than
   this guard's declared scope; `test_progress_bar_ordering.py::test_freeze_complete_time_consistency`
   is exactly this excluded shape).
2. An `assert <comparison>` (or a `self.assertLess`/`assertGreater`/`assertLessEqual`/
   `assertGreaterEqual` call) using `<`, `>`, `<=`, or `>=` appears in the same scope.

A flagged function must carry `performance` or `xdist_serial`, checked at the function's own
decorators, its enclosing class's decorators (covers class-level marking, e.g.
`TestPerformanceAndScalabilityScenarios`), or a module-level `pytestmark = [...]` list.
"""

from __future__ import annotations

import ast
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
SCAN_ROOTS = [
    REPO_ROOT / "code" / "src" / "model_checker",
    REPO_ROOT / "code" / "tests",
]

_CLOCK_READ_ATTRS = {"time", "perf_counter", "monotonic"}
_BOUND_CMP_OPS = (ast.Lt, ast.Gt, ast.LtE, ast.GtE)
_UNITTEST_BOUND_METHODS = {
    "assertLess",
    "assertGreater",
    "assertLessEqual",
    "assertGreaterEqual",
}
_REQUIRED_MARKERS = {"performance", "xdist_serial"}

# Explicit, commented allowlist for modules that patch/mock the clock rather than reading real
# wall-clock time -- a mocked `time.time()` return value compared against a bound is not a real
# contention-sensitive assertion and does not need a marker. Entries are
# (path relative to REPO_ROOT, qualified test name) pairs. Empty today: a full-tree scan (see
# this module's own verification history in
# specs/169_eliminate_wall_clock_sensitive_test_flakes/handoffs/) confirmed the one candidate
# module doing real time-patching --
# code/src/model_checker/models/tests/unit/test_structure.py -- does not match this guard's AST
# pattern in the first place (its mocked-time assertions are not shaped as a same-scope
# clock-read-plus-bound-comparison), so no suppression is currently needed. Add an entry here,
# with a comment naming the mocking mechanism, if a future mocked-clock test does match.
MOCKED_CLOCK_ALLOWLIST: set[tuple[str, str]] = set()


def _iter_test_files():
    for root in SCAN_ROOTS:
        yield from sorted(root.rglob("test_*.py"))


def _calls_clock(node: ast.AST) -> bool:
    for n in ast.walk(node):
        if (
            isinstance(n, ast.Call)
            and isinstance(n.func, ast.Attribute)
            and n.func.attr in _CLOCK_READ_ATTRS
            and isinstance(n.func.value, ast.Name)
            and n.func.value.id == "time"
        ):
            return True
    return False


def _has_bound_assertion(node: ast.AST) -> bool:
    for n in ast.walk(node):
        if isinstance(n, ast.Assert) and isinstance(n.test, ast.Compare):
            if any(isinstance(op, _BOUND_CMP_OPS) for op in n.test.ops):
                return True
        if (
            isinstance(n, ast.Call)
            and isinstance(n.func, ast.Attribute)
            and n.func.attr in _UNITTEST_BOUND_METHODS
        ):
            return True
    return False


def _called_names(node: ast.AST) -> set[str]:
    return {
        n.func.id
        for n in ast.walk(node)
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
    }


def _marker_name_from_decorator(dec: ast.AST) -> str | None:
    target = dec.func if isinstance(dec, ast.Call) else dec
    # Matches `pytest.mark.<name>` (as `Attribute(Attribute(Name('pytest'), 'mark'), name)`).
    if (
        isinstance(target, ast.Attribute)
        and isinstance(target.value, ast.Attribute)
        and isinstance(target.value.value, ast.Name)
        and target.value.value.id == "pytest"
        and target.value.attr == "mark"
    ):
        return target.attr
    return None


def _marker_names(decorator_list: list[ast.AST]) -> set[str]:
    names = set()
    for dec in decorator_list:
        name = _marker_name_from_decorator(dec)
        if name:
            names.add(name)
    return names


def _module_pytestmark_names(tree: ast.Module) -> set[str]:
    names = set()
    for node in tree.body:
        if isinstance(node, ast.Assign) and any(
            isinstance(t, ast.Name) and t.id == "pytestmark" for t in node.targets
        ):
            elts = node.value.elts if isinstance(node.value, (ast.List, ast.Tuple)) else [node.value]
            for elt in elts:
                name = _marker_name_from_decorator(elt)
                if name:
                    names.add(name)
    return names


def _find_unmarked_timing_tests(path: Path) -> list[str]:
    try:
        tree = ast.parse(path.read_text())
    except SyntaxError:
        return []

    module_funcs = [
        n for n in ast.walk(tree) if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))
    ]
    # One-hop helper tracing: a same-module, non-test function whose own body already carries a
    # bound assertion counts as satisfying the assertion half when a test function calls it by
    # name (see module docstring's assert_warm_iterations_consistent example).
    bound_assert_helpers = {
        n.name
        for n in module_funcs
        if _has_bound_assertion(n) and not n.name.startswith("test")
    }
    module_marker_names = _module_pytestmark_names(tree)

    # Map each FunctionDef to its enclosing ClassDef (or None), for class-level marker lookup.
    enclosing_class: dict[int, ast.ClassDef] = {}
    for node in ast.walk(tree):
        if isinstance(node, ast.ClassDef):
            for child in node.body:
                if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    enclosing_class[id(child)] = node

    label = str(path.relative_to(REPO_ROOT))
    violations = []
    for node in module_funcs:
        if not node.name.startswith("test"):
            continue
        has_assertion = _has_bound_assertion(node) or bool(
            _called_names(node) & bound_assert_helpers
        )
        if not (_calls_clock(node) and has_assertion):
            continue
        if (label, node.name) in MOCKED_CLOCK_ALLOWLIST:
            continue

        markers = set(module_marker_names)
        markers |= _marker_names(node.decorator_list)
        parent = enclosing_class.get(id(node))
        if parent is not None:
            markers |= _marker_names(parent.decorator_list)

        if not (markers & _REQUIRED_MARKERS):
            violations.append(f"{label}::{node.name} (line {node.lineno})")
    return violations


def test_all_wall_clock_timing_assertions_are_marked():
    all_violations = []
    for path in _iter_test_files():
        all_violations.extend(_find_unmarked_timing_tests(path))

    assert not all_violations, (
        "The following test functions read a real clock (time.time/perf_counter/monotonic) "
        "and assert a bound comparison on the derived value, but carry neither "
        "@pytest.mark.performance nor @pytest.mark.xdist_serial -- they would land in the "
        "contended -n 6 pool unmarked. Mark them per code/docs/core/TESTING_GUIDE.md's marker "
        "taxonomy, or add a justified entry to this module's MOCKED_CLOCK_ALLOWLIST if the clock "
        "is mocked:\n  " + "\n  ".join(sorted(all_violations))
    )


def test_scan_finds_the_known_marked_inventory():
    """Sanity check that the AST scan's positive-detection logic actually fires (not just that
    it stays silent) -- confirms the scan recognizes the established `xdist_serial`/`performance`
    inventory rather than vacuously matching nothing."""
    known = {
        (
            "code/src/model_checker/builder/tests/e2e/test_project_edge_cases.py",
            "test_multiple_project_generation_completes_within_reasonable_time",
        ),
        (
            "code/src/model_checker/builder/tests/e2e/test_project_edge_cases.py",
            "test_repeated_project_operations_maintain_consistent_performance",
        ),
        (
            "code/src/model_checker/builder/tests/integration/test_performance.py",
            "test_module_loading_performance",
        ),
        (
            "code/src/model_checker/builder/tests/integration/test_performance.py",
            "test_serialization_performance",
        ),
        (
            "code/src/model_checker/builder/tests/test_refactoring_target_behavior.py",
            "test_performance_improvement",
        ),
        (
            "code/src/model_checker/builder/tests/unit/test_project_version.py",
            "test_version_detection_performance_is_reasonable",
        ),
        (
            "code/src/model_checker/builder/tests/unit/test_serialize.py",
            "test_serialize_semantic_theory_handles_large_operator_collections",
        ),
        ("code/tests/integration/test_performance.py", "test_complex_model_performance"),
        ("code/tests/integration/test_timeout_resources.py", "test_z3_solver_timeout"),
        ("code/tests/integration/test_timeout_resources.py", "test_cli_command_timeout"),
    }
    found = set()
    for path in _iter_test_files():
        try:
            tree = ast.parse(path.read_text())
        except SyntaxError:
            continue
        module_funcs = [
            n for n in ast.walk(tree) if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))
        ]
        bound_assert_helpers = {
            n.name
            for n in module_funcs
            if _has_bound_assertion(n) and not n.name.startswith("test")
        }
        label = str(path.relative_to(REPO_ROOT))
        for node in module_funcs:
            if not node.name.startswith("test"):
                continue
            has_assertion = _has_bound_assertion(node) or bool(
                _called_names(node) & bound_assert_helpers
            )
            if _calls_clock(node) and has_assertion:
                found.add((label, node.name))

    missing = known - found
    assert not missing, f"AST scan failed to detect known timing-assertion tests: {sorted(missing)}"
