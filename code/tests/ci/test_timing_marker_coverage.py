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

**Embedded-source-string route.** The two conditions above can also live inside a Python source
string handed to a subprocess/exec-style call site (`subprocess.run`/`call`/`check_call`/
`check_output`/`Popen`, or bare `exec`/`eval`) rather than in the scanned function's own
statements -- exactly the shape `test_import_performs_no_subprocess_call` used before this guard
was extended: `code = ("import time\\n" "t = time.time()\\n" ... "assert elapsed < 1.0\\n")`
followed by `subprocess.run([sys.executable, "-c", code], ...)`. To an `ast.walk` over the outer
function, that whole string is a single opaque `ast.Constant` -- nothing to flag. The scan
resolves this one specific, deliberately narrow shape: a string literal passed directly as a
call argument, OR a string first bound to a local name via a simple `x = "..."` assignment and
then referenced by that name (including one level inside a `list`/`tuple` argument, e.g.
`[sys.executable, "-c", code]`), is parsed as its own Python source and re-scanned with the same
two conditions above. A resolved string that fails to parse as Python is silently skipped (most
likely a shell command line, not embedded Python source). This stays a structural scan, not
dataflow: `+=`/f-string-built strings, strings assembled across multiple statements, and strings
passed through an intermediate function call are all out of scope, same as the module-level
non-dataflow posture already documented above.

`os.system` is deliberately NOT added to the recognized call-target set: its argument is a shell
command line, not Python source, so resolving and `ast.parse`-ing it would routinely raise
`SyntaxError` and never match -- the same "not embedded Python" reasoning the paragraph above
already gives for skipping unparseable resolved strings, just decided up front for a call target
known to hit it every time.
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


_SUBPROCESS_CALL_ATTRS = {"run", "call", "check_call", "check_output", "Popen"}
_EXEC_STYLE_NAMES = {"exec", "eval"}


def _is_source_executing_call(func: ast.AST) -> bool:
    """True for `subprocess.run`/`call`/`check_call`/`check_output`/`Popen` calls and bare
    `exec`/`eval` calls -- the recognized call-target set for the embedded-source-string route
    (see module docstring)."""
    if (
        isinstance(func, ast.Attribute)
        and func.attr in _SUBPROCESS_CALL_ATTRS
        and isinstance(func.value, ast.Name)
        and func.value.id == "subprocess"
    ):
        return True
    return isinstance(func, ast.Name) and func.id in _EXEC_STYLE_NAMES


def _local_string_bindings(node: ast.AST) -> dict[str, str]:
    """Map `name -> value` for every simple `name = "constant string"` assignment found anywhere
    in `node` (structural, not scope-aware -- consistent with this module's other helpers, which
    already walk the full subtree rather than tracking scope boundaries)."""
    bindings: dict[str, str] = {}
    for n in ast.walk(node):
        if (
            isinstance(n, ast.Assign)
            and len(n.targets) == 1
            and isinstance(n.targets[0], ast.Name)
            and isinstance(n.value, ast.Constant)
            and isinstance(n.value.value, str)
        ):
            bindings[n.targets[0].id] = n.value.value
    return bindings


def _candidate_strings_from_value(value: ast.AST, bindings: dict[str, str]) -> list[str]:
    """Extract candidate embedded-source strings from a single call argument: a direct string
    constant, a name resolved through `bindings`, or either of those nested one level inside a
    `list`/`tuple` literal (the `[sys.executable, "-c", code]` shape)."""
    if isinstance(value, ast.Constant) and isinstance(value.value, str):
        return [value.value]
    if isinstance(value, ast.Name) and value.id in bindings:
        return [bindings[value.id]]
    if isinstance(value, (ast.List, ast.Tuple)):
        candidates = []
        for elt in value.elts:
            if isinstance(elt, ast.Constant) and isinstance(elt.value, str):
                candidates.append(elt.value)
            elif isinstance(elt, ast.Name) and elt.id in bindings:
                candidates.append(bindings[elt.id])
        return candidates
    return []


def _embedded_trees(node: ast.AST) -> list[ast.AST]:
    """Resolve and parse Python source strings passed to subprocess/exec-style call sites within
    `node` (see module docstring). A resolved string that fails to parse as Python is skipped."""
    bindings = _local_string_bindings(node)
    trees: list[ast.AST] = []
    for n in ast.walk(node):
        if not (isinstance(n, ast.Call) and _is_source_executing_call(n.func)):
            continue
        candidates: list[str] = []
        for arg in n.args:
            candidates.extend(_candidate_strings_from_value(arg, bindings))
        for kw in n.keywords:
            if kw.value is not None:
                candidates.extend(_candidate_strings_from_value(kw.value, bindings))
        for source in candidates:
            try:
                trees.append(ast.parse(source))
            except SyntaxError:
                continue
    return trees


def _scanned_trees(node: ast.AST) -> list[ast.AST]:
    """The function's own node plus every embedded-source tree resolved from it -- the shared
    union both `_calls_clock_deep` and `_has_bound_assertion_deep` scan over."""
    return [node] + _embedded_trees(node)


def _calls_clock_deep(node: ast.AST) -> bool:
    return any(_calls_clock(t) for t in _scanned_trees(node))


def _has_bound_assertion_deep(node: ast.AST) -> bool:
    return any(_has_bound_assertion(t) for t in _scanned_trees(node))


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

    try:
        label = str(path.relative_to(REPO_ROOT))
    except ValueError:
        label = str(path)
    violations = []
    for node in module_funcs:
        if not node.name.startswith("test"):
            continue
        has_assertion = _has_bound_assertion_deep(node) or bool(
            _called_names(node) & bound_assert_helpers
        )
        if not (_calls_clock_deep(node) and has_assertion):
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
            has_assertion = _has_bound_assertion_deep(node) or bool(
                _called_names(node) & bound_assert_helpers
            )
            if _calls_clock_deep(node) and has_assertion:
                found.add((label, node.name))

    missing = known - found
    assert not missing, f"AST scan failed to detect known timing-assertion tests: {sorted(missing)}"


def _embedded_subprocess_fixture_source(*, marked: bool) -> str:
    """Build the source of a synthetic test module reproducing the pre-fix
    `test_import_performs_no_subprocess_call` shape: a clock-read-plus-bound-assert pair living
    inside a Python source string that is bound to a local name (`code`) and then referenced by
    that name inside a list literal argument to `subprocess.run`. This is exactly the shape an
    `ast.walk` over the *outer* module's own nodes cannot see -- the clock call and the bound
    assert exist only inside the string's own text, one `ast.Constant` node to the outer scan.
    """
    decorator = "    @pytest.mark.xdist_serial\n" if marked else ""
    return (
        "import subprocess\n"
        "import sys\n"
        "\n"
        "import pytest\n"
        "\n"
        "\n"
        "class TestEmbedded:\n"
        f"{decorator}"
        "    def test_import_is_fast(self):\n"
        "        code = (\n"
        '            "import time\\n"\n'
        '            "t = time.time()\\n"\n'
        '            "elapsed = time.time() - t\\n"\n'
        '            "assert elapsed < 1.0, elapsed\\n"\n'
        "        )\n"
        "        result = subprocess.run(\n"
        '            [sys.executable, "-c", code], capture_output=True, text=True, timeout=15\n'
        "        )\n"
        "        assert result.returncode == 0\n"
    )


def test_embedded_subprocess_source_is_flagged_when_unmarked(tmp_path):
    """`_find_unmarked_timing_tests` must resolve the local-variable binding and parse the
    embedded source string, not just walk the outer module's own AST nodes."""
    fixture = tmp_path / "test_embedded_fixture.py"
    fixture.write_text(_embedded_subprocess_fixture_source(marked=False))

    violations = _find_unmarked_timing_tests(fixture)

    assert len(violations) == 1, violations
    assert "test_import_is_fast" in violations[0]


def test_embedded_subprocess_source_respects_marker_suppression(tmp_path):
    """The same embedded-string shape, but with the function itself decorated
    `@pytest.mark.xdist_serial` -- must NOT be flagged."""
    fixture = tmp_path / "test_embedded_fixture_marked.py"
    fixture.write_text(_embedded_subprocess_fixture_source(marked=True))

    violations = _find_unmarked_timing_tests(fixture)

    assert violations == []
