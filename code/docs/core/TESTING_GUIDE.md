# Comprehensive Testing Guide

[← Code Standards](CODE_STANDARDS.md) | [Back to Core](README.md) | [Architecture →](ARCHITECTURE.md)

## Overview

This guide defines comprehensive testing standards for the ModelChecker codebase, consolidating testing practices, test organization, and Test-Driven Development requirements into a unified framework. These standards ensure maintainable, reliable, and efficient tests that support long-term codebase evolution.

**Core Testing Philosophy:**
- **Test-Driven Development**: Write tests BEFORE implementation code
- **Fail Fast**: Tests expose errors clearly rather than masking them
- **Minimal Mocking**: Use real objects wherever possible, mock only external dependencies
- **Clear Separation**: Distinct unit, integration, and end-to-end test categories
- **Test Isolation**: Tests run independently without contaminating the environment
- **Comprehensive Documentation**: Every test explains what behavior is verified

---

## Table of Contents

1. [Test-Driven Development Requirements](#1-test-driven-development-requirements)
2. [Test Organization and Structure](#2-test-organization-and-structure)
3. [Test Categories](#3-test-categories)
4. [Running Tests](#4-running-tests)
5. [Writing Effective Tests](#5-writing-effective-tests)
6. [Theory-Specific Testing](#6-theory-specific-testing)
7. [Test Coverage Requirements](#7-test-coverage-requirements)
8. [Best Practices and Patterns](#8-best-practices-and-patterns)

---

## 1. Test-Driven Development Requirements

### 1.1 TDD Workflow (RED-GREEN-REFACTOR)

**MANDATORY Process**: All new features and fixes MUST follow TDD:

```python
# RED: Write failing test first
def test_new_feature_handles_valid_input_successfully():
    """Test new feature processes valid input correctly."""
    # This test will fail initially
    input_data = TestExamples.SIMPLE_VALID
    expected_output = "processed_successfully"

    result = new_feature(input_data)

    assert result == expected_output, \
        "New feature should process valid input successfully"

# GREEN: Write minimal implementation to pass
def new_feature(data):
    # Minimal implementation to make test pass
    if data == TestExamples.SIMPLE_VALID:
        return "processed_successfully"
    raise NotImplementedError("Additional cases not implemented yet")

# REFACTOR: Improve code quality while keeping tests passing
def new_feature(data):
    # Full implementation with proper logic
    validate_input(data)
    processed = process_data(data)
    return format_output(processed)
```

### 1.2 TDD Compliance Requirements

**Before any code implementation:**
1. **Write Failing Test**: Create test that describes desired behavior
2. **Run Test**: Verify test fails (RED state)
3. **Minimal Implementation**: Write just enough code to pass
4. **Run Test**: Verify test passes (GREEN state)
5. **Refactor**: Improve code quality while maintaining passing tests
6. **Repeat**: Continue cycle for next requirement

**TDD Verification Checklist:**
- [ ] Test written before implementation
- [ ] Test initially fails (proves it tests something)
- [ ] Minimal implementation makes test pass
- [ ] Code refactored for quality
- [ ] All tests still pass after refactoring

### 1.3 TDD for Bug Fixes

**Bug Fix Process:**
1. **Reproduce Bug**: Write test that demonstrates the bug
2. **Verify Failure**: Confirm test fails with current code
3. **Fix Bug**: Make minimal changes to pass the test
4. **Verify Fix**: Ensure test passes and bug is resolved
5. **Regression Prevention**: Test prevents bug from reoccurring

```python
def test_bug_fix_loader_handles_malformed_syntax_gracefully():
    """Test that ModuleLoader handles malformed syntax with helpful error.

    Bug: ModuleLoader crashes with unhelpful error when syntax is malformed.
    Expected: Should raise ImportError with clear message about syntax issues.
    """
    malformed_content = "this is not valid python !@#$"
    loader = ModuleLoader("test", create_temp_file(malformed_content))

    with pytest.raises(ImportError) as exc_info:
        loader.load_module()

    error_msg = str(exc_info.value).lower()
    assert "syntax" in error_msg, "Error should mention syntax problem"
    assert "malformed" in error_msg, "Error should indicate malformed code"
```

---

## 2. Test Organization and Structure

### 2.1 Test Directory Structure

```
code/
├── tests/                         # Top-level test discovery
│   ├── unit/                      # Unit tests for packages
│   └── integration/               # Cross-package integration tests
└── src/model_checker/
    ├── theory_lib/
    │   ├── logos/
    │   │   └── tests/
    │   │       ├── unit/          # Theory unit tests
    │   │       └── integration/   # Theory integration tests
    │   ├── exclusion/
    │   │   └── tests/
    │   │       ├── unit/
    │   │       └── integration/
    │   └── tests/                 # Cross-theory infrastructure tests
    ├── builder/
    │   └── tests/
    │       └── unit/
    └── iterate/
        └── tests/
            └── unit/
```

### 2.2 Test File Naming Conventions

- **Unit tests**: `test_<module_name>.py` (e.g., `test_semantic.py`)
- **Integration tests**: `test_<feature>_integration.py`
- **Example tests**: `test_<theory>_examples.py`
- **Test modules**: Mirror the structure of source code

### 2.3 Test Runner Configuration

The ModelChecker project uses two complementary test approaches:

**Method 1: pytest (Primary)**
```bash
# From project root, run all tests
PYTHONPATH=code/src pytest code/tests/ -v

# Run specific theory tests
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/tests/ -v

# Run with coverage
PYTHONPATH=code/src pytest --cov=model_checker --cov-report=term-missing
```

**Method 2: dev_cli.py (Development)**
```bash
# Run tests through development CLI
cd Code
./dev_cli.py test
```

---

## 3. Test Categories

### 3.1 Example Tests (Integration Tests)

**Purpose**: Validate that the model checker produces correct results for logical examples

**Characteristics**:
- Test complete model checking pipeline from formula parsing to result validation
- Use realistic logical examples that demonstrate theory capabilities
- Validate both valid arguments (no countermodel) and invalid arguments (countermodel found)
- Cover all operator types and their interactions

**Location**:
- `theory_lib/*/tests/integration/test_*_examples.py`
- `theory_lib/*/subtheories/*/tests/integration/test_*_examples.py`

**Example Structure**:
```python
def test_logos_modus_ponens_is_valid():
    """Test that modus ponens is valid in logos theory.

    Formula: (p → q), p ⊢ q
    Expected: Valid (no countermodel)
    """
    premises = ["(p > q)", "p"]
    conclusion = "q"

    result = check_validity(premises, conclusion, theory="logos")

    assert result.is_valid, "Modus ponens should be valid"
    assert result.countermodel is None, "Should have no countermodel"
```

### 3.2 Unit Tests (Component Tests)

**Purpose**: Validate individual software components work correctly

**Characteristics**:
- Test semantic methods directly (without full model checking pipeline)
- Test operator implementations and their semantic clauses
- Test registry and loading mechanisms
- Test error conditions and edge cases
- Validate API contracts and data structures

**Location**:
- `theory_lib/*/tests/unit/test_*.py`
- `builder/tests/unit/test_*.py`
- `iterate/tests/unit/test_*.py`

**Example Structure**:
```python
def test_semantic_evaluates_conjunction_correctly():
    """Test that conjunction operator evaluates correctly."""
    semantic = LogosSemantic()
    model = semantic.create_base_model()

    # Set up: p=True, q=False
    model.add_constraint(semantic.atoms['p'] == True)
    model.add_constraint(semantic.atoms['q'] == False)

    # Test: p ∧ q should be False
    conjunction = semantic.evaluate_and(model, 'p', 'q')

    assert conjunction == False, "p ∧ q should be False when q is False"
```

### 3.3 Infrastructure Tests

**Purpose**: Verify cross-theory functionality and framework infrastructure

**Characteristics**:
- Metadata management (versions, citations, licenses)
- Theory discovery and loading
- Cross-theory compatibility
- Common functionality validation

**Location**: `theory_lib/tests/`

---

## 4. Running Tests

### 4.1 Dual Testing Methodology

The ModelChecker uses a **dual testing methodology** to ensure comprehensive validation. Both methods are REQUIRED for all changes:

**Method 1: pytest (Primary Test Runner)**
- **When**: Before every commit, during development
- **Coverage**: All unit tests, integration tests, and theory tests
- **Command**: `PYTHONPATH=code/src pytest code/tests/ -v`

**Method 2: dev_cli.py (Development Workflow)**
- **When**: During feature development, interactive testing
- **Coverage**: Full pipeline testing with real examples
- **Command**: `cd Code && ./dev_cli.py test`

### 4.2 Common Test Commands

```bash
# Run all tests with verbose output
PYTHONPATH=code/src pytest code/tests/ -v

# Run specific theory tests
PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/tests/unit/ -v

# Run with coverage report
PYTHONPATH=code/src pytest --cov=model_checker --cov-report=term-missing --cov-report=html

# Run specific test file
PYTHONPATH=code/src pytest code/tests/unit/test_semantic.py -v

# Run specific test function
PYTHONPATH=code/src pytest code/tests/unit/test_semantic.py::test_conjunction_evaluates_correctly -v

# Run tests matching pattern
PYTHONPATH=code/src pytest -k "test_logos" -v

# Stop on first failure
PYTHONPATH=code/src pytest -x -v

# Show local variables on failure
PYTHONPATH=code/src pytest -l -v
```

### 4.3 Continuous Integration

All tests must pass in CI before merging. CI runs:
1. Full test suite with pytest
2. Coverage analysis (must meet thresholds)
3. Type checking with mypy
4. Linting with flake8

---

## 5. Writing Effective Tests

### 5.1 Test Structure (AAA Pattern)

Follow the **Arrange-Act-Assert** pattern:

```python
def test_feature_handles_edge_case():
    """Test that feature handles edge case correctly."""
    # ARRANGE: Set up test conditions
    test_input = create_edge_case_input()
    expected_output = calculate_expected_result(test_input)

    # ACT: Execute the code under test
    actual_output = feature_under_test(test_input)

    # ASSERT: Verify results
    assert actual_output == expected_output, \
        f"Feature should handle edge case: expected {expected_output}, got {actual_output}"
```

### 5.2 Test Documentation

Every test MUST have a docstring explaining:
- What behavior is being tested
- Why this test exists (especially for bug fixes)
- Expected outcome

```python
def test_loader_rejects_invalid_package_marker():
    """Test that ModuleLoader rejects packages with invalid .modelchecker marker.

    The .modelchecker file must contain 'package=true' to be valid.
    This test ensures we fail fast on invalid package markers rather than
    allowing silent failures or unexpected behavior.

    Expected: ImportError with clear message about invalid marker.
    """
    # Test implementation...
```

### 5.3 Assertion Messages

Always include descriptive assertion messages:

```python
# Good: Clear message explaining what went wrong
assert result.is_valid, \
    f"Formula '{formula}' should be valid in {theory} theory"

# Bad: No message
assert result.is_valid
```

### 5.4 Test Isolation

Each test must be independent:

```python
# Good: Each test creates its own data
def test_feature_A():
    data = create_test_data()
    result = process(data)
    assert result.success

def test_feature_B():
    data = create_test_data()  # Fresh data, not shared
    result = process(data)
    assert result.success

# Bad: Tests share mutable state
shared_data = create_test_data()  # Don't do this

def test_feature_A():
    result = process(shared_data)
    assert result.success

def test_feature_B():
    result = process(shared_data)  # Depends on test_A's side effects
    assert result.success
```

---

## 6. Theory-Specific Testing

### 6.1 Testing Semantic Implementations

Every theory MUST test:
- All operators are correctly implemented
- Operator interactions work as expected
- Edge cases and boundary conditions
- Error handling for invalid formulas

```python
def test_logos_conditional_satisfies_modus_ponens():
    """Test that → operator supports modus ponens inference."""
    semantic = LogosSemantic()

    # Test: (p → q) ∧ p entails q
    premises = ["(p > q)", "p"]
    conclusion = "q"

    result = semantic.check_entailment(premises, conclusion)

    assert result.is_valid, "Modus ponens should be valid in logos"
```

### 6.2 Testing Examples

Every theory should have comprehensive examples covering:
- Valid arguments (should find no countermodel)
- Invalid arguments (should find countermodel)
- All operators in isolation
- Complex operator combinations
- Known logical principles

**Example Test Structure**:
```python
def test_exclusion_veridicality_principle():
    """Test that exclusion validates veridicality principle.

    Principle: ◻p ⊢ p (what is necessary is true)
    Expected: Valid in exclusion theory
    """
    premises = ["[]p"]
    conclusion = "p"

    result = check_validity(premises, conclusion, theory="exclusion")

    assert result.is_valid, "Veridicality should hold in exclusion"
```

### 6.3 Cross-Theory Compatibility

Test that theories can coexist and theory selection works:

```python
def test_theory_selection_loads_correct_semantics():
    """Test that specifying theory loads correct semantic implementation."""
    logos_result = run_model_checker(formula, theory="logos")
    exclusion_result = run_model_checker(formula, theory="exclusion")

    # Different theories may produce different results
    assert logos_result.theory_name == "logos"
    assert exclusion_result.theory_name == "exclusion"
```

---

## 7. Test Coverage Requirements

### 7.1 Coverage Targets

**Minimum Coverage Requirements**:
- **Overall codebase**: ≥85% coverage
- **Critical paths** (semantic evaluation, model iteration): ≥90% coverage
- **Utility functions**: ≥80% coverage
- **Error handling paths**: ≥75% coverage

**Coverage Measurement**:
```bash
# Generate coverage report
PYTHONPATH=code/src pytest --cov=model_checker --cov-report=term-missing --cov-report=html

# View HTML report
# Open htmlcov/index.html in browser
```

### 7.2 What to Cover

**Must be tested**:
- All public API methods
- All semantic operators
- All error conditions
- All configuration options
- All file I/O operations

**Can skip testing**:
- Simple getters/setters with no logic
- Third-party library code
- Generated code (if any)

### 7.3 Coverage Gaps

When coverage is below target:
1. Identify uncovered lines with `--cov-report=term-missing`
2. Write tests for uncovered code
3. If code is truly untestable, refactor to make it testable
4. Document any intentional coverage exclusions

---

## 8. Best Practices and Patterns

### 8.1 Test Naming Conventions

Follow consistent naming:
- `test_<feature>_<condition>_<expected_outcome>()`
- Examples:
  - `test_loader_accepts_valid_package_marker()`
  - `test_semantic_rejects_invalid_formula()`
  - `test_iterator_finds_all_models_within_size_limit()`

### 8.2 Fixtures and Test Utilities

Use pytest fixtures for reusable test setup:

```python
import pytest

@pytest.fixture
def sample_theory():
    """Provide a sample theory instance for testing."""
    return LogosSemantic()

@pytest.fixture
def temp_package_dir(tmp_path):
    """Create a temporary package directory for testing."""
    package_dir = tmp_path / "test_package"
    package_dir.mkdir()
    (package_dir / ".modelchecker").write_text("package=true\n")
    return package_dir

def test_uses_fixtures(sample_theory, temp_package_dir):
    """Test using fixtures for setup."""
    # Test implementation uses sample_theory and temp_package_dir
    pass
```

### 8.3 Testing Error Conditions

Always test that errors are raised appropriately:

```python
def test_semantic_raises_error_on_undefined_operator():
    """Test that using undefined operator raises clear error."""
    semantic = LogosSemantic()

    with pytest.raises(ValueError) as exc_info:
        semantic.evaluate("undefined_operator(p, q)")

    assert "undefined_operator" in str(exc_info.value).lower()
    assert "not supported" in str(exc_info.value).lower()
```

### 8.4 Parametrized Tests

Use parametrization to test multiple cases efficiently:

```python
@pytest.mark.parametrize("formula,expected_valid", [
    ("p > p", True),           # Reflexivity
    ("p > q", False),          # Not tautology
    ("(p & q) > p", True),     # Simplification
    ("p > (p | q)", True),     # Addition
])
def test_logos_validates_propositional_principles(formula, expected_valid):
    """Test various propositional logic principles."""
    result = check_validity([], formula, theory="logos")
    assert result.is_valid == expected_valid, \
        f"Formula '{formula}' validity should be {expected_valid}"
```

### 8.5 Performance Testing

For performance-critical code, include timing assertions:

```python
import time

def test_iteration_completes_within_time_limit():
    """Test that model iteration completes within reasonable time."""
    start = time.time()

    result = iterate_models(formula, max_size=10)

    duration = time.time() - start
    assert duration < 5.0, f"Iteration took {duration}s, should complete in <5s"
```

#### Repeated-Operation Timing: Discard Cold Starts, Avoid Unbounded Ratios

A single-shot absolute-budget assertion like the one above is fine. A *repeated*-operation
assertion needs a different shape, because a naive one degrades as the code under test gets
faster rather than staying reliable.

**Anti-pattern (observed failing in this repository).**
`code/src/model_checker/builder/tests/e2e/test_project_edge_cases.py`'s
`TestPerformanceAndScalabilityScenarios::test_repeated_project_operations_maintain_consistent_performance`
used to time five repeated `BuildProject.generate()` calls and assert
`max_time / min_time < 5.0`:

```python
# Anti-pattern: an unbounded max/min ratio over repeated real filesystem work.
operation_times = []
for iteration in range(5):
    start_time = time.time()
    project_generator.generate(f'{project_name}_{iteration}')
    operation_times.append(time.time() - start_time)

ratio = max(operation_times) / min(operation_times)
assert ratio < 5.0  # Failed at ratio 17.4
```

This failed at a measured ratio of **17.4 against the 5.0 bound**, while a companion absolute
bound on the same run (`max(operation_times) < 10.0`) passed comfortably. The operation
(`BuildProject.generate()`) is pure filesystem work with no solver involved, and the first
("cold") iteration pays one-time costs -- cold Python import caches, cold OS filesystem caches --
that later iterations do not. A ratio assertion over a series that includes that cold iteration
has no floor on `min_time`, so as the *warm* iterations get faster (the code improving), the
ratio *grows*: the assertion degrades exactly when the implementation gets better, which is
backwards for a regression guard.

**Correct pattern: discard the cold iteration, then bound the warm ones absolutely.** Run one
throwaway warm-up iteration before the measured loop, then assert every warm iteration against a
fixed absolute ceiling, plus `max(warm_times) < median(warm_times) + FIXED_SLACK_SECONDS` (a
fixed slack, never a ratio) to catch a single outlier without punishing overall improvement:

```python
# Correct pattern: one discarded warm-up, then absolute + median-plus-slack bounds.
warm_up_generator = BuildProject('bimodal')
warm_up_generator.generate(f'{project_name}_warmup')  # discarded, not measured

operation_times = []
for iteration in range(5):
    start_time = time.time()
    project_generator.generate(f'{project_name}_{iteration}')
    operation_times.append(time.time() - start_time)

assert_warm_iterations_consistent(self, operation_times)  # absolute ceiling + median + slack
```

See `assert_warm_iterations_consistent()` and the module-level `WARM_ITERATION_*` constants in
`test_project_edge_cases.py` for the concrete bounds. This test now also carries
`@pytest.mark.xdist_serial` (see 8.12 below) -- the redesigned assertion has adequate headroom
under normal conditions, but CPU contention under the shared `-n 6` worker pool can still push a
tight repeated-operation timing assertion past budget, independent of the ratio-vs-absolute
question this subsection addresses.

### 8.6 Solver Timing Budgets and Machine Variance

Z3 solve times for the *same* formula vary widely between runs on the same machine. Measured on a
single unchanged test exercising one bimodal countermodel, the reported call time across repeated
invocations was 0.69s, 1.37s, 1.85s, 1.98s, and 15.08s — roughly a 20x spread with no change to
the code under test. The variance tracks machine load, not test order.

**Why this matters more than ordinary slowness**: when a solve exceeds `max_time`, Z3 returns
UNKNOWN, which `models/structure.py`'s `solve()`/`re_solve()` already classify as
`is_timeout=True`, populating `ModelStructure.timeout`. A test whose `max_time` sits near its
typical solve time therefore risks reading an inconclusive run as if it were a genuine "no
countermodel exists" outcome under load, unless the caller actually reads the timeout signal.

**Fixed: the timeout signal is now surfaced everywhere a result is read, not just inside
`ModelStructure`.** `BuildExample.get_result()` and `BuildExample._get_model_structure_data()`
(and the equivalent module-level helper and `run_enhanced_test()` in `utils/testing.py`) always
carry a `"timeout"` key alongside `"model_found"`, populated from `ModelStructure.timeout` and
readable independently of it -- `model_found=False, timeout=True` and
`model_found=False, timeout=False` are now distinguishable, where before both collapsed to the
same `model_found=False`. `TestResultData.check_result` and both `BuildExample.check_result()`
(in `builder/example.py`) and `ModelDefaults.check_result()` (in `models/structure.py`) return
one of three values -- `"match"`, `"mismatch"`, or `"inconclusive"` -- checking `timeout` before
the expectation comparison, so a timed-out solve is reported as `"inconclusive"` rather than
silently folded into `"mismatch"`. See
`code/src/model_checker/builder/tests/unit/test_example.py`'s `TestTimeoutSurfacing` and
`TestThreeWayCheckResult` classes for the pinning tests, and
`code/src/model_checker/models/tests/unit/test_structure.py::test_check_result` for the
`ModelDefaults` side.

**A deterministic complement to `max_time`: the `max_rlimit` setting.** `max_time` is a
wall-clock budget in milliseconds, so it inherits the machine-load variance this section
documents -- the same formula can time out on a busy machine and not on an idle one.
`ExampleSettings` (`code/src/model_checker/settings/types.py`) also accepts an optional
`max_rlimit: int`: a Z3 resource-unit budget, set via `Z3SolverAdapter.set_rlimit()`
(`code/src/model_checker/solver/z3_adapter.py`), that counts Z3's internal resource units rather
than wall-clock time, so the same constraint set exhausts the same budget regardless of host CPU
load. It is optional and default-off: `ModelDefaults.solve()`/`re_solve()`
(`code/src/model_checker/models/structure.py`) only call `set_rlimit()` when
`settings.get("max_rlimit")` is truthy, immediately after the existing `set_timeout()` call, so
no existing example's behavior changes unless it opts in. An `rlimit`-exhausted UNKNOWN is
classified identically to a wall-clock timeout (`is_timeout=True`) -- the existing UNKNOWN-as-
timeout branch already covers it without narrowing, pinned by a dedicated test in
`models/tests/unit/test_structure.py`. Prefer `max_rlimit` alongside `max_time` (not instead of
it) for a test whose flakiness is specifically load-driven rather than a genuine near-budget
solve.

**Set budgets generously, not tightly.** Do not derive `max_time` from a measured solve time plus a
small margin. An observed ~1.7s solve was given a 10s budget — an ~6x margin — and still failed at
10.11s call time inside a full-suite run. Prefer the 30s convention used by the sibling bimodal
examples:

```python
# Good: headroom well beyond the observed solve time, so load spikes cannot
# turn a timeout into a false "no countermodel" result.
SIMPLE_EXAMPLE = [premises, conclusions, {'N': 2, 'max_time': 30}]

# Bad: omitting max_time inherits the theory's DEFAULT_EXAMPLE_SETTINGS value
# (1s for BimodalSemantics), which is below the actual solve time for many
# non-trivial formulas.
SIMPLE_EXAMPLE = [premises, conclusions, {'N': 2}]
```

**Suspect the budget before suspecting state leakage.** When a test's outcome changes depending on
how it is invoked, the timeout budget is the more likely cause. Solver isolation is already
deliberate and verified: `models/structure.py` builds a fresh solver context per solve
(documented there as ensuring "deterministic behavior regardless of which examples were run
previously"), `settings/settings.py` copies default dicts before merging rather than mutating
shared state, and there is no memoization in the settings or model layers. Confirm the budget
first; only then look for shared state.

**Wall-clock assertions are load-sensitive.** The timing assertions shown in 8.5 above inherit this
same variance: repeat full sweeps of the suite have differed from each other by several failures
with no intervening code change. Give such assertions generous tolerances, and mark them
`@pytest.mark.xdist_serial` (see 8.12 below) so they run outside the contended `-n` worker pool,
or `@pytest.mark.performance` if the budget itself is too tight for any shared CI runner
(8.12's taxonomy table draws that line precisely) -- either way, a default gating run should have
no unmarked wall-clock assertion left in it. `code/tests/ci/test_timing_marker_coverage.py`
enforces this with an AST scan: see 8.12 below.

**Concurrent test sessions contend.** Two test runs in the same sandbox measurably affect each
other's timing-sensitive outcomes, and a long suite can be killed outright by resource pressure
from a competing run. Before launching a long or timing-sensitive suite, check for competing
processes (`ps aux | grep pytest`), and prefer `pytest -n <N>` to shorten the window during which
a collision can occur.

### 8.7 Regression Testing

For bug fixes, always add regression tests:

```python
def test_regression_issue_73_package_loading():
    """Test that package loading works after Issue #73 fix.

    Issue #73: Package loading failed when .modelchecker missing 'package=true'
    Fix: Added validation and clear error message

    This test ensures the fix remains effective.
    """
    # Test implementation that would have failed before fix
    package_dir = create_package_without_marker()

    with pytest.raises(ImportError) as exc_info:
        load_package(package_dir)

    assert "package=true" in str(exc_info.value).lower()
```

### 8.8 Oracle Suite: Gating vs. Exhaustive Split

`oracle/` (the standalone bimodal-logic differential-oracle tree) is split into two entry points
so that routine, gating test runs stay fast while a full self-consistency sweep remains available
on demand.

**The `not slow` gating default, and why `oracle/` must spell it out.** `oracle/run-oracle-suite.sh`
runs two pytest passes, and both deselect the `slow` marker explicitly (and, since this tree's
first `unstable` marking, `unstable` as well — see 8.9 below):
`-m "not xdist_serial and not slow and not unstable"` /
`-m "xdist_serial and not slow and not unstable"`. Unlike `code/`, which has
`code/pyproject.toml` as a reachable ini file, `oracle/` (and the repo root above it) has no ini
file for pytest to read a default `-m` expression from — `oracle/conftest.py`'s own module
docstring explains why marks are registered there instead of in an ini file. Without an explicit
deselect on every invocation, nothing filters out the slow-marked tests, and a full run silently
becomes the exhaustive sweep described below.

**The exhaustive path.** `oracle/run-oracle-exhaustive-scan.sh` drives
`pytest oracle -m slow -s` (serial, not parallel, so streamed output is not buffered by xdist and
solve times are not contention-inflated) to run the full complexity<=5 primitive-formula
self-consistency scan — 274 formulas x 2 solves each. This is never part of the gating path; it is
invoked explicitly, typically to re-derive the known-conclusive baseline (below) after a change to
the formula enumerator or the solve budget. Budget it at roughly 60-90 minutes of wall clock at the
deployed `SELF_SCAN_SOLVE_TIMEOUT_MS` (see
`oracle/bimodal_logic/tests/test_cross_oracle_differential.py`); a real derivation run measured
3640.955s (~60.7 minutes).

**The known-conclusive-population strategy.** Re-solving all 274 formulas on every gating run is
redundant: roughly 60-65% of them are known in advance to be inconclusive (the solver does not
decide within budget) and re-discovering the same timeouts every run buys nothing. Instead, the
gating suite asserts the soundness property only over the *known-conclusive* subset, persisted in
`oracle/bimodal_logic/tests/data/known_conclusive_complexity5.json`. Each manifest entry records
both the formula's `index` in the enumerator's output and its canonical `formula_json` — never the
index alone, since a bare index would silently misalign if the enumerator ever changed. Before
solving anything, the gating test (`TestGatingConclusiveScan` in `test_cross_oracle_differential.py`)
re-enumerates the population and cross-checks every manifest entry against it; a mismatch fails
loudly with an explicit "re-derive the baseline" message rather than proceeding on stale data.
**A change to the formula enumerator or the solve budget requires regenerating this manifest** via
a fresh `oracle/run-oracle-exhaustive-scan.sh` run — there is no other sanctioned way to update it.

**The two-budget contract (derivation vs. gating re-check).** The manifest is *derived* at
`SELF_SCAN_SOLVE_TIMEOUT_MS` (10000 ms — the exhaustive scan, `scan_runner.py`'s default, and
every re-derivation keep this budget), but the gating re-check re-solves the manifest population
at the separate, wider `GATING_RECHECK_SOLVE_TIMEOUT_MS` (40000 ms as of 2026-08-12, widened from
the original 20000 ms after a real CI conclusive-population shortfall — see that constant's own
comment in `test_cross_oracle_differential.py` for the full measurement-backed justification; both
constants live in that same file). The two are deliberately decoupled: the slowest manifest
member entered the manifest at 10.094 s against the 10000 ms derivation budget, so re-checking at
the derivation budget ran at ~1.0x headroom by construction. Decoupling is sound because
conclusiveness is monotone in budget — every derivation-time member remains legitimately
conclusive at a wider re-check budget, so no manifest re-derivation is triggered, the gating floor
is untouched, and `disagreements == 0` is asserted over *more* decided results. The recorded
trade-off: per-formula solve-cost regressions from <10 s into the 10 s-to-re-check-budget band no
longer trip the gating floor; that regression detection lives in the scheduled exhaustive scan,
which keeps the 10000 ms budget and its manifest-freshness check. Only a manifest re-derivation
changes what "known-conclusive" means; the re-check budget only changes how much headroom the
gating pass has while verifying it.

**The JSON-artifact and completion-marker contract.** Both the exhaustive test and the standalone
`oracle/scan_runner.py` CLI call the same shared scan core
(`_generate_differential_report()` in `test_cross_oracle_differential.py`), so there is only ever
one enumerate-solve-compare loop to keep correct. When given an output directory, that core writes,
per run: `progress.jsonl` (one flushed JSON record per formula, so an in-flight run is readable
mid-run — heartbeat and "loud" lines print to stdout on the same cadence), `report.json` (the full
differential report, written and closed first), and finally a `SCAN_COMPLETE` marker (written via
write-to-temp-then-`os.replace`, so it is atomic and never observably half-written). **The marker's
existence — never process or PID liveness — is the only sanctioned signal that a scan run reached
completion.** A vanished PID is not a verdict: a process can exit for many reasons (killed,
crashed, `timeout`-terminated) without ever writing a marker, and inferring completion from PID
absence produced a false completion report before this split existed. Runners poll for the marker
file, not for whether a process is still running.

**Per-pass timeouts and exit-124 semantics.** Both `run-oracle-suite.sh` passes, and the exhaustive
scan, are wrapped in `timeout --kill-after=60s BUDGET`. A pass that exceeds its budget is reported
as `TIMED OUT (exit 124)` (or `137` if `--kill-after`'s SIGKILL was needed after SIGTERM), reported
distinctly from `FAILED (exit N)` in each script's summary — so a stall is never mistaken for a
passing or a merely-failing run. Budgets are overridable via `ORACLE_PASS1_TIMEOUT` /
`ORACLE_PASS2_TIMEOUT` (gating) and `ORACLE_EXHAUSTIVE_TIMEOUT` (exhaustive), defaulting to roughly
2x the real measured wall clock of each pass on an idle machine. `--kill-after=60s` matters
specifically for the parallel `-n 6` pass: a bare SIGTERM to the `timeout`-wrapped pytest parent
does not reliably terminate its xdist worker subprocesses, and a deliberately-triggered timeout
was verified (via `ps aux | grep pytest` immediately afterward) to leave no orphaned workers once
`--kill-after`'s SIGKILL follows.

**The hard constraint.** Speed in this split comes only from running less redundant work, never
from weakening assertions. The soundness tooth (`disagreements == 0` among conclusive results) and
the conclusiveness-floor tooth (a `min_conclusive` performance floor, catching a starved budget
before it can vacuously "pass" by making everything inconclusive) are both non-negotiable — the
gating variant asserts them over a different, smaller *population* than the exhaustive variant, but
never with different, weaker *logic*. A conclusiveness-floor miss is a budget/performance signal to
investigate (see 8.6 above on machine-load variance and concurrent-session contention — this same
class of issue applies here), never a license to lower the floor to force a green run.

**Exhaustive-scan cadence decision: scheduled off-hours, never gating.** The exhaustive scan stays
out of the gating path — at roughly 60 minutes it is incompatible with per-commit or per-PR gating,
which is exactly why the known-conclusive-population split above exists. The recorded decision is
to run it on a **low-frequency schedule, off-hours, unattended** (weekly, or on merge-to-main),
invoking `oracle/run-oracle-exhaustive-scan.sh` **unmodified** — no assertion change, no widened
budget, no lowered conclusiveness floor. The evidence behind this cadence: two independent,
code-current, `SCAN_COMPLETE`-marker-verified runs agree on the property that matters
(`disagreements: 0` both times), at 3651.243s and 3555.065s wall clock and 103 and 105 of 274
formulas conclusive respectively. The 2-formula conclusive-count swing between the two runs is the
near-budget-headroom contention sensitivity already documented in 8.6 above, not a regression —
some formulas sit close enough to `SELF_SCAN_SOLVE_TIMEOUT_MS` that ambient machine load flips a
handful between "decided" and "timed out" without changing whether the decided ones agree.
A cadence decision never licenses an assertion change: the hard-constraint paragraph above is
unaffected by this subsection.

A scheduled scan that silently bit-rots (a dead cron entry, a CI trigger that stops firing, an
operator who forgot) is the same invisible-failure-mode class this task exists to fix at the
per-test level — so the schedule must be paired with an explicit staleness check rather than
run-and-forget. `oracle/check-scan-freshness.sh` is that check: it reports the newest
`oracle/scan-results/*/SCAN_COMPLETE` marker's age and the run's own recorded `disagreements` /
`conclusive` / `wall_clock_seconds`, and exits non-zero when the newest marker is older than a
cadence window (default 7 days, overridable via `ORACLE_SCAN_MAX_AGE_DAYS`) or when no marker
exists at all — marker existence, never PID or process liveness, matching the completion-marker
contract already established above. Wiring an actual schedule into CI (a cron-triggered workflow
that invokes the exhaustive scan and this freshness check) is deliberately not done as part of
recording this decision — it needs its own runner-capacity evaluation and is tracked as a scoped
follow-up.

**Timeout-skip inventory: surfacing what a gating run already knows but does not report.** Both
`run-oracle-suite.sh` passes now pass `-rs` to pytest, so every skip's reason string appears in the
terminal output — previously the gating suite ran the two timeout-conditional `pytest.skip()` sites
in `oracle/bimodal_logic/tests/test_oracle_interface.py` (`TestOracleExampleRegressionViaAPI
::test_oracle_regression` and `TestEnrichedRoundTrip::test_enriched_vs_primitive_sat_agreement`)
without ever printing why a formula skipped. `oracle/conftest.py` additionally collects every
timeout-caused skip during the session (matched on the stable shared substring `did not decide
within`, present in both skip messages) and prints a delimited `== ORACLE TIMEOUT-SKIP INVENTORY
==` section at the end of each pass, classifying every timeout skip as:

- **`[KNOWN]`** — skipped, and recognized in `oracle/conftest.py`'s `_KNOWN_TIMEOUT_SKIPS` mapping,
  with a short adjudication note (e.g. "label corrected to SAT from the ground-truth evaluator; the
  solver still does not decide it at 2x budget").
- **`[NEW]`** — skipped, but not recognized — the actionable drift signal. Adjudicate the formula's
  `expected_sat` against `bimodal_logic/ground_truth.py` before assuming the existing label is
  right; do not assume tooling error.
- **`[RESOLVED]`** — recognized in `_KNOWN_TIMEOUT_SKIPS`, ran in this session (present in the
  session's *seen* set, derived from `pytest_runtest_logreport` so it behaves identically under
  `-n 6` and serial), and is *not* skipped this time — the formula now decides. Go re-check its
  label and its `REGRESSION_TIMEOUT_EXAMPLES` membership; a known entry absent from the current
  session's seen set is not reported at all, so a two-pass run never mistakes one pass's skip
  inventory for the other pass's business.

A skip is always a budget/performance outcome, never a semantic regression, and this inventory is
reporting-only: it adds no marker, never touches `session.exitstatus`, and never converts a skip
into a failure. Never widen a solve budget to clear a `[NEW]` or `[RESOLVED]` entry off this list —
see 8.6 above and the hard constraint two subsections up.

### 8.9 The `unstable` Marker

**What the marker means.** Registered verbatim in `code/pyproject.toml` (and mirrored in
`oracle/conftest.py`'s `pytest_configure`, since `oracle/` sits outside `code/pyproject.toml`'s
ini-discovery reach — see that file's module docstring): "Tests with a documented, investigated
non-semantic instability (e.g. a heavy-tailed solver draw). Deselected from release-gating runs
with `-m "not unstable"`; run on their own by the unstable-watch workflow so they stay observed
rather than forgotten." `unstable` is the pressure-release valve for genuine residue *after*
repair is attempted — see 8.6's timing-budget discipline and 8.8's gating-floor discipline for the
two mechanisms this category exists to route around when they run out.

**Entry criteria.** All four are mandatory and must be recorded explicitly, as separately
identifiable items, in a comment at the marker's source site — not merely implied:

1. **What fails and why** — the specific failure mechanism (e.g. a heavy-tailed Z3 solve
   distribution near a budget), with concrete measurements, not a vague "sometimes flaky".
2. **Demonstrably non-semantic** — the assertion holds on every decided/complete run; the failure
   mode is a budget overrun or resource exhaustion, never a changed logical conclusion.
3. **A genuine fix was attempted and its failure recorded** — cite the specific avenues tried
   (encoding changes, budget recalibrations, alternative algorithms) and what each measurement
   showed, so a future reader starts from the frontier instead of re-trying a closed avenue.
4. **A written, concrete exit criterion** — see below.

**"It failed once in CI" never qualifies on its own** — that is exactly the ordinary machine-load
variance 8.6 describes, and the correct first response is checking the budget, not reaching for
this marker. `unstable` is for instability that survives a genuine repair attempt, not a shortcut
around one. The category must not become a dumping ground: every marking costs this policy's
credibility, so mark sparingly and keep the entry-criteria record honest.

**Exit criteria and the promotion path.** The general rule: a written, per-test exit criterion is
mandatory at the marker site, stated concretely enough that "has this been met?" has a yes/no
answer. The concrete default, absent a test-specific reason to differ: **20 consecutive
`unstable-watch` runs recording zero failures (nightly cadence, so roughly 3 weeks), OR a genuine
encoding/algorithmic fix demonstrated to collapse the instability across a statistically
meaningful sweep (e.g. >= 20 seeds) with no residual failure at the documented budget.** When an
exit criterion is met, promotion is mechanical: remove `@pytest.mark.unstable` (or the
`UNSTABLE_EXAMPLES`-style membership that applies it) from the test, remove it from any
workflow-level exclusion accounting that names it directly, and record the promotion — with the
date and the evidence that justified it — in the settings/marker comment rather than deleting that
comment's history. The history of what was tried and what finally worked is worth more than a
clean diff.

**Review cadence.** The `unstable` set is reviewed monthly (a human check that every marked test
still has a live justification and an unmet exit criterion). `unstable-watch.yml` itself runs
nightly and surfaces `READY TO PROMOTE` automatically the moment the 20-run streak is reached —
the monthly review is a backstop for cases the automated streak does not catch (e.g. a test that
should be promoted for a different reason, such as a landed encoding fix).

**The standing rule.** An indefinitely-quarantined test is itself a defect to escalate, not a
steady state that the marker lets a codebase settle into. A test still marked `unstable` after two
review cycles (roughly two months) with no promotion and no active repair work in progress must
get a task opened against it — continuing to sit in the `unstable` category with neither progress
nor an active investigation is the failure mode this rule exists to catch.

**Where the deselection is wired.** `.github/workflows/tests.yml`'s main suite invocation,
`.github/workflows/differential-tests.yml`'s first invocation, `flake.nix`'s `checks.default`
(the same suite under the nixpkgs-native Z3 toolchain), and `oracle/run-oracle-suite.sh`'s two
passes (parallel and serial) all carry `and not unstable` in their `-m` expression.
`oracle/run-oracle-suite.sh` entered scope only once the oracle tree carried its first `unstable`
marking (see "Currently marked" below) — `.github/workflows/tests.yml`'s and `flake.nix`'s
`code/`-tree invocations never reach `oracle/`, so this script needed its own, separate filter.
`.github/workflows/release.yml`'s `test-and-release` job runs no pytest suite at all — a
documented no-op comment there states that any pytest suite added to that job in the future MUST
carry `not unstable`; the `build` job's packaging-contract invocation already carries a defensive
`and not unstable` even though no packaging test is or should ever be `unstable`-marked. A future
author adding a new gating pytest invocation anywhere in this repository should include the same
filter as a matter of course, not rediscover the need for it —
`code/tests/ci/test_unstable_deselection_wiring.py` enforces this contract executably across
`tests.yml`, `flake.nix`, `differential-tests.yml`, and `run-oracle-suite.sh`.

**The classifier lives in an importable module, not YAML.** `unstable-watch.yml`'s classify step
invokes `.github/scripts/unstable_watch_classify.py`, unit-tested by
`code/tests/ci/test_unstable_watch_classifier.py`. Adding a third `unstable` marking means
extending that module (a new signature branch in `classify()`, following the pattern the
`GATING_FLOOR_NODEID_FRAGMENT`/`GATING_FLOOR_SIGNATURE` constants establish, plus tests) — not
editing workflow YAML.

**Promotion-streak limitation.** `unstable-watch.yml`'s step-summary streak counter's historical
component (prior runs, via `gh run list` job conclusions) is `NEW`-sensitive only: a run whose
marked test failed `TIMING`-style still exits 0, so that run's job conclusion reads as success.
This run's own contribution to the streak is honesty-corrected (`compute_promotion_streak` zeroes
it on ANY failure, `TIMING` or `NEW`), but the historical component cannot be retroactively
corrected without downloading and re-parsing every prior run's `unstable-watch-record.jsonl`
artifact — out of scope for the mechanism as it stands. The reported streak is therefore an
UPPER BOUND on the true zero-failure streak. Evaluating a per-test exit criterion (above) for a
test expected to fail `TIMING`-style with any regularity requires checking the uploaded per-run
`unstable-watch-record.jsonl` artifacts directly, not just the step-summary number.

**Currently marked.**
- `test_example_cases[BM_CM_1-example_case7]` in
  `code/src/model_checker/theory_lib/bimodal/tests/unit/test_bimodal.py` — see that file's
  `UNSTABLE_EXAMPLES` entry-criteria comment block for the full record (a heavy-tailed solve on
  the Future/all_future quantifier family; three closed encoding avenues; the written
  20-run-or-verified-fix exit criterion).
- `TestGatingConclusiveScan::test_known_conclusive_population_self_consistent` in
  `oracle/bimodal_logic/tests/test_cross_oracle_differential.py` — see that file's
  `GATING_RECHECK_SOLVE_TIMEOUT_MS` comment block for the full record (a CI-verified
  conclusive-population shortfall on the performance floor only, never on the disagreements
  soundness check; the closed `xdist_serial` isolation lead; the CI-verified 2x budget widening
  that bought zero additional conclusive formulas; the written 20-run-or-verified-fix exit
  criterion).

Neither record is duplicated here; each marker's own source-site comment block is the source of
truth.

### 8.10 Optional, Developer-Local External Test Dependencies

Some test files in `oracle/bimodal_logic/tests/` reference `bimodal_harness`, a separate,
developer-local package (not part of this repository, not declared in `code/pyproject.toml`,
never installed by any CI workflow). Any test file that touches such a package MUST NOT import it
at module scope unconditionally: pytest must successfully import a module before it can inspect
that module's markers, so an unguarded top-level import crashes *collection* -- before marker-based
deselection (e.g. `-m unstable`) ever gets a chance to run -- on every machine and every CI runner
where the optional package is not installed.

**Required pattern.** `oracle/bimodal_logic/tests/_bimodal_harness.py` is the shared guard module
for this dependency: it exposes `BH_AVAILABLE` (a module-level bool set by attempting the import
inside a `try/except ImportError`) and `BH_SKIP_REASON` (a shared skip message). Any test file
needing symbols from the optional package must:

1. Import `BH_AVAILABLE` and `BH_SKIP_REASON` from `_bimodal_harness` -- never import the optional
   package itself at module scope.
2. Resolve the optional package's symbols conditionally (`if BH_AVAILABLE: import ...` else bind
   to `None`), so the names still exist for a skipped test's body.
3. Gate only the specific tests that need those symbols with
   `@pytest.mark.skipif(not BH_AVAILABLE, reason=BH_SKIP_REASON)`, at test granularity -- never at
   class or module granularity, so tests that do not depend on the optional package keep running
   and keep providing coverage.
4. When stacking `skipif` above an existing `xfail(strict=True)` mark, note that `skipif` is
   evaluated first: the test reports as `SKIPPED`, not `XFAIL`, when the optional dependency is
   unavailable.

**Verifying a fix for this class of defect.** A plain local run is not sufficient evidence that a
guard actually works, because an accidental `sys.path` mutation performed by an alphabetically
earlier file in the same collected directory can silently make the optional package importable for
a later file too, masking exactly the failure mode this pattern exists to prevent. Verification
must instead run in a subprocess with an explicit `sys.meta_path` finder that raises `ImportError`
for the optional package's name (and any of its submodules), faithfully simulating a CI runner
where the package genuinely does not exist. See `test_bimodal_harness_guard.py` for the reference
implementation of this blocker harness and its two portability regression tests.

### 8.11 CI Timeout Guard: `--timeout` and `--timeout-method=thread`

**Motivating incident.** CI run `32897405646`'s Python 3.12 job reached 94% progress, produced
zero output for 17 minutes, and was killed by `general-tests`' job-level `timeout-minutes: 20`
backstop -- the cleanup log showed only orphaned `pytest` and worker processes, with no
indication of which test had hung. A job-level timeout is a backstop, not a diagnostic: it ends
the job, but names nothing.

**The fix: a per-test `pytest-timeout` guard on both gating pytest invocations.**
`.github/workflows/tests.yml`'s `general-tests` job and `flake.nix`'s `checks.default`
`checkPhase` (the same suite under, respectively, the PyPI `z3-solver` wheel and the
nixpkgs-native Z3/Python toolchain) both pass `--timeout=300 --timeout-method=thread` on every
pytest invocation. `pytest-timeout` was already an installed dependency in both toolchains before
this addition (`code/pyproject.toml`'s `dev` extra, and `flake.nix`'s `devPython` package list);
what was missing was passing the flag at all.

**Why `--timeout-method=thread`, not the `signal` default.** `pytest-timeout`'s default `signal`
method delivers `SIGALRM`, which the Python interpreter can only act on between bytecode
instructions -- it cannot interrupt or diagnose a hang blocked inside a C extension call such as
a stuck Z3 solve, which is exactly the failure mode the motivating incident exhibits. The
`thread` method instead runs a watcher thread that, on timeout, dumps every thread's stack via
`faulthandler` regardless of where execution is blocked, naming the hung test and showing exactly
where it is stuck.

**Why 300 seconds.** It sits far below `general-tests`' `timeout-minutes: 20` (1200s) job-level
backstop, so the per-test timeout fires first and actually produces the diagnostic, and it
comfortably exceeds the slowest single test measured locally under the same `-n 6` gating
selection (82.34s,
`theory_lib/bimodal/tests/integration/test_iterate.py::TestBimodalIteratorReal::test_iterate_two_produces_distinct_models`)
-- better than 3x headroom. If a future test's genuine runtime approaches this budget, raise the
value in both files in a single commit; never remove the flag, and never raise
`timeout-minutes` instead.

**Prior in-repo precedent for this invocation shape.**
`specs/archive/129_triage_preexisting_test_failure_backlog/plans/01_verify-fixes-baseline-doc.md`
used `--timeout=180 --timeout-method=thread` (and `--timeout=300 --timeout-method=thread`) for a
comparable verification sweep before this convention was adopted for the two gating CI
invocations themselves.

**Kept in sync by an executable guard, not a comment.**
`code/tests/ci/test_workflow_parity.py` regex-extracts both files' pytest invocation lines and
asserts the `--timeout` value, `--timeout-method`, `-n` worker count, and both marker expressions
(parallel-pass and serial-pass, see 8.12 below) are textually identical between them, plus that
every marker token either invocation names is registered in `code/pyproject.toml`'s `markers`
list. A future edit that changes one file without the other, or introduces an unregistered
marker typo, fails this guard rather than silently drifting.

### 8.12 The `xdist_serial` Marker

**What the marker means.** Registered in `code/pyproject.toml` (and mirrored in
`oracle/conftest.py`'s identically-named marker for the oracle suite's own parallel/serial
split): "Tests with a real wall-clock timing assertion that has adequate headroom under normal
conditions, but which CPU contention under pytest-xdist's `-n` worker pool can push past budget.
Deselected from the parallel `-n` pass; run in a serial second CI pass with no `-n` flag
instead." Unlike 8.9's `unstable` marker, `xdist_serial` is not a quarantine for a residual,
investigated defect -- it is a routine, structural classification for any real wall-clock
assertion that belongs in the gating suite but should not compete with five other workers for
CPU while its clock is running.

**Two-marker taxonomy (`performance` vs. `xdist_serial`).** Both markers cover a wall-clock
assertion; which one applies is a budget-size question, not a severity question:

| Marker | Meaning | CI treatment |
|---|---|---|
| `performance` | Budget too tight for any shared CI runner (sub-10ms class) | Deselected from both the parallel and serial passes entirely |
| `xdist_serial` | Real wall-clock assertion with adequate headroom, but which shared-runner contention can push past budget | Deselected from the `-n` pass; run in the serial second pass |

Folding every wall-clock-asserting test under `performance` alone is wrong: `performance` is
deselected outright by both gating CI invocations, so it silently deletes coverage rather than
relocating it. Use `xdist_serial` for anything that should keep gating but cannot tolerate
`-n`-pool contention; reserve `performance` for the genuinely too-tight sub-10ms class (currently
`test_refactoring_target_behavior.py::test_performance_improvement` and
`code/tests/integration/test_performance.py::test_complex_model_performance`, the latter carrying
`@pytest.mark.timeout(30)` as a hang guard alongside `performance`, not as a substitute for it).

**Where the deselection and the serial pass are wired.** `.github/workflows/tests.yml`'s
`general-tests` step and `flake.nix`'s `checks.default` `checkPhase` each run two pytest
invocations: a parallel pass with `and not xdist_serial` added to its `-m` expression and `-n 6`,
followed immediately by a serial pass with `-m "xdist_serial and not packaging and not
unstable"` and no `-n` flag at all -- mirroring `oracle/run-oracle-suite.sh`'s existing
parallel/serial two-pass structure for the oracle suite. Both passes carry the identical
`--timeout=300 --timeout-method=thread` guard from 8.11 above.
`code/tests/ci/test_workflow_parity.py` enforces that both files' parallel- and serial-pass
marker expressions stay textually identical.

**Currently marked.** Nine tests across six files, each carrying a one-line
contention-sensitivity comment at the marker site:
`builder/tests/e2e/test_project_edge_cases.py`'s `TestPerformanceAndScalabilityScenarios` class
(both methods -- see 8.5's repeated-operation subsection above for the redesigned assertion this
class uses),
`builder/tests/integration/test_performance.py::test_module_loading_performance` and
`::test_serialization_performance`,
`builder/tests/unit/test_project_version.py::test_version_detection_performance_is_reasonable`,
`builder/tests/unit/test_serialize.py::test_serialize_semantic_theory_handles_large_operator_collections`,
`builder/tests/unit/test_progress_bar_ordering.py::test_freeze_complete_time_consistency`, and
`code/tests/integration/test_timeout_resources.py::test_z3_solver_timeout` and
`::test_cli_command_timeout`.

**Kept complete by an executable AST guard, not a one-time grep.**
`code/tests/ci/test_timing_marker_coverage.py` walks every test file under
`code/src/model_checker/**/tests/**` and `code/tests/**`, and flags any `test_*` function that
both reads a real clock (`time.time`, `time.perf_counter`, or `time.monotonic`, checked in the
function's own body or in a same-module helper function it calls) and asserts a bound comparison
on the derived value, but carries neither `performance` nor `xdist_serial` (checked at the
function, its enclosing class, or a module-level `pytestmark`). It carries an explicit,
commented `MOCKED_CLOCK_ALLOWLIST` for a future test that patches the clock rather than reading
real wall-clock time, so a mocked-time assertion is never forced to carry either marker.

### 8.13 The Example Solve-Budget Floor

**The class 8.12's guard cannot see.** `test_timing_marker_coverage.py` scans for the *explicit*
wall-clock shape -- a test that reads `time.time()` and asserts a bound on the delta. The larger
class is *implicit*: an example whose `max_time` setting is itself the clock. When such a budget
sits near the example's typical solve time, ordinary CPU contention turns into a test failure --
Z3 returns UNKNOWN, `ModelDefaults.check_result()` reports `"inconclusive"`, and
`utils.testing.run_test()` maps that to `False`, which the theory-level example tests assert on.
The resulting message ("Model result did not match expectation value in settings") reads as a
semantic regression while being purely a budget artifact. No marker applies and no AST scan for
clock reads will ever flag it.

**The motivating incident.** `CL_TH_12` and `CL_TH_13` in
`theory_lib/logos/subtheories/constitutive/examples.py` were set to `'max_time': 1` against
measured solve times of 0.267s and 0.350s -- ~3x headroom on a 12-core development host, but
under 1x on a 4-vCPU `ubuntu-latest` runner sharing six xdist workers. Both failed on all three
Python versions and under `nix flake check` on the v1.3.5 release pushes. The same mechanism had
already fired on different victims in earlier runs
(`test_iterate_example_generator_yields_models`, `test_iteration_via_iterate_api`), which is what
identifies it as a class rather than two bad constants.

**Note that a local reproduction is not available for this class.** Restricting the development
host with `taskset -c 0-3` and running the full gating selection at `-n 6` passes cleanly
(2292 passed) -- core-count restriction does not reproduce a per-core clock/IPC gap or a
virtualized neighbour. The oracle suite's own budget work reached the identical conclusion
independently (103/103 conclusive both with and without `taskset -c 0,1`, against 96/103 on real
CI). Because the failure cannot be reproduced locally, a budget must carry enough margin that the
question never arises -- which is precisely 8.6's "set budgets generously, not tightly", restated
as an executable floor.

**The floor.** `code/tests/ci/test_example_budget_floor.py` AST-scans the four
`logos/subtheories/*/examples.py` files and fails on any settings dict whose `max_time` is below
10 seconds, or whose `max_time` is not an integer literal at all (an indirected budget defeats
the point of a readable floor). 10 was chosen because it is already the in-tree convention for 81
of the 129 budgeted examples across `theory_lib/`, including 25 in the sibling
`counterfactual/examples.py`, and gives ~29x headroom over the worst solve in the covered files.
It is a floor, not an equality: 8.6's 30s bimodal convention remains available above it. A
blanket 30 was rejected only because it would cost 30s per failure across ~100 examples on a
genuine hang, with no evidence that the extra margin is needed.

**Raise the budget; never lower the floor.** This is the same discipline 8.8 states for the
oracle gating floor and 8.9 states for `unstable`: the constant encodes a real property, and
editing it to make a run green is the assertion-weakening those sections exist to forbid.

**`max_rlimit` was evaluated and deliberately not adopted.** 8.6 recommends its deterministic
resource-unit budget alongside `max_time` for a flake that is specifically load-driven, which
described `CL_TH_12`/`CL_TH_13` exactly. It was measured -- their requirement bisects to ~3.13M
and ~3.22M units, stable across repeated draws, so a 20M setting would sit ~6x clear -- and then
left out, because that margin is the argument against it rather than for it. **An `rlimit` bound
can only ever cause an inconclusive result, never prevent one.** It has no mechanism to rescue a
solve; it only supplies an additional way to fail. Adding one to an example that a widened
`max_time` has already carried green therefore widens the failure surface without widening the
success surface. The corollary matters for reading a green run: because the bound never fired on
CI, that run is evidence for the `max_time` widening alone, and removing the `rlimit` cannot
regress it.

Reach for `max_rlimit` where it actually earns its place: an example whose wall-clock budget
cannot be widened far enough to be safe (because the suite cannot afford the worst case), where
a *tight, calibrated* rlimit converts an unpredictable load-dependent timeout into a
reproducible, host-independent one. That is a different situation from a budget that simply had
too little headroom, which 8.6's "set budgets generously" already solves outright. Measured
requirements are recorded at the marker site so the option can be exercised without re-deriving
them.

**Coverage is deliberately partial.** `bimodal`, `exclusion`, and `imposition` still carry 20
settings dicts at `max_time: 2` and 2 at `3`. They are the same latent hazard but have not been
observed failing, and bimodal's budgets were calibrated per-example (see that file's
`BM_CM_1`/`BM_CM_4` recalibration record). Extending `_COVERED` to them is a separate,
measurement-backed decision -- not a pattern-match on the logos change.

---

## Quick Reference

### Common Testing Tasks

| Task | Command |
|------|---------|
| Run all tests | `PYTHONPATH=code/src pytest code/tests/ -v` |
| Run specific theory | `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/tests/ -v` |
| Check coverage | `PYTHONPATH=code/src pytest --cov=model_checker --cov-report=term-missing` |
| Run one test | `PYTHONPATH=code/src pytest path/to/test.py::test_function_name -v` |
| Stop on first failure | `PYTHONPATH=code/src pytest -x` |
| Show local vars | `PYTHONPATH=code/src pytest -l` |

### TDD Workflow Quick Reference

1. **RED**: Write failing test
2. **GREEN**: Minimal implementation
3. **REFACTOR**: Improve code quality
4. **REPEAT**: Next requirement

### Coverage Targets

- Overall: ≥85%
- Critical paths: ≥90%
- Utilities: ≥80%
- Error handling: ≥75%

---

## See Also

- [Code Standards](CODE_STANDARDS.md) - Python coding conventions
- [Development Workflow](../implementation/DEVELOPMENT_WORKFLOW.md) - Feature development process
- [Architecture](ARCHITECTURE.md) - System design patterns
- [Manual Testing](../quality/MANUAL_TESTING_GUIDE.md) - Integration and acceptance testing
- [Quality Metrics](../quality/METRICS.md) - Quality measurement and targets

[← Code Standards](CODE_STANDARDS.md) | [Back to Core](README.md) | [Architecture →](ARCHITECTURE.md)
