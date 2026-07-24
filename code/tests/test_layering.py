"""Layering test: enforces the strictly one-way core -> theory_lib dependency direction.

Walks the AST of every production module under `code/src/model_checker/` (test directories are
excluded -- see EXCLUDED_DIR_SEGMENTS -- since integration/e2e tests legitimately import
theories directly) and classifies each into one of three layers declared in
`theory_lib/docs/THEORY_ARCHITECTURE.md`'s Layering section:

- **core**: models, syntactic, solver, utils, iterate, builder, settings, output, z3_shim.
- **theory_lib**: may import core freely; may never be imported by core. Excluded from this
  walk entirely -- governed by its own contract (theory conformance), not this boundary check.
- **upper**: `model_checker/__init__.py`, `model_checker/__main__.py`, and everything under
  `jupyter/`. Recorded here as the named UPPER_LAYER_SINGLE_FILES / UPPER_LAYER_DIR_PREFIXES
  constants rather than a scattered exemption.

Two independently-scoped rules, not one blanket "core vs. everything else" split:

1. **theory_lib dependency direction** (import nodes, including function-local imports, and
   string literals reaching theory_lib via `importlib.import_module(f"...")`) applies to the
   **core** layer only. The upper layer is explicitly permitted to import theory_lib -- that is
   the entire point of it being "upper": `jupyter/` and the two top-level entry modules
   legitimately need to know about all theories, and this is the one place the dependency
   direction may correctly invert.
2. **Hardcoded theory-name string literals** (`'bimodal'`, `'exclusion'`, `'imposition'`,
   `'logos'`) apply to **core + upper** (i.e. everywhere under `model_checker/` except
   `theory_lib/` itself). This is a different concern from (1) -- it is about extensibility via
   the registry, not directional dependency -- and applies to jupyter/ too: jupyter is allowed
   to *depend on* theory_lib, but is not exempt from *enumerating* theory names inline, since a
   registry-driven adapter/lookup mechanism replaces exactly this enumeration in a later phase
   without changing jupyter's layer classification at all.

This is the intentional RED baseline for the core/theory_lib refactor: it is expected to FAIL
until the violations enumerated in the plan are fixed in later phases. There is no module-level
skip: this test runs and reports every violation with file:line so the RED state is visible, not
silenced. Docstrings are excluded from the string-literal scans (both rules) -- prose that
merely *mentions* "model_checker.theory_lib" or a theory name in a module/class/function
docstring is not a functional reference and would otherwise produce false positives (confirmed
against `builder/serialize.py` and `builder/strategies.py`, both of which only mention
theory_lib in docstring prose).

`model_checker/api.py` is named in the Layering section as the eventual upper-layer home for
theory-aware helpers currently living in `utils/api.py`; until that relocation happens,
`utils/api.py` is still physically inside the `utils` core package and is correctly treated as a
core-layer violation site by this test, not an upper-layer exemption.
"""

import ast
import os

MODEL_CHECKER_ROOT = os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
    'src', 'model_checker',
)

CORE_PACKAGE_DIRS = [
    'models', 'syntactic', 'solver', 'utils', 'iterate', 'builder', 'settings', 'output',
]
CORE_SINGLE_FILES = ['z3_shim.py', 'registry.py']

# Upper layer: permitted to import theory_lib (rule 1), but still subject to the
# hardcoded-theory-name rule (rule 2) -- see module docstring.
UPPER_LAYER_SINGLE_FILES = ['__init__.py', '__main__.py']
UPPER_LAYER_DIR_PREFIXES = ['jupyter']

# Directories excluded from the walk entirely: theory_lib itself (governed by its own contract,
# not this core-boundary check), and every package's own tests/ directory (integration/e2e tests
# legitimately import theories directly -- none of the plan's enumerated violations are test
# files, and 14+ existing core-package test files already do this intentionally).
EXCLUDED_TOP_DIRS = ['theory_lib']
EXCLUDED_DIR_SEGMENTS = {'tests', '__pycache__'}

THEORY_NAMES = {'bimodal', 'exclusion', 'imposition', 'logos'}
THEORY_LIB_DOTTED = 'model_checker.theory_lib'
# Path-separated form: catches human-readable references (error messages, log text) such as
# builder/strategies.py's "Theory library files must be under model_checker/theory_lib" --
# these are not `importlib.import_module()` calls, but they are still a reference to theory_lib
# from core code and the plan enumerates this exact site as an expected RED violation.
THEORY_LIB_SLASH = 'model_checker/theory_lib'


def _classify(rel_path):
    """Classify a path (relative to MODEL_CHECKER_ROOT) into 'core', 'upper', or None (skip)."""
    parts = rel_path.split(os.sep)
    if parts[0] in EXCLUDED_TOP_DIRS:
        return None
    if any(seg in EXCLUDED_DIR_SEGMENTS for seg in parts):
        return None
    if len(parts) == 1 and parts[0] in UPPER_LAYER_SINGLE_FILES:
        return 'upper'
    if parts[0] in UPPER_LAYER_DIR_PREFIXES:
        return 'upper'
    if len(parts) == 1 and parts[0] in CORE_SINGLE_FILES:
        return 'core'
    if parts[0] in CORE_PACKAGE_DIRS:
        return 'core'
    return None


def _iter_python_files(layers):
    """Yield (rel_path, abs_path, layer) for every .py file under model_checker/ whose
    classified layer is in `layers`."""
    for dirpath, dirnames, filenames in os.walk(MODEL_CHECKER_ROOT):
        rel_dir = os.path.relpath(dirpath, MODEL_CHECKER_ROOT)
        # Prune excluded directories in-place so os.walk doesn't descend into them.
        dirnames[:] = [
            d for d in dirnames
            if d not in EXCLUDED_DIR_SEGMENTS
            and not (rel_dir == '.' and d in EXCLUDED_TOP_DIRS)
        ]
        for filename in filenames:
            if not filename.endswith('.py'):
                continue
            rel_path = os.path.normpath(
                os.path.join(rel_dir, filename) if rel_dir != '.' else filename
            )
            layer = _classify(rel_path)
            if layer in layers:
                yield rel_path, os.path.join(dirpath, filename), layer


def _docstring_node_ids(tree):
    """Return the set of id()s of Constant nodes that are docstrings (the first statement of a
    Module/ClassDef/FunctionDef/AsyncFunctionDef body, when it is a bare string expression) --
    these are excluded from the string-literal scans below, since they are prose, not code."""
    ids = set()
    candidates = [tree] + [
        n for n in ast.walk(tree)
        if isinstance(n, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef))
    ]
    for node in candidates:
        body = getattr(node, 'body', None)
        if body and isinstance(body[0], ast.Expr):
            value = body[0].value
            if isinstance(value, ast.Constant) and isinstance(value.value, str):
                ids.add(id(value))
    return ids


def _theory_lib_dependency_violations(rel_path, tree, docstring_ids):
    """Rule 1 (core-only): import nodes and string literals reaching theory_lib."""
    violations = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name == THEORY_LIB_DOTTED or alias.name.startswith(THEORY_LIB_DOTTED + '.'):
                    violations.append(
                        f"{rel_path}:{node.lineno}: `import {alias.name}` imports theory_lib "
                        f"from a core module"
                    )
        elif isinstance(node, ast.ImportFrom):
            module = node.module or ''
            if module == THEORY_LIB_DOTTED or module.startswith(THEORY_LIB_DOTTED + '.'):
                violations.append(
                    f"{rel_path}:{node.lineno}: `from {module} import ...` imports theory_lib "
                    f"from a core module"
                )
        elif (
            isinstance(node, ast.Constant)
            and isinstance(node.value, str)
            and id(node) not in docstring_ids
            and (THEORY_LIB_DOTTED in node.value or THEORY_LIB_SLASH in node.value)
        ):
            violations.append(
                f"{rel_path}:{node.lineno}: string literal {node.value!r} references "
                f"theory_lib from a core module"
            )
    return violations


def _hardcoded_theory_name_violations(rel_path, tree, docstring_ids):
    """Rule 2 (core + upper): hardcoded theory-name string literals."""
    violations = []
    for node in ast.walk(tree):
        if (
            isinstance(node, ast.Constant)
            and isinstance(node.value, str)
            and id(node) not in docstring_ids
            and node.value in THEORY_NAMES
        ):
            violations.append(
                f"{rel_path}:{node.lineno}: string literal {node.value!r} hardcodes a "
                f"theory name; theory identity must come from the registry"
            )
    return violations


def test_no_core_module_imports_or_references_theory_lib():
    """RED baseline: core modules currently import/reference theory_lib in several places.

    This assertion is expected to FAIL until those violations are fixed in a later phase --
    intentionally no xfail marker here (per the plan, this phase's job is to make the RED state
    visible, not to suppress it). The failure message enumerates every violation with file:line.
    """
    all_violations = []
    for rel_path, abs_path, _layer in sorted(_iter_python_files({'core'})):
        with open(abs_path, encoding='utf-8') as f:
            tree = ast.parse(f.read(), filename=abs_path)
        docstring_ids = _docstring_node_ids(tree)
        all_violations.extend(
            _theory_lib_dependency_violations(rel_path, tree, docstring_ids)
        )

    assert not all_violations, (
        f"{len(all_violations)} core-layer violation(s) found (core modules must never import "
        f"or reference theory_lib, statically or by string literal):\n"
        + "\n".join(f"  - {v}" for v in all_violations)
    )


def test_no_hardcoded_theory_names_in_core_or_upper_layer():
    """RED baseline: several core AND upper-layer modules hardcode theory names as string
    literals (builder/loader.py, builder/project.py, and jupyter/adapters.py's four-theory
    dict, among others). Applies to core + upper (see module docstring for why jupyter/ is not
    exempt from this particular rule despite being permitted to import theory_lib)."""
    all_violations = []
    for rel_path, abs_path, _layer in sorted(_iter_python_files({'core', 'upper'})):
        with open(abs_path, encoding='utf-8') as f:
            tree = ast.parse(f.read(), filename=abs_path)
        docstring_ids = _docstring_node_ids(tree)
        all_violations.extend(
            _hardcoded_theory_name_violations(rel_path, tree, docstring_ids)
        )

    assert not all_violations, (
        f"{len(all_violations)} hardcoded-theory-name violation(s) found:\n"
        + "\n".join(f"  - {v}" for v in all_violations)
    )


def test_upper_layer_classification_has_no_false_positives():
    """Sanity check on _classify() itself, independent of the two assertions above."""
    assert _classify(os.path.join('theory_lib', 'bimodal', 'operators.py')) is None
    assert _classify(os.path.join('theory_lib', '__init__.py')) is None
    assert _classify('__init__.py') == 'upper'
    assert _classify('__main__.py') == 'upper'
    assert _classify(os.path.join('jupyter', 'display.py')) == 'upper'
    assert _classify('z3_shim.py') == 'core'
    assert _classify('registry.py') == 'core'
    assert _classify(os.path.join('utils', 'api.py')) == 'core'
    assert _classify(os.path.join('builder', 'tests', 'unit', 'test_project.py')) is None


def test_docstring_exclusion_avoids_false_positives():
    """Sanity check: a module/class/function docstring that merely mentions theory_lib or a
    theory name in prose must not be flagged -- confirmed against two real files that would
    otherwise false-positive on rule 1 (docstrings mentioning "model_checker.theory_lib")."""
    for rel_path in (
        os.path.join('builder', 'serialize.py'),
        os.path.join('builder', 'strategies.py'),
    ):
        abs_path = os.path.join(MODEL_CHECKER_ROOT, rel_path)
        with open(abs_path, encoding='utf-8') as f:
            tree = ast.parse(f.read(), filename=abs_path)
        docstring_ids = _docstring_node_ids(tree)
        violations = _theory_lib_dependency_violations(rel_path, tree, docstring_ids)
        docstring_only_violations = [v for v in violations if 'Serialize an OperatorCollection' in v or 'Import strategy for theory library files' in v]
        assert not docstring_only_violations, (
            f"docstring exclusion failed for {rel_path}: {docstring_only_violations}"
        )
