"""Theory conformance test suite.

Encodes the canonical theory contract from `theory_lib/docs/THEORY_ARCHITECTURE.md` as an
executable, parametrized test over `AVAILABLE_THEORIES` (and, for the subtheory contract, over
`AVAILABLE_SUBTHEORIES`). This is the intentional RED baseline for the core/theory_lib
refactor: every currently-known contract gap is captured here as a narrowly-scoped
`xfail(strict=True)` naming the specific defect, rather than a broad module-level skip. As each
gap is fixed in a later phase, its `xfail` marker is removed; `strict=True` means an
unexpectedly-passing assertion (an XPASS) fails the suite immediately, so no fix can be silently
left un-flipped.

Do not add a new xfail here without a reason string describing the exact defect -- "unexplained"
xfails defeat the purpose of this file as a living gap tracker.
"""

import ast
import os

import pytest

from model_checker import registry
from model_checker.theory_lib import get_test_examples
from model_checker.theory_lib.logos.subtheories import AVAILABLE_SUBTHEORIES

# Parametrize over the registry (the single source of truth as of the Phase 10 registry
# introduction), not a standalone literal -- `AVAILABLE_THEORIES` itself is now just a view over
# this same registry (see `theory_lib/__init__.py`), so this is the authoritative form.
AVAILABLE_THEORIES = registry.get_registered()

THEORY_LIB_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LOGOS_SUBTHEORIES_ROOT = os.path.join(THEORY_LIB_ROOT, 'logos', 'subtheories')

# Canonical file/attribute sets, mirroring theory_lib/docs/THEORY_ARCHITECTURE.md's Theory
# Contract and Subtheory Contract sections.
REQUIRED_ROOT_ITEMS = [
    '__init__.py',
    'operators.py',
    'examples.py',
    'tests',
    'docs',
    'README.md',
    'CITATION.md',
    'LICENSE.md',
    'VERSION',
]

REQUIRED_DOCS_FILES = [
    'README.md',
    'API_REFERENCE.md',
    'ARCHITECTURE.md',
    'ITERATE.md',
    'SETTINGS.md',
    'USER_GUIDE.md',
]

REQUIRED_EXAMPLES_ATTRS = [
    'example_range',
    'test_example_range',
    'semantic_theories',
    'unit_tests',
]

REQUIRED_GET_THEORY_KEYS = {'semantics', 'proposition', 'model', 'operators'}

REQUIRED_SUBTHEORY_ITEMS = [
    '__init__.py',
    'operators.py',
    'examples.py',
    'tests',
    'README.md',
]

ITERATE_REQUIRED_ATTRS = [
    'iterate_example',
    'iterate_example_generator',
]

# --- Known RED-baseline gaps, tracked individually (see module docstring). ---

# logos's entry was removed in the phase that split its monolithic semantic.py into a
# semantic/ package (core.py + proposition.py + model.py behind a re-export-only __init__.py),
# matching the form exclusion was normalized onto. bimodal's entry was removed the same way:
# semantic.py was moved into semantic/core.py and then split into core.py/model.py/proposition.py.
# Kept as an empty dict (rather than deleted) so _xfail_params()'s call site below needs no
# further edit.
SEMANTIC_PACKAGE_XFAIL_REASON = {}

# Fixed in the phase that restored bimodal/iterate.py (ported to the current
# iterate_example_generator convention using imposition/iterate.py as the template) and
# re-exported iterate_example / iterate_example_generator from bimodal/__init__.py. Kept as an
# empty dict (rather than deleted) so _xfail_params()'s call site below needs no further edit.
ITERATE_MODULE_XFAIL_REASON = {}

# Fixed in the phase that unified get_theory() signatures: logos now uses get_theory(config=None,
# *, subtheories=None), matching the other three theories' get_theory(config=None). Kept as an
# empty dict (rather than deleted) so _xfail_params()'s call site below needs no further edit.
GET_THEORY_SIGNATURE_XFAIL_REASON = {}

# Fixed in the phase that added bimodal's test_example_range = unit_tests.
GET_TEST_EXAMPLES_XFAIL_REASON = {}

# Fixed alongside GET_TEST_EXAMPLES_XFAIL_REASON above (same root cause).
MISSING_EXAMPLES_ATTR_XFAIL_REASON = {}

# Fixed in the phase that removed logos's duplicate example_range assignment (kept the one
# assigned after unit_tests is final, near semantic_theories).
DUPLICATE_EXAMPLE_RANGE_XFAIL_REASON = {}


def _xfail_params(xfail_reasons):
    """Build pytest.param list over AVAILABLE_THEORIES, marking known-gap theories xfail."""
    params = []
    for theory in AVAILABLE_THEORIES:
        if theory in xfail_reasons:
            params.append(
                pytest.param(
                    theory,
                    marks=pytest.mark.xfail(strict=True, reason=xfail_reasons[theory]),
                    id=theory,
                )
            )
        else:
            params.append(pytest.param(theory, id=theory))
    return params


def _assignment_lines(tree, name):
    """Return the line numbers where `name` is assigned at module (top) level."""
    lines = []
    for node in tree.body:
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name) and target.id == name:
                    lines.append(node.lineno)
        elif isinstance(node, ast.AnnAssign):
            if isinstance(node.target, ast.Name) and node.target.id == name:
                lines.append(node.lineno)
    return lines


class TestTheoryFileSet:
    """Required file set: theory root, docs/, and the semantic/ package form."""

    @pytest.mark.parametrize('theory', AVAILABLE_THEORIES)
    def test_required_root_items_exist(self, theory):
        theory_dir = os.path.join(THEORY_LIB_ROOT, theory)
        missing = [
            item for item in REQUIRED_ROOT_ITEMS
            if not os.path.exists(os.path.join(theory_dir, item))
        ]
        assert not missing, f"{theory} is missing required root item(s): {missing}"

    @pytest.mark.parametrize('theory', AVAILABLE_THEORIES)
    def test_required_docs_files_exist(self, theory):
        docs_dir = os.path.join(THEORY_LIB_ROOT, theory, 'docs')
        missing = [
            f for f in REQUIRED_DOCS_FILES
            if not os.path.exists(os.path.join(docs_dir, f))
        ]
        assert not missing, f"{theory}/docs/ is missing required file(s): {missing}"

    @pytest.mark.parametrize('theory', _xfail_params(SEMANTIC_PACKAGE_XFAIL_REASON))
    def test_semantic_is_a_package(self, theory):
        semantic_path = os.path.join(THEORY_LIB_ROOT, theory, 'semantic')
        assert os.path.isdir(semantic_path), (
            f"{theory}/semantic must be a package (directory with __init__.py), "
            f"not a bare semantic.py module"
        )
        assert os.path.exists(os.path.join(semantic_path, '__init__.py')), (
            f"{theory}/semantic/ is a directory but has no __init__.py"
        )
        # A directory alone is not sufficient: THEORY_ARCHITECTURE.md's contract requires
        # semantic/ to actually hold the semantics implementation (core.py), not merely exist as
        # a re-export or compatibility shim. bimodal's semantic/ used to be exactly this trap --
        # a real directory with a real __init__.py, but no core.py; it dynamically re-executed a
        # sibling semantic.py purely for sys.modules pickling compatibility. That shim is gone;
        # bimodal now has a real core.py like the other three theories.
        assert os.path.exists(os.path.join(semantic_path, 'core.py')), (
            f"{theory}/semantic/ exists but has no core.py -- it is not the canonical "
            f"semantic package (the required semantics implementation module), just a "
            f"directory that happens to share the name"
        )


class TestExamplesContract:
    """examples.py must define the four required attributes, each exactly once."""

    @pytest.mark.parametrize('theory', _xfail_params(MISSING_EXAMPLES_ATTR_XFAIL_REASON))
    def test_required_attrs_present(self, theory):
        examples_path = os.path.join(THEORY_LIB_ROOT, theory, 'examples.py')
        with open(examples_path) as f:
            tree = ast.parse(f.read(), filename=examples_path)
        top_level_names = set()
        for node in tree.body:
            if isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(target, ast.Name):
                        top_level_names.add(target.id)
            elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
                top_level_names.add(node.target.id)
        missing = [attr for attr in REQUIRED_EXAMPLES_ATTRS if attr not in top_level_names]
        assert not missing, f"{theory}/examples.py is missing required attribute(s): {missing}"

    @pytest.mark.parametrize('theory', _xfail_params(DUPLICATE_EXAMPLE_RANGE_XFAIL_REASON))
    def test_required_attrs_assigned_exactly_once(self, theory):
        examples_path = os.path.join(THEORY_LIB_ROOT, theory, 'examples.py')
        with open(examples_path) as f:
            tree = ast.parse(f.read(), filename=examples_path)
        duplicates = {}
        for attr in REQUIRED_EXAMPLES_ATTRS:
            lines = _assignment_lines(tree, attr)
            if len(lines) > 1:
                duplicates[attr] = lines
        assert not duplicates, (
            f"{theory}/examples.py assigns these attributes more than once "
            f"(later assignment silently shadows earlier ones): {duplicates}"
        )


class TestGetTheoryContract:
    """get_theory() must have a uniform signature and return the expected dict shape."""

    @pytest.mark.parametrize('theory', AVAILABLE_THEORIES)
    def test_get_theory_returns_expected_shape(self, theory):
        module = __import__(
            f'model_checker.theory_lib.{theory}', fromlist=['get_theory']
        )
        result = module.get_theory()
        assert isinstance(result, dict), f"{theory}.get_theory() must return a dict"
        assert set(result.keys()) == REQUIRED_GET_THEORY_KEYS, (
            f"{theory}.get_theory() returned keys {sorted(result.keys())}, "
            f"expected exactly {sorted(REQUIRED_GET_THEORY_KEYS)}"
        )

    @pytest.mark.parametrize('theory', _xfail_params(GET_THEORY_SIGNATURE_XFAIL_REASON))
    def test_get_theory_uses_uniform_config_parameter(self, theory):
        import inspect
        module = __import__(
            f'model_checker.theory_lib.{theory}', fromlist=['get_theory']
        )
        sig = inspect.signature(module.get_theory)
        params = list(sig.parameters.values())
        assert params, f"{theory}.get_theory() must accept at least a 'config' parameter"
        first = params[0]
        assert first.name == 'config' and first.kind in (
            inspect.Parameter.POSITIONAL_OR_KEYWORD,
            inspect.Parameter.POSITIONAL_ONLY,
        ), (
            f"{theory}.get_theory()'s first parameter is {first.name!r} (kind={first.kind}), "
            f"expected a leading 'config' parameter for a uniform signature across all theories"
        )
        # Every theory takes exactly 'config'; logos is the sole documented exception, which may
        # additionally accept 'subtheories' as a keyword-only parameter (see
        # THEORY_ARCHITECTURE.md's Theory Contract and logos/__init__.py's get_theory()
        # docstring) -- any other extra parameter, or a non-keyword-only 'subtheories', is not
        # part of the uniform contract and must fail here.
        extra = params[1:]
        if theory == 'logos':
            assert [p.name for p in extra] == ['subtheories'], (
                f"logos.get_theory() has extra parameter(s) {[p.name for p in extra]}, "
                f"expected exactly one additional 'subtheories' parameter"
            )
            assert extra[0].kind == inspect.Parameter.KEYWORD_ONLY, (
                f"logos.get_theory()'s 'subtheories' parameter must be keyword-only, "
                f"got kind={extra[0].kind}"
            )
        else:
            assert not extra, (
                f"{theory}.get_theory() has unexpected extra parameter(s) "
                f"{[p.name for p in extra]}; only 'config' is part of the uniform contract"
            )


class TestGetTestExamplesContract:
    """theory_lib.get_test_examples(name) must succeed for every registered theory."""

    @pytest.mark.parametrize('theory', _xfail_params(GET_TEST_EXAMPLES_XFAIL_REASON))
    def test_get_test_examples_succeeds(self, theory):
        result = get_test_examples(theory)
        assert isinstance(result, dict) and len(result) > 0, (
            f"get_test_examples('{theory}') should return a non-empty dict"
        )


class TestIterateContract:
    """iterate.py is required for every theory (not optional) and must expose the generator
    interface with its markers."""

    @pytest.mark.parametrize('theory', _xfail_params(ITERATE_MODULE_XFAIL_REASON))
    def test_iterate_module_exists(self, theory):
        iterate_path = os.path.join(THEORY_LIB_ROOT, theory, 'iterate.py')
        assert os.path.exists(iterate_path), (
            f"{theory}/iterate.py is required: DEFAULT_EXAMPLE_SETTINGS declares an "
            f"'iterate' setting for every theory, so its absence is a live reachable "
            f"ImportError under iterate: 2, not merely a missing optional file"
        )

    @pytest.mark.parametrize('theory', _xfail_params(ITERATE_MODULE_XFAIL_REASON))
    def test_iterate_module_exposes_required_interface(self, theory):
        module = __import__(
            f'model_checker.theory_lib.{theory}.iterate', fromlist=ITERATE_REQUIRED_ATTRS
        )
        missing = [attr for attr in ITERATE_REQUIRED_ATTRS if not hasattr(module, attr)]
        assert not missing, f"{theory}/iterate.py is missing required attribute(s): {missing}"

        iterate_example_generator = module.iterate_example_generator
        assert getattr(iterate_example_generator, 'returns_generator', False) is True, (
            f"{theory}.iterate.iterate_example_generator must set "
            f"'.returns_generator = True' so builder/runner.py's generator-interface "
            f"detection recognizes it"
        )
        assert hasattr(iterate_example_generator, '__wrapped__'), (
            f"{theory}.iterate.iterate_example_generator must set '.__wrapped__' so "
            f"builder/runner.py's hasattr-based detection recognizes the generator interface"
        )

        # {Theory}ModelIterator must exist somewhere in the iterate module, named after the
        # theory (capitalized).
        theory_class_name = f"{theory.capitalize()}ModelIterator"
        assert hasattr(module, theory_class_name) or any(
            name.endswith('ModelIterator') for name in dir(module)
        ), (
            f"{theory}/iterate.py must expose a *ModelIterator class "
            f"(expected {theory_class_name} or similarly named)"
        )


class TestSubtheoryConformance:
    """Subtheory file set and the non-empty get_operators() requirement."""

    @pytest.mark.parametrize('subtheory', AVAILABLE_SUBTHEORIES)
    def test_required_items_exist(self, subtheory):
        subtheory_dir = os.path.join(LOGOS_SUBTHEORIES_ROOT, subtheory)
        missing = [
            item for item in REQUIRED_SUBTHEORY_ITEMS
            if not os.path.exists(os.path.join(subtheory_dir, item))
        ]
        assert not missing, f"subtheory '{subtheory}' is missing required item(s): {missing}"

    @pytest.mark.parametrize('subtheory', AVAILABLE_SUBTHEORIES)
    def test_get_operators_non_empty(self, subtheory):
        module = __import__(
            f'model_checker.theory_lib.logos.subtheories.{subtheory}.operators',
            fromlist=['get_operators'],
        )
        operators = module.get_operators()
        assert isinstance(operators, dict) and len(operators) > 0, (
            f"subtheory '{subtheory}'s get_operators() must return a non-empty dict; "
            f"a subtheory contributing zero operators is a defect, not a valid configuration"
        )
