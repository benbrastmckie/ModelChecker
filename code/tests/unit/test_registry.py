"""Unit tests for the core theory registry (`model_checker.registry`).

Exercises the mechanism in isolation using synthetic theory names -- never `bimodal` /
`exclusion` / `imposition` / `logos`, since those are already registered as a side effect of
importing `model_checker` (see `model_checker/__init__.py`'s bootstrap import of `theory_lib`)
and this suite must not depend on, or interfere with, that real registration.
"""

import pytest

from model_checker import registry


@pytest.fixture(autouse=True)
def _isolated_registry():
    """Snapshot and restore the module-level registry state around each test, so tests here
    can register/clear freely without leaking into other tests (including the real theory
    registrations performed at `model_checker` import time)."""
    saved_registry = dict(registry._REGISTRY)
    saved_order = list(registry._ORDER)
    saved_default = registry._DEFAULT_THEORY
    yield
    registry._REGISTRY.clear()
    registry._REGISTRY.update(saved_registry)
    registry._ORDER.clear()
    registry._ORDER.extend(saved_order)
    registry._DEFAULT_THEORY = saved_default


class _FakeSemantics:
    pass


class _FakeProposition:
    pass


class _FakeModel:
    pass


def test_register_and_retrieve():
    registry.register_theory(
        'widget',
        module_path='some.module.path.widget',
        semantics=_FakeSemantics,
        proposition=_FakeProposition,
        model=_FakeModel,
        operators={'op': object()},
    )
    entry = registry.get_theory_entry('widget')
    assert entry.name == 'widget'
    assert entry.module_path == 'some.module.path.widget'
    assert entry.semantics is _FakeSemantics
    assert entry.proposition is _FakeProposition
    assert entry.model is _FakeModel
    assert 'op' in entry.operators
    assert 'widget' in registry.get_registered()


def test_registration_order_preserved():
    registry.register_theory(
        'alpha', module_path='m.alpha', semantics=_FakeSemantics,
        proposition=_FakeProposition, model=_FakeModel, operators={},
    )
    registry.register_theory(
        'beta', module_path='m.beta', semantics=_FakeSemantics,
        proposition=_FakeProposition, model=_FakeModel, operators={},
    )
    order = registry.get_registered()
    assert order.index('alpha') < order.index('beta')


def test_duplicate_registration_rejected_fail_fast():
    registry.register_theory(
        'gadget', module_path='m.gadget', semantics=_FakeSemantics,
        proposition=_FakeProposition, model=_FakeModel, operators={},
    )
    with pytest.raises(ValueError, match="already registered"):
        registry.register_theory(
            'gadget', module_path='m.gadget.other', semantics=_FakeSemantics,
            proposition=_FakeProposition, model=_FakeModel, operators={},
        )


def test_unknown_name_lookup_raises_with_available_list():
    registry.register_theory(
        'known_one', module_path='m.known_one', semantics=_FakeSemantics,
        proposition=_FakeProposition, model=_FakeModel, operators={},
    )
    with pytest.raises(ValueError) as excinfo:
        registry.get_theory_entry('totally_unknown_theory_name')
    message = str(excinfo.value)
    assert 'totally_unknown_theory_name' in message
    assert 'known_one' in message


def test_lazy_thunk_resolved_once_and_cached():
    calls = []

    def _lazy_semantics():
        calls.append('semantics')
        return _FakeSemantics

    registry.register_theory(
        'lazygadget', module_path='m.lazygadget',
        semantics=_lazy_semantics,
        proposition=_FakeProposition, model=_FakeModel, operators={},
    )
    entry = registry.get_theory_entry('lazygadget')
    assert calls == []  # not resolved at registration time
    assert entry.semantics is _FakeSemantics
    assert calls == ['semantics']
    # Second access must not re-invoke the loader.
    assert entry.semantics is _FakeSemantics
    assert calls == ['semantics']


def test_iter_theories_yields_entries_in_order():
    registry.register_theory(
        'first', module_path='m.first', semantics=_FakeSemantics,
        proposition=_FakeProposition, model=_FakeModel, operators={},
    )
    registry.register_theory(
        'second', module_path='m.second', semantics=_FakeSemantics,
        proposition=_FakeProposition, model=_FakeModel, operators={},
    )
    names = [entry.name for entry in registry.iter_theories()]
    assert names.index('first') < names.index('second')


def test_real_theories_are_registered_via_bootstrap():
    """Sanity check on the actual production registration performed by
    `model_checker/__init__.py`'s bootstrap import of `theory_lib` -- not a synthetic case."""
    registered = registry.get_registered()
    for theory_name in ('bimodal', 'exclusion', 'imposition', 'logos'):
        assert theory_name in registered
        entry = registry.get_theory_entry(theory_name)
        assert entry.module_path == f'model_checker.theory_lib.{theory_name}'
