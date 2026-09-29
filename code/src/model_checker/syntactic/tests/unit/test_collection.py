"""Unit tests for `Operator.aliases` registration in `OperatorCollection`.

These tests cover the alias mechanism added so a theory's `operators.py` can declare
one or more user-facing Unicode (or other) spellings for an operator alongside its
canonical LaTeX `name`. Collision handling (`DuplicateOperatorError`) and unknown-key
lookup (`UnknownOperatorError`) are covered separately in the Phase 2 additions below.
"""

import pytest

from model_checker.syntactic.collection import OperatorCollection
from model_checker.syntactic.operators import Operator
from model_checker.syntactic.syntax import Syntax
from model_checker.syntactic.errors import DuplicateOperatorError, UnknownOperatorError


class TestAliasRegistration:
    """Operators with a declared `aliases` list register under every key."""

    def test_operator_with_single_alias_registers_under_both_keys(self):
        class AndOp(Operator):
            name = "\\wedge"
            arity = 2
            aliases = ["∧"]

        collection = OperatorCollection(AndOp)

        assert collection["\\wedge"] is AndOp
        assert collection["∧"] is AndOp

    def test_operator_with_multiple_aliases_registers_under_all_keys(self):
        class OrOp(Operator):
            name = "\\vee"
            arity = 2
            aliases = ["∨", "V"]

        collection = OperatorCollection(OrOp)

        assert collection["\\vee"] is OrOp
        assert collection["∨"] is OrOp
        assert collection["V"] is OrOp

    def test_operator_without_aliases_attribute_registers_under_name_only(self):
        class NegOp(Operator):
            name = "\\neg"
            arity = 1
            # deliberately no `aliases` attribute declared at all

        collection = OperatorCollection(NegOp)

        assert collection["\\neg"] is NegOp
        assert list(collection.operator_dictionary.keys()) == ["\\neg"]

    def test_declared_aliases_do_not_leak_to_sibling_without_aliases(self):
        class WithAlias(Operator):
            name = "\\wedge"
            arity = 2
            aliases = ["∧"]

        class WithoutAlias(Operator):
            name = "\\vee"
            arity = 2

        assert WithAlias.aliases == ["∧"]
        assert WithoutAlias.aliases == []

        collection = OperatorCollection([WithAlias, WithoutAlias])

        assert set(collection.operator_dictionary.keys()) == {"\\wedge", "∧", "\\vee"}

    def test_add_operator_never_mutates_shared_default_aliases_list(self):
        """Regression guard for the shared-mutable-default risk: `add_operator` must
        only *read* `aliases`, never append to it, or a sibling subclass that falls
        back to the base-class default would silently gain aliases it never declared.
        """
        class WithAlias(Operator):
            name = "\\wedge"
            arity = 2
            aliases = ["∧"]

        class NoOwnAliases(Operator):
            name = "\\vee"
            arity = 2
            # falls back to Operator.aliases (the shared class-level default)

        OperatorCollection([WithAlias, NoOwnAliases])

        assert Operator.aliases == []
        assert NoOwnAliases.aliases == []


class TestAliasEndToEndParsing:
    """A Unicode alias and its LaTeX canonical name resolve to the same operator
    class when parsed through `Syntax`, for both infix (arity 2) and prefix
    (arity 1) operators.
    """

    def test_infix_unicode_alias_resolves_to_same_class_as_latex_name(self):
        class AndOp(Operator):
            name = "\\wedge"
            arity = 2
            aliases = ["∧"]

        collection = OperatorCollection(AndOp)

        latex_syntax = Syntax(["(p \\wedge q)"], [], collection)
        unicode_syntax = Syntax(["(p ∧ q)"], [], collection)

        assert latex_syntax.premises[0].operator == AndOp
        assert unicode_syntax.premises[0].operator == AndOp
        assert unicode_syntax.premises[0].operator == latex_syntax.premises[0].operator

    def test_prefix_unicode_alias_resolves_to_same_class_as_latex_name(self):
        class NegOp(Operator):
            name = "\\neg"
            arity = 1
            aliases = ["¬"]

        collection = OperatorCollection(NegOp)

        latex_syntax = Syntax(["\\neg p"], [], collection)
        unicode_syntax = Syntax(["¬ p"], [], collection)

        assert latex_syntax.premises[0].operator == NegOp
        assert unicode_syntax.premises[0].operator == NegOp


class TestDuplicateAndUnknownOperatorErrors:
    """Phase 2: conflict-aware duplicate policy and `UnknownOperatorError` on lookup.

    Policy (plan Decision 1): re-registering the SAME class under a key it already
    owns is a silent no-op; a DIFFERENT class claiming an already-taken name or
    alias raises `DuplicateOperatorError`.
    """

    def test_different_classes_claiming_same_alias_raises(self):
        class OpA(Operator):
            name = "\\a"
            arity = 1
            aliases = ["α"]

        class OpB(Operator):
            name = "\\b"
            arity = 1
            aliases = ["α"]

        collection = OperatorCollection(OpA)
        with pytest.raises(DuplicateOperatorError):
            collection.add_operator(OpB)

    def test_alias_colliding_with_another_operators_name_raises(self):
        class OpA(Operator):
            name = "∧"
            arity = 2

        class OpB(Operator):
            name = "\\wedge"
            arity = 2
            aliases = ["∧"]

        collection = OperatorCollection(OpA)
        with pytest.raises(DuplicateOperatorError):
            collection.add_operator(OpB)

    def test_readding_same_class_directly_is_silent_noop(self):
        class OpA(Operator):
            name = "\\wedge"
            arity = 2
            aliases = ["∧"]

        collection = OperatorCollection(OpA)
        collection.add_operator(OpA)  # no raise

        assert collection["\\wedge"] is OpA
        assert collection["∧"] is OpA

    def test_readding_same_class_via_collection_merge_is_silent_noop(self):
        class OpA(Operator):
            name = "\\wedge"
            arity = 2
            aliases = ["∧"]

        collection1 = OperatorCollection(OpA)
        collection2 = OperatorCollection(OpA)

        collection1.add_operator(collection2)  # no raise

        assert collection1["\\wedge"] is OpA
        assert collection1["∧"] is OpA

    def test_readding_same_class_via_serialize_deserialize_roundtrip_is_silent_noop(self):
        import sys

        from model_checker.builder.serialize import serialize_operators, deserialize_operators

        class RoundtripOp(Operator):
            name = "\\wedge"
            arity = 2
            aliases = ["∧"]

        # Give the class a resolvable module path for deserialize_operators' importlib call:
        # `getattr(module, class_name)` needs the class reachable as a module attribute, not
        # just tagged with the module's __name__.
        RoundtripOp.__module__ = __name__
        setattr(sys.modules[__name__], "RoundtripOp", RoundtripOp)

        collection = OperatorCollection(RoundtripOp)
        serialized = serialize_operators(collection)

        # Aliased class is serialized once per registered key (name + each alias).
        assert set(serialized.keys()) == {"\\wedge", "∧"}

        rebuilt = deserialize_operators(serialized)

        assert rebuilt["\\wedge"] is RoundtripOp
        assert rebuilt["∧"] is RoundtripOp

    def test_unknown_operator_lookup_raises_with_available_operators(self):
        class OpA(Operator):
            name = "\\wedge"
            arity = 2

        collection = OperatorCollection(OpA)

        with pytest.raises(UnknownOperatorError) as exc_info:
            collection["\\nosuchop"]

        assert exc_info.value.context.get("available") == ["\\wedge"]

    def test_apply_operator_with_unregistered_head_raises_unknown_operator_error(self):
        collection = OperatorCollection()

        with pytest.raises(UnknownOperatorError):
            collection.apply_operator(["\\nosuchop", ["p"], ["q"]])
