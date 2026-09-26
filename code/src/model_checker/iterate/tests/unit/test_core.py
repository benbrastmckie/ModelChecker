"""Tests for the core iteration functionality.

These tests focus on the theory-agnostic iteration framework, not
the theory-specific implementations.
"""

import unittest
from types import SimpleNamespace
from unittest.mock import Mock
import z3

# Import the functionality to test
from model_checker.iterate.core import BaseModelIterator

class TestBaseModelIterator(unittest.TestCase):
    """Tests for the BaseModelIterator class."""

    def test_initialization(self):
        """Test that the BaseModelIterator initialization fails with NotImplementedError.

        Since BaseModelIterator is an abstract base class, we expect initializing
        it directly to fail with a NotImplementedError.
        """
        # This test will be implemented later once we have a mock BuildExample
        pass


class TestIterateExample(unittest.TestCase):
    """Tests for the iterate_example convenience function."""

    def test_iterate_example_validation(self):
        """Test that iterate_example validates its inputs."""
        # This test will be implemented later once we have a mock BuildExample
        pass


class TestIsTriviallyTrue(unittest.TestCase):
    """`_is_trivially_true` is the shared filter `_build_exclusion_constraints` and
    `_build_stronger_constraint` use to drop no-op placeholder constraints."""

    def test_bool_val_true_is_trivially_true(self):
        self.assertTrue(BaseModelIterator._is_trivially_true(z3.BoolVal(True)))

    def test_none_is_not_trivially_true(self):
        self.assertFalse(BaseModelIterator._is_trivially_true(None))

    def test_a_real_constraint_is_not_trivially_true(self):
        self.assertFalse(BaseModelIterator._is_trivially_true(z3.Bool('x')))

    def test_bool_val_false_is_not_trivially_true(self):
        self.assertFalse(BaseModelIterator._is_trivially_true(z3.BoolVal(False)))


class TestBuildExclusionConstraints(unittest.TestCase):
    """`_build_exclusion_constraints` wraps the polymorphic
    `_create_difference_constraint` hook (called once, with the full list) into the
    `List[z3.BoolRef]` shape `check_satisfiability` expects."""

    def _fake_iterator(self, difference_constraint):
        fake = SimpleNamespace()
        fake._create_difference_constraint = Mock(return_value=difference_constraint)
        fake._is_trivially_true = BaseModelIterator._is_trivially_true
        return fake

    def test_none_result_yields_empty_list(self):
        fake = self._fake_iterator(None)
        result = BaseModelIterator._build_exclusion_constraints(fake, [Mock()])
        self.assertEqual(result, [])
        fake._create_difference_constraint.assert_called_once()

    def test_trivially_true_result_yields_empty_list(self):
        fake = self._fake_iterator(z3.BoolVal(True))
        result = BaseModelIterator._build_exclusion_constraints(fake, [Mock()])
        self.assertEqual(result, [])

    def test_real_constraint_yields_one_element_list(self):
        constraint = z3.Bool('differs')
        fake = self._fake_iterator(constraint)
        result = BaseModelIterator._build_exclusion_constraints(fake, [Mock(), Mock()])
        self.assertEqual(result, [constraint])

    def test_hook_is_called_once_with_the_full_previous_models_list(self):
        """Not once per model (the old `create_extended_constraints` looping shape) --
        once, with the whole list, per the polymorphic-hook contract every theory's
        `_create_difference_constraint` override already assumes."""
        constraint = z3.Bool('differs')
        fake = self._fake_iterator(constraint)
        previous_models = [Mock(), Mock(), Mock()]
        BaseModelIterator._build_exclusion_constraints(fake, previous_models)
        fake._create_difference_constraint.assert_called_once_with(previous_models)


class TestBuildStrongerConstraint(unittest.TestCase):
    """`_build_stronger_constraint` composes (conjoins) the generic
    `ConstraintGenerator` constraint with every non-trivial theory-specific override,
    rather than preferring one over the other -- required because logos's and
    imposition's own overrides are `BoolVal(True)` no-op placeholders."""

    def _fake_iterator(self, generic, non_iso, stronger):
        fake = SimpleNamespace()
        fake.constraint_generator = Mock()
        fake.constraint_generator.create_stronger_constraint = Mock(return_value=generic)
        fake._create_non_isomorphic_constraint = Mock(return_value=non_iso)
        fake._create_stronger_constraint = Mock(return_value=stronger)
        fake._is_trivially_true = BaseModelIterator._is_trivially_true
        return fake

    def test_all_trivial_or_none_yields_none(self):
        fake = self._fake_iterator(z3.BoolVal(True), None, z3.BoolVal(True))
        result = BaseModelIterator._build_stronger_constraint(fake, Mock())
        self.assertIsNone(result)

    def test_generic_only_is_kept_when_theory_overrides_are_trivial(self):
        """Logos/imposition shape: the theory-specific hooks are BoolVal(True)
        placeholders, so only the generic constraint must survive -- this is the
        composition, not replacement, this method exists to guarantee."""
        generic = z3.Bool('generic_real_constraint')
        fake = self._fake_iterator(generic, z3.BoolVal(True), z3.BoolVal(True))
        result = BaseModelIterator._build_stronger_constraint(fake, Mock())
        self.assertTrue(result.eq(generic))

    def test_theory_specific_only_is_kept_when_generic_is_none(self):
        """Bimodal shape: no is_world, so the generic half contributes nothing, but
        the theory-specific _create_non_isomorphic_constraint is real."""
        theory_specific = z3.Bool('bimodal_blocking_clause')
        fake = self._fake_iterator(None, theory_specific, z3.BoolVal(True))
        result = BaseModelIterator._build_stronger_constraint(fake, Mock())
        self.assertTrue(result.eq(theory_specific))

    def test_both_real_are_conjoined(self):
        generic = z3.Bool('generic_real')
        theory_specific = z3.Bool('theory_real')
        fake = self._fake_iterator(generic, theory_specific, z3.BoolVal(True))
        result = BaseModelIterator._build_stronger_constraint(fake, Mock())
        self.assertEqual(result.decl().name(), 'and')
        children = {str(c) for c in result.children()}
        self.assertEqual(children, {'generic_real', 'theory_real'})


if __name__ == '__main__':
    unittest.main()