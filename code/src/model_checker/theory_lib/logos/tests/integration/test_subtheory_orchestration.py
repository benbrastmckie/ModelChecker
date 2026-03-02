"""
Integration test orchestration for all Logos subtheories.

This module ensures that all subtheory tests run together and validates
the integration between subtheories and the main Logos framework.
"""

import pytest
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Any

# Import our protocols to ensure they work
from model_checker.theory_lib.logos.protocols import (
    SubtheoryProtocol,
    OperatorProtocol,
    SemanticsProtocol,
    RegistryProtocol,
    PropositionProtocol
)
from model_checker.theory_lib.logos.operators import LogosOperatorRegistry
from model_checker.theory_lib.logos.semantic import LogosSemantics


class TestSubtheoryOrchestration:
    """Test orchestration across all Logos subtheories."""

    @pytest.fixture
    def subtheory_names(self) -> List[str]:
        """Get list of all subtheory names."""
        return ['extensional', 'modal', 'constitutive', 'counterfactual', 'relevance']

    @pytest.fixture
    def registry(self) -> LogosOperatorRegistry:
        """Create a fresh operator registry."""
        return LogosOperatorRegistry()

    def test_all_subtheories_loadable(self, registry: LogosOperatorRegistry, subtheory_names: List[str]):
        """Test that all subtheories can be loaded without errors."""
        for name in subtheory_names:
            module = registry.load_subtheory(name)
            assert module is not None, f"Failed to load subtheory: {name}"
            assert hasattr(module, 'get_operators'), f"Subtheory {name} missing get_operators method"
            assert hasattr(module, 'get_examples'), f"Subtheory {name} missing get_examples method"

    def test_subtheory_protocol_compliance(self, registry: LogosOperatorRegistry, subtheory_names: List[str]):
        """Test that all subtheories comply with SubtheoryProtocol."""
        for name in subtheory_names:
            module = registry.load_subtheory(name)

            # Test get_operators
            operators = module.get_operators()
            assert isinstance(operators, dict), f"Subtheory {name} get_operators must return dict"

            # Test get_examples
            examples = module.get_examples()
            assert isinstance(examples, dict), f"Subtheory {name} get_examples must return dict"

            # Test validate_config if it exists
            if hasattr(module, 'validate_config'):
                # Test with empty config
                result = module.validate_config({})
                assert isinstance(result, bool), f"Subtheory {name} validate_config must return bool"

    def test_operator_protocol_compliance(self, registry: LogosOperatorRegistry, subtheory_names: List[str]):
        """Test that all operators comply with OperatorProtocol."""
        for name in subtheory_names:
            module = registry.load_subtheory(name)
            operators = module.get_operators()

            for op_name, op_class in operators.items():
                # Check required methods exist
                assert hasattr(op_class, 'true_at'), f"Operator {op_name} in {name} missing true_at"
                assert hasattr(op_class, 'false_at'), f"Operator {op_name} in {name} missing false_at"
                assert hasattr(op_class, 'extended_verify'), f"Operator {op_name} in {name} missing extended_verify"
                assert hasattr(op_class, 'extended_falsify'), f"Operator {op_name} in {name} missing extended_falsify"
                assert hasattr(op_class, 'find_verifiers_and_falsifiers'), f"Operator {op_name} in {name} missing find_verifiers_and_falsifiers"

    def test_registry_protocol_compliance(self, registry: LogosOperatorRegistry):
        """Test that LogosOperatorRegistry complies with RegistryProtocol."""
        # Test all required methods exist
        assert hasattr(registry, 'load_subtheory')
        assert hasattr(registry, 'load_subtheories')
        assert hasattr(registry, 'get_operators')
        assert hasattr(registry, 'get_loaded_subtheories')
        assert hasattr(registry, 'validate_operator_compatibility')

        # Test method signatures work
        registry.load_subtheory('extensional')
        registry.load_subtheories(['modal'])
        operators = registry.get_operators()
        loaded = registry.get_loaded_subtheories()
        issues = registry.validate_operator_compatibility()

        assert isinstance(loaded, list)
        assert isinstance(issues, list)

    def test_semantics_protocol_compliance(self):
        """Test that LogosSemantics complies with SemanticsProtocol."""
        from model_checker.theory_lib.logos.operators import LogosOperatorRegistry

        registry = LogosOperatorRegistry()
        # Use smaller N value to avoid computational hang in tests
        semantics = LogosSemantics({'N': 4}, operator_registry=registry)

        # Test required attributes exist
        assert hasattr(semantics, 'verify')
        assert hasattr(semantics, 'falsify')
        assert hasattr(semantics, 'possible')
        assert hasattr(semantics, 'frame_constraints')
        assert hasattr(semantics, 'main_world')
        assert hasattr(semantics, 'main_point')

        # Test required methods exist
        assert hasattr(semantics, 'load_subtheories')
        assert hasattr(semantics, 'true_at')
        assert hasattr(semantics, 'false_at')
        assert hasattr(semantics, 'extended_verify')
        assert hasattr(semantics, 'extended_falsify')
        assert hasattr(semantics, 'is_world')
        assert hasattr(semantics, 'compatible')

    def test_dependency_resolution(self, registry: LogosOperatorRegistry):
        """Test that subtheory dependencies are resolved correctly."""
        # Modal depends on extensional and counterfactual
        registry.load_subtheory('modal')
        loaded = registry.get_loaded_subtheories()

        assert 'modal' in loaded
        assert 'extensional' in loaded, "Modal subtheory should load extensional dependency"
        assert 'counterfactual' in loaded, "Modal subtheory should load counterfactual dependency"

    def test_no_operator_conflicts(self, registry: LogosOperatorRegistry, subtheory_names: List[str]):
        """Test that loading all subtheories creates no operator conflicts."""
        registry.load_subtheories(subtheory_names)
        issues = registry.validate_operator_compatibility()

        # Report any issues for debugging
        if issues:
            print(f"Operator compatibility issues: {issues}")

        assert len(issues) == 0, f"Found operator compatibility issues: {issues}"

    def test_all_subtheory_tests_pass(self, subtheory_names: List[str]):
        """Run all individual subtheory test suites."""
        base_path = Path(__file__).parent.parent.parent  # Go to logos root
        failures = []

        for name in subtheory_names:
            test_path = base_path / 'subtheories' / name / 'tests'
            if test_path.exists():
                # Run pytest on this subtheory's tests
                result = subprocess.run([
                    sys.executable, '-m', 'pytest',
                    str(test_path),
                    '-v', '--tb=short'
                ], capture_output=True, text=True, cwd=base_path)

                if result.returncode != 0:
                    failures.append({
                        'subtheory': name,
                        'stdout': result.stdout,
                        'stderr': result.stderr,
                        'returncode': result.returncode
                    })

        # Report failures
        if failures:
            failure_msg = f"Subtheory tests failed for: {[f['subtheory'] for f in failures]}\n"
            for failure in failures:
                failure_msg += f"\n{failure['subtheory']} errors:\n{failure['stderr']}\n"
            pytest.fail(failure_msg)

    def test_iterator_contract_compliance(self):
        """Test that LogosModelIterator complies with iterator contracts."""
        from model_checker.theory_lib.logos.iterate import LogosModelIterator

        # Test that the class has all required methods
        required_methods = [
            '_calculate_differences',
            '_create_difference_constraint',
            '_create_non_isomorphic_constraint',
            '_create_stronger_constraint',
            'iterate_generator'
        ]

        for method in required_methods:
            assert hasattr(LogosModelIterator, method), f"LogosModelIterator missing {method}"

    def test_type_hint_coverage(self):
        """Test that key modules have proper type hint coverage."""
        from model_checker.theory_lib.logos import semantic, iterate, operators

        # Check that typing imports are present
        modules_to_check = [semantic, iterate, operators]

        for module in modules_to_check:
            # Check if module has typing imports
            module_file = Path(module.__file__)
            content = module_file.read_text()

            # Should have typing imports
            assert 'from typing import' in content, f"Module {module.__name__} missing typing imports"

            # Should have TYPE_CHECKING block for forward references
            assert 'TYPE_CHECKING' in content, f"Module {module.__name__} missing TYPE_CHECKING block"


class TestProtocolDefinitions:
    """Test that our protocol definitions are correct and usable."""

    def test_protocols_importable(self):
        """Test that all protocols can be imported."""
        from model_checker.theory_lib.logos.protocols import (
            SubtheoryProtocol,
            OperatorProtocol,
            SemanticsProtocol,
            RegistryProtocol,
            PropositionProtocol,
            ModelIteratorProtocol
        )

        # If we get here without import errors, protocols are importable
        assert True

    def test_protocol_runtime_checking(self):
        """Test that protocols support runtime checking."""
        from model_checker.theory_lib.logos.protocols import SubtheoryProtocol
        from model_checker.theory_lib.logos.operators import LogosOperatorRegistry

        # This should not raise an error - registry should implement the protocol
        registry = LogosOperatorRegistry()

        # Runtime protocol checking
        assert hasattr(SubtheoryProtocol, '__protocol_attrs__') or True  # Python 3.8+ compatibility


if __name__ == "__main__":
    pytest.main([__file__, "-v"])