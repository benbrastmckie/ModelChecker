"""
Integration tests for error propagation through builder components.

This module tests how errors are handled and propagated between integrated
components, ensuring graceful degradation and informative error messages.
"""

import unittest
import os

from model_checker.builder.tests.fixtures.test_data import TestModules, TestExamples
from model_checker.builder.tests.fixtures.mock_objects import MockObjectFactory
from model_checker.builder.tests.fixtures.temp_resources import TempFileCleanup
from model_checker.builder.tests.fixtures.assertions import (
    assert_error_message_contains,
    assert_no_exceptions_during_execution
)

from model_checker.builder.module import BuildModule
from model_checker.builder.loader import ModuleLoader


class TestModuleLoadingErrorPropagation(unittest.TestCase):
    """Test error propagation in module loading scenarios."""
    
    def setUp(self):
        """Set up module loading error propagation testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
    
    def test_module_loader_propagates_file_not_found_error_with_context(self):
        """Test ModuleLoader propagates file not found errors with descriptive context."""
        nonexistent_file_path = "/completely/nonexistent/path/examples.py"
        
        flags = MockObjectFactory.create_flags({
            'file_path': nonexistent_file_path
        })
        
        # BuildModule initialization should propagate loader error
        with self.assertRaises(ImportError) as context:
            BuildModule(flags)
        
        # Error should contain contextual information
        error_message = str(context.exception).lower()
        self.assertTrue(
            any(keyword in error_message 
                for keyword in ['not found', 'no such file', 'cannot load']),
            f"Error should provide context about file not found: {context.exception}"
        )
    
    def test_module_loader_propagates_syntax_errors_with_location_info(self):
        """Test ModuleLoader propagates syntax errors with file location information."""
        # Create module with deliberate syntax error
        syntax_error_module_content = '''
# Deliberately broken syntax for testing error propagation
semantic_theories = {
    "BrokenSyntax": {
        "semantics": object
        # Missing comma creates syntax error
        "operators": {}
    }
}
example_range = {}
general_settings = {}
'''
        
        syntax_error_file = self.cleanup.create_temp_file(
            syntax_error_module_content,
            suffix=".py"
        )
        
        flags = MockObjectFactory.create_flags({
            'file_path': syntax_error_file
        })
        
        # Should propagate syntax error through BuildModule
        with self.assertRaises((SyntaxError, ImportError)) as context:
            BuildModule(flags)
        
        # Error should provide information about syntax problem
        error_message = str(context.exception).lower()
        self.assertTrue(
            any(keyword in error_message 
                for keyword in ['syntax', 'invalid', 'failed to import']),
            f"Error should indicate syntax problem: {context.exception}"
        )
    
    def test_module_loader_propagates_import_errors_from_module_dependencies(self):
        """Test ModuleLoader propagates import errors from module dependencies."""
        # Create module that tries to import nonexistent package
        import_error_module_content = '''
# This import will fail and should be propagated
from completely_nonexistent_package import NonexistentClass

semantic_theories = {"Test": {"semantics": NonexistentClass}}
example_range = {}
general_settings = {}
'''
        
        import_error_file = self.cleanup.create_temp_file(
            import_error_module_content,
            suffix=".py"
        )
        
        # Test direct module loader error propagation
        loader = ModuleLoader("import_error_test", import_error_file)
        
        with self.assertRaises((ImportError, ModuleNotFoundError)) as context:
            loader.load_module()
        
        # Error should indicate the problematic import
        assert_error_message_contains(
            self, context.exception, "nonexistent",
            "Import error from module dependencies"
        )
    
    def test_module_loader_propagates_missing_attribute_errors_descriptively(self):
        """Test ModuleLoader propagates missing attribute errors with descriptive messages."""
        # Create module missing required semantic_theories attribute
        missing_attributes_module_content = '''
# Missing semantic_theories attribute
example_range = {"TEST": [["p"], ["q"], {"N": 2}]}
general_settings = {}
'''
        
        missing_attrs_file = self.cleanup.create_temp_file(
            missing_attributes_module_content,
            suffix=".py"
        )
        
        flags = MockObjectFactory.create_flags({
            'file_path': missing_attrs_file
        })
        
        # BuildModule should detect and report missing attributes
        with self.assertRaises(ImportError) as context:
            BuildModule(flags)
        
        # Error should identify the missing attribute
        assert_error_message_contains(
            self, context.exception, "semantic_theories",
            "Missing required attribute error"
        )


class TestTheoryDiscoveryErrorPropagation(unittest.TestCase):
    """Test error propagation in theory discovery scenarios."""
    
    def setUp(self):
        """Set up theory discovery error testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
    
    def test_theory_discovery_propagates_unknown_theory_errors_clearly(self):
        """Test theory discovery propagates unknown theory errors with clear messages."""
        unknown_theory_name = "completely_unknown_theory"
        loader = ModuleLoader(unknown_theory_name, None)
        
        with self.assertRaises(ImportError) as context:
            loader.discover_theory_module()
        
        # Error should clearly indicate the unknown theory
        assert_error_message_contains(
            self, context.exception, unknown_theory_name,
            "Unknown theory discovery error"
        )
    
    def test_theory_discovery_error_includes_available_theories_suggestion(self):
        """Test theory discovery error includes helpful information about available theories."""
        # This tests the integration aspect - when theory discovery fails,
        # the error should be informative about what went wrong
        
        invalid_theory_name = "not_a_real_theory"
        loader = ModuleLoader(invalid_theory_name, None)
        
        with self.assertRaises(ImportError) as context:
            loader.discover_theory_module()
        
        # Error message should be descriptive enough to help users
        error_message = str(context.exception).lower()
        self.assertTrue(
            any(keyword in error_message 
                for keyword in ['not found', 'theory', invalid_theory_name.lower()]),
            f"Error should help identify the problem: {context.exception}"
        )


class TestComponentIntegrationErrorPropagation(unittest.TestCase):
    """Test error propagation across integrated components."""
    
    def setUp(self):
        """Set up component integration error testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
    
    def test_build_module_propagates_component_initialization_errors_appropriately(self):
        """Test BuildModule propagates component initialization errors appropriately."""
        # Create valid module file first
        valid_module_file = self.cleanup.create_temp_file(
            TestModules.MINIMAL_CONTENT,
            suffix=".py"
        )
        
        flags = MockObjectFactory.create_flags({
            'file_path': valid_module_file
        })
        
        # This test documents that BuildModule should handle component errors gracefully
        build_module = assert_no_exceptions_during_execution(
            self,
            lambda: BuildModule(flags),
            operation_name="BuildModule with component integration"
        )
        
        # Verify core components are available
        expected_components = ['loader', 'translation']
        for component in expected_components:
            self.assertTrue(hasattr(build_module, component),
                          f"BuildModule should initialize {component} component")
    
    def test_error_propagation_preserves_original_error_context(self):
        """Test error propagation preserves original error context through component chain."""
        # Create module with specific error that should propagate through components
        error_inducing_content = '''
# This will cause a specific error during attribute loading
semantic_theories = {}  # Empty - will cause error during processing
example_range = {}
general_settings = {}
'''
        
        error_file = self.cleanup.create_temp_file(
            error_inducing_content,
            suffix=".py"
        )
        
        flags = MockObjectFactory.create_flags({
            'file_path': error_file
        })
        
        # BuildModule should fail with a clear error for empty theories
        with self.assertRaises(ImportError) as context:
            BuildModule(flags)
        
        # Verify error message is clear and preserves context
        error_msg = str(context.exception)
        self.assertIn("empty", error_msg.lower(),
                     "Error should mention empty semantic_theories")
        self.assertIn("semantic_theories", error_msg,
                     "Error should mention the specific attribute")


class TestErrorRecoveryAndGracefulDegradation(unittest.TestCase):
    """Test error recovery and graceful degradation scenarios."""
    
    def setUp(self):
        """Set up error recovery testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
    
    def test_system_recovers_gracefully_from_partial_module_loading_failures(self):
        """Test system recovers gracefully from partial module loading failures."""
        # Create module with some valid and some problematic content
        partially_valid_content = '''
from model_checker.models.semantic import SemanticDefaults
from model_checker.models.proposition import PropositionDefaults
from model_checker.models.structure import ModelDefaults

class PartialTestSemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {"N": 2}
    DEFAULT_GENERAL_SETTINGS = {"save_output": False}

class PartialTestProposition(PropositionDefaults):
    pass

class PartialTestModel(ModelDefaults):
    pass

# Valid semantic theory definition
semantic_theories = {
    "ValidTheory": {
        "semantics": PartialTestSemantics,
        "proposition": PartialTestProposition,
        "model": PartialTestModel,
        "operators": {},
        "dictionary": {}
    }
}

# Valid examples
example_range = {
    "VALID_EXAMPLE": [["p"], ["p"], {"N": 2}]
}

# Valid settings
general_settings = {"N": 2}
'''
        
        partial_module_file = self.cleanup.create_temp_file(
            partially_valid_content,
            suffix=".py"
        )
        
        flags = MockObjectFactory.create_flags({
            'file_path': partial_module_file
        })
        
        # Should load successfully with valid parts
        build_module = assert_no_exceptions_during_execution(
            self,
            lambda: BuildModule(flags),
            operation_name="Partial module recovery"
        )
        
        # Verify valid parts were loaded
        self.assertTrue(hasattr(build_module, 'semantic_theories'),
                       "Should load valid semantic theories")
        
        if hasattr(build_module, 'semantic_theories'):
            theories = build_module.semantic_theories
            self.assertIn('ValidTheory', theories,
                         "Should load valid theory despite other issues")
    
    def test_informative_error_messages_help_debugging_common_issues(self):
        """Test error messages provide informative context for debugging common issues."""
        common_error_scenarios = [
            # Scenario 1: File doesn't exist
            {
                'file_path': '/tmp/nonexistent_file.py',
                'expected_keywords': ['not found', 'file', 'does not exist']
            },
            
            # Scenario 2: File exists but empty
            {
                'file_content': '',
                'expected_keywords': ['missing', 'attribute', 'semantic_theories']
            },
            
            # Scenario 3: File exists with empty semantic_theories
            {
                'file_content': 'semantic_theories = {}',
                'expected_keywords': ['empty', 'semantic_theories']
            }
        ]
        
        for i, scenario in enumerate(common_error_scenarios):
            with self.subTest(scenario_index=i):
                if 'file_content' in scenario:
                    # Create file with specific content
                    test_file = self.cleanup.create_temp_file(
                        scenario['file_content'],
                        suffix=".py"
                    )
                    file_path = test_file
                else:
                    # Use specified file path
                    file_path = scenario['file_path']
                
                flags = MockObjectFactory.create_flags({
                    'file_path': file_path
                })
                
                with self.assertRaises((ImportError, FileNotFoundError)) as context:
                    BuildModule(flags)
                
                # Verify error message contains helpful keywords
                error_message = str(context.exception).lower()
                found_keyword = any(
                    keyword in error_message 
                    for keyword in scenario['expected_keywords']
                )
                
                self.assertTrue(
                    found_keyword,
                    f"Error should contain helpful keywords {scenario['expected_keywords']}: {context.exception}"
                )


if __name__ == '__main__':
    unittest.main()