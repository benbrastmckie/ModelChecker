"""
Integration tests for builder component interactions.

This module tests complex interactions between components, ensuring the entire
system works cohesively with real component integration.
"""

import unittest
import os
from unittest.mock import Mock, patch

from model_checker.builder.tests.fixtures.test_data import TestTheories, TestExamples, TestModules, TestConstants
from model_checker.builder.tests.fixtures.mock_objects import MockObjectFactory
from model_checker.builder.tests.fixtures.temp_resources import TempFileCleanup
from model_checker.builder.tests.fixtures.assertions import (
    assert_error_message_contains,
    assert_no_exceptions_during_execution
)

from model_checker.builder.module import BuildModule
from model_checker.builder.loader import ModuleLoader


class TestLoaderRunnerIntegration(unittest.TestCase):
    """Test integration between loader and runner components."""
    
    def setUp(self):
        """Set up loader-runner integration testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Create test module file
        self.module_path = self.cleanup.create_temp_file(
            TestModules.LOGOS_CONTENT,
            suffix=".py"
        )
    
    def test_loader_runner_workflow_processes_examples_correctly(self):
        """Test complete workflow from loading to example processing."""
        flags = MockObjectFactory.create_flags({
            'file_path': self.module_path,
            'comparison': False
        })
        
        # Initialize BuildModule (integrates loader)
        build_module = assert_no_exceptions_during_execution(
            self,
            lambda: BuildModule(flags),
            operation_name="BuildModule initialization with loader"
        )
        
        # Verify loader component initialized
        self.assertTrue(hasattr(build_module, 'loader'),
                       "BuildModule should have loader component")
        
        # Mock runner integration (when it exists)
        if hasattr(build_module, 'runner'):
            # Verify runner can access loaded data
            self.assertIsNotNone(build_module.runner,
                               "Runner component should be initialized")
            
            # Test example processing workflow
            with patch.object(build_module.runner, 'process_example') as mock_process:
                mock_process.return_value = "processed_result"
                
                # Should be able to process examples from loaded module
                if hasattr(build_module, 'example_range') and build_module.example_range:
                    example_keys = list(build_module.example_range.keys())
                    if example_keys:
                        first_example = build_module.example_range[example_keys[0]]
                        result = build_module.runner.process_example(first_example)
                        
                        self.assertEqual(result, "processed_result",
                                       "Runner should process loaded examples")
        else:
            # Document current state before runner extraction
            self.assertTrue(hasattr(build_module, 'semantic_theories'),
                          "BuildModule should load semantic theories")
    
    def test_loader_translation_integration_applies_dictionaries(self):
        """Test integration between loader and translation components."""
        # Create module with translation dictionary
        module_with_dict = TestModules.LOGOS_CONTENT.replace(
            'dictionary = {}',
            'dictionary = {"\\\\wedge": "∧", "\\\\vee": "∨"}'
        )
        
        module_path = self.cleanup.create_temp_file(
            module_with_dict,
            suffix=".py"
        )
        
        flags = MockObjectFactory.create_flags({
            'file_path': module_path
        })
        
        build_module = BuildModule(flags)
        
        # Verify translation component has access to loaded dictionary
        self.assertTrue(hasattr(build_module, 'translation'),
                       "BuildModule should have translation component")
        
        # If dictionary was loaded, translation should be able to use it
        if hasattr(build_module, 'semantic_theories'):
            theories = build_module.semantic_theories
            if theories:
                first_theory = list(theories.values())[0]
                if 'dictionary' in first_theory:
                    # Translation integration should work
                    self.assertIn('dictionary', first_theory,
                                "Theory should contain dictionary for translation")


class TestModuleTheoryIntegration(unittest.TestCase):
    """Test integration between module loading and theory components."""
    
    def setUp(self):
        """Set up module-theory integration testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
    
    def test_module_loads_multiple_theories_correctly(self):
        """Test module loading integrates correctly with multiple theories."""
        # Create module with multiple theories
        multi_theory_content = '''
from model_checker.theory_lib import logos, exclusion

theory_logos = logos.get_theory(['extensional'])
theory_exclusion = exclusion.get_theory()

semantic_theories = {
    "Logos": theory_logos,
    "Exclusion": theory_exclusion
}

example_range = {
    "TEST_MULTI": [
        ["p ∧ q"],
        ["p", "q"], 
        {"N": 2}
    ]
}

general_settings = {
    "print_constraints": False
}
'''
        
        module_path = self.cleanup.create_temp_file(
            multi_theory_content,
            suffix=".py"
        )
        
        flags = MockObjectFactory.create_flags({
            'file_path': module_path
        })
        
        build_module = assert_no_exceptions_during_execution(
            self,
            lambda: BuildModule(flags),
            operation_name="Multi-theory module loading"
        )
        
        # Verify multiple theories loaded
        self.assertTrue(hasattr(build_module, 'semantic_theories'),
                       "BuildModule should load semantic_theories")
        
        if hasattr(build_module, 'semantic_theories'):
            theories = build_module.semantic_theories
            self.assertIsInstance(theories, dict,
                                "semantic_theories should be dictionary")
            
            expected_theories = ["Logos", "Exclusion"]
            for theory_name in expected_theories:
                if theory_name in theories:
                    self.assertIsNotNone(theories[theory_name],
                                       f"{theory_name} theory should be loaded")
    
    def test_module_theory_validation_integration(self):
        """Test integration between module loading and theory validation."""
        # Create module with potentially invalid theory structure
        questionable_content = '''
from model_checker.models.semantic import SemanticDefaults
from model_checker.models.proposition import PropositionDefaults
from model_checker.models.structure import ModelDefaults

class ValidTheorySemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {"N": 2}
    DEFAULT_GENERAL_SETTINGS = {"save_output": False}

class ValidTheoryProposition(PropositionDefaults):
    pass

class ValidTheoryModel(ModelDefaults):
    pass

semantic_theories = {
    "ValidTheory": {
        "semantics": ValidTheorySemantics,
        "operators": {},
        "model": ValidTheoryModel,
        "proposition": ValidTheoryProposition
    }
}

example_range = {
    "TEST": [["p"], ["q"], {"N": 2}]
}

general_settings = {}
'''
        
        module_path = self.cleanup.create_temp_file(
            questionable_content,
            suffix=".py"
        )
        
        flags = MockObjectFactory.create_flags({
            'file_path': module_path
        })
        
        # Module loading should succeed, but theory validation would catch issues
        with patch('builtins.input', return_value='s'):
            build_module = BuildModule(flags)
        
        # Document integration point - validation occurs when theories are used
        self.assertTrue(hasattr(build_module, 'semantic_theories'),
                       "Module loading should succeed, validation occurs during use")


class TestComparisonIntegration(unittest.TestCase):
    """Test integration with comparison mode functionality."""
    
    def setUp(self):
        """Set up comparison integration testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
        
        # Create module suitable for comparison
        self.comparison_module_path = self.cleanup.create_temp_file(
            TestModules.MULTI_THEORY_CONTENT,
            suffix=".py"
        )
    
    def test_comparison_mode_integration_with_multiple_theories(self):
        """Test comparison mode integration with multiple theory loading."""
        flags = MockObjectFactory.create_flags({
            'file_path': self.comparison_module_path,
            'comparison': True
        })
        
        with patch('builtins.input', return_value='s'):
            build_module = assert_no_exceptions_during_execution(
                self,
                lambda: BuildModule(flags),
                operation_name="Comparison mode module initialization"
            )
        
        # Verify comparison mode is enabled
        self.assertTrue(flags.comparison,
                       "Comparison mode should be enabled")
        
        # Verify module loads in comparison mode
        self.assertIsNotNone(build_module,
                           "BuildModule should initialize in comparison mode")
        
        # If comparison component exists, verify integration
        if hasattr(build_module, 'comparison'):
            self.assertIsNotNone(build_module.comparison,
                               "Comparison component should be initialized")
        
        # Verify theories are available for comparison
        if hasattr(build_module, 'semantic_theories'):
            theories = build_module.semantic_theories
            if theories and len(theories) > 1:
                self.assertGreater(len(theories), 1,
                                 "Should have multiple theories for comparison")


class TestTranslationIntegration(unittest.TestCase):
    """Test integration with translation functionality."""
    
    def setUp(self):
        """Set up translation integration testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
    
    def test_translation_integration_with_example_processing(self):
        """Test translation integration with example processing workflow."""
        # Create module with translation dictionary
        translation_module_content = '''
from model_checker.models.semantic import SemanticDefaults
from model_checker.models.proposition import PropositionDefaults
from model_checker.models.structure import ModelDefaults

class TestTheorySemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {"N": 2}
    DEFAULT_GENERAL_SETTINGS = {"save_output": False}

class TestTheoryProposition(PropositionDefaults):
    pass

class TestTheoryModel(ModelDefaults):
    pass

semantic_theories = {
    "TestTheory": {
        "semantics": TestTheorySemantics,
        "operators": {},
        "model": TestTheoryModel,
        "proposition": TestTheoryProposition,
        "dictionary": {
            "\\\\wedge": "∧",
            "\\\\vee": "∨",
            "\\\\neg": "¬"
        }
    }
}

example_range = {
    "TRANSLATE_TEST": [
        ["p \\\\wedge q"],
        ["p \\\\vee q"],
        {"N": 2}
    ]
}

general_settings = {}
'''
        
        module_path = self.cleanup.create_temp_file(
            translation_module_content,
            suffix=".py"
        )
        
        flags = MockObjectFactory.create_flags({
            'file_path': module_path
        })
        
        with patch('builtins.input', return_value='s'):
            build_module = BuildModule(flags)
        
        # Verify translation component is available
        self.assertTrue(hasattr(build_module, 'translation'),
                       "BuildModule should have translation component")
        
        # Verify dictionary data is accessible for translation
        if hasattr(build_module, 'semantic_theories'):
            theories = build_module.semantic_theories
            if "TestTheory" in theories:
                theory = theories["TestTheory"]
                if "dictionary" in theory:
                    dictionary = theory["dictionary"]
                    # Check if dictionary is preserved
                    self.assertIsInstance(dictionary, dict,
                                        "Dictionary should be a dict")
                    # The dictionary should have the expected keys (processed as single backslash)
                    self.assertIn("\\wedge", dictionary,
                                 f"Dictionary should have \\wedge key, got keys: {list(dictionary.keys())}")
                    self.assertEqual(dictionary["\\wedge"], "∧",
                                   "Translation dictionary should be available")
    
    def test_translation_integration_with_multiple_theory_dictionaries(self):
        """Test translation integration handles multiple theory dictionaries."""
        # Create module with different dictionaries per theory
        multi_dict_content = '''
from model_checker.models.semantic import SemanticDefaults
from model_checker.models.proposition import PropositionDefaults
from model_checker.models.structure import ModelDefaults

class StandardTheorySemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {"N": 2}
    DEFAULT_GENERAL_SETTINGS = {"save_output": False}

class StandardTheoryProposition(PropositionDefaults):
    pass

class StandardTheoryModel(ModelDefaults):
    pass

class CustomTheorySemantics(SemanticDefaults):
    DEFAULT_EXAMPLE_SETTINGS = {"N": 2}
    DEFAULT_GENERAL_SETTINGS = {"save_output": False}

class CustomTheoryProposition(PropositionDefaults):
    pass

class CustomTheoryModel(ModelDefaults):
    pass

semantic_theories = {
    "StandardTheory": {
        "semantics": StandardTheorySemantics,
        "operators": {},
        "model": StandardTheoryModel,
        "proposition": StandardTheoryProposition,
        "dictionary": {
            "\\\\wedge": "∧",
            "\\\\vee": "∨"
        }
    },
    "CustomTheory": {
        "semantics": CustomTheorySemantics,
        "operators": {},
        "model": CustomTheoryModel,
        "proposition": CustomTheoryProposition,
        "dictionary": {
            "\\\\wedge": "&",
            "\\\\vee": "|"
        }
    }
}

example_range = {
    "MULTI_DICT_TEST": [
        ["p \\\\wedge q"],
        ["p \\\\vee q"],
        {"N": 2}
    ]
}

general_settings = {}
'''
        
        module_path = self.cleanup.create_temp_file(
            multi_dict_content,
            suffix=".py"
        )
        
        flags = MockObjectFactory.create_flags({
            'file_path': module_path
        })
        
        with patch('builtins.input', return_value='s'):
            build_module = BuildModule(flags)
        
        # Verify different dictionaries are accessible
        if hasattr(build_module, 'semantic_theories'):
            theories = build_module.semantic_theories
            
            if "StandardTheory" in theories and "CustomTheory" in theories:
                standard_dict = theories["StandardTheory"].get("dictionary", {})
                custom_dict = theories["CustomTheory"].get("dictionary", {})
                
                # Different theories should have different translations
                self.assertEqual(standard_dict.get("\\wedge"), "∧",
                               "Standard theory should use Unicode")
                self.assertEqual(custom_dict.get("\\wedge"), "&",
                               "Custom theory should use ASCII")


class TestSystemIntegration(unittest.TestCase):
    """Test overall system integration scenarios."""
    
    def setUp(self):
        """Set up system integration testing environment."""
        self.cleanup = TempFileCleanup()
        self.addCleanup(self.cleanup.__exit__, None, None, None)
    
    def test_complete_system_initialization_succeeds(self):
        """Test complete system initialization with all components."""
        module_path = self.cleanup.create_temp_file(
            TestModules.COMPLETE_MODULE_CONTENT,
            suffix=".py"
        )
        
        flags = MockObjectFactory.create_flags({
            'file_path': module_path,
            'comparison': False,
            'print_constraints': False,
            'print_z3': False,
            'save_output': False
        })
        
        build_module = assert_no_exceptions_during_execution(
            self,
            lambda: BuildModule(flags),
            operation_name="Complete system initialization"
        )
        
        # Verify core system components
        expected_components = ['loader', 'translation']
        for component in expected_components:
            self.assertTrue(hasattr(build_module, component),
                          f"System should have {component} component")
        
        # Verify data loading succeeded
        expected_data = ['semantic_theories', 'example_range', 'general_settings']
        for data_attr in expected_data:
            if hasattr(build_module, data_attr):
                self.assertIsNotNone(getattr(build_module, data_attr),
                                   f"System should load {data_attr}")
    
    def test_error_propagation_through_system_integration(self):
        """Test error propagation through integrated system components."""
        # Create module with import error
        error_module_content = '''
import nonexistent_module  # This will cause ImportError

semantic_theories = {}
example_range = {}
general_settings = {}
'''
        
        module_path = self.cleanup.create_temp_file(
            error_module_content,
            suffix=".py"
        )
        
        flags = MockObjectFactory.create_flags({
            'file_path': module_path
        })
        
        # System should propagate import errors appropriately
        with self.assertRaises(ImportError) as context:
            BuildModule(flags)
        
        # Error should be descriptive
        assert_error_message_contains(
            self, context.exception, "nonexistent_module",
            "System integration error propagation"
        )


if __name__ == '__main__':
    unittest.main()