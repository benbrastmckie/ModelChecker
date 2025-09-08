"""Test module imports and compatibility.

This test ensures that all imports work correctly after refactoring
and that the module structure is properly organized.
"""

import unittest


class TestModelsImports(unittest.TestCase):
    """Test that models package imports work correctly."""
    
    def test_package_import(self):
        """Test that models package can be imported."""
        import model_checker.models
        self.assertIsNotNone(model_checker.models)
    
    def test_submodule_imports(self):
        """Test that all submodules can be imported."""
        # Import existing modules
        import model_checker.models.semantic
        import model_checker.models.proposition
        import model_checker.models.constraints
        
        # Verify they exist and can be used
        from model_checker.models.semantic import SemanticDefaults
        from model_checker.models.proposition import PropositionDefaults
        from model_checker.models.constraints import ModelConstraints
        
        # Ensure classes are accessible
        self.assertIsNotNone(SemanticDefaults)
        self.assertIsNotNone(PropositionDefaults)
        self.assertIsNotNone(ModelConstraints)
        
        # TODO: Add imports for other modules as they are populated:
        # - structure (Phase 1.6)
        # - printing (Phase 1.6)
        # - analysis (Phase 1.6)


if __name__ == '__main__':
    unittest.main()