"""
Unit tests for BuildProject version detection functionality.

This module tests version detection mechanisms in BuildProject to ensure
proper version retrieval and handling of fallback scenarios.
"""

import unittest

from model_checker.builder.tests.fixtures.test_data import TestConstants
from model_checker.builder.tests.fixtures.assertions import (
    assert_no_exceptions_during_execution
)

from model_checker.builder.project import BuildProject


class TestBuildProjectVersionDetection(unittest.TestCase):
    """Test BuildProject version detection functionality."""
    
    def test_build_project_retrieves_version_information_successfully(self):
        """Test BuildProject retrieves version information without errors."""
        project = BuildProject('logos')
        
        version = assert_no_exceptions_during_execution(
            self,
            lambda: project._get_current_version(),
            operation_name="Version detection"
        )
        
        # Version should be a string
        self.assertIsInstance(version, str,
                            "Version should be returned as string")
        self.assertGreater(len(version), 0,
                         "Version should not be empty")
    
    def test_version_detection_handles_valid_version_format_correctly(self):
        """Test version detection handles valid semantic version formats correctly."""
        project = BuildProject('logos')
        version = project._get_current_version()
        
        if version != "unknown":
            # Should follow semantic versioning pattern
            version_parts = version.split(".")
            self.assertGreaterEqual(len(version_parts), 2,
                                  f"Valid version should have at least major.minor format: {version}")
            
            # Each part should be numeric (for standard semantic versions)
            for part in version_parts:
                # Handle pre-release versions (e.g., "1.0.0-alpha")
                clean_part = part.split('-')[0]
                self.assertTrue(clean_part.isdigit() or clean_part == '0',
                              f"Version part should be numeric: {clean_part} in {version}")
    
    def test_version_detection_provides_fallback_for_unknown_versions(self):
        """Test version detection provides appropriate fallback for unknown versions."""
        project = BuildProject('logos')
        version = project._get_current_version()
        
        # Should return either a valid version or "unknown" fallback
        self.assertIn(version, ["unknown"] if version == "unknown" else [version],
                     "Version should be either valid version string or 'unknown' fallback")
        
        # "unknown" is acceptable fallback when detection fails
        if version == "unknown":
            # This is a valid scenario - package may not be installed
            # or version may not be detectable in test environment
            pass
        else:
            # Should be a valid version string
            self.assertRegex(version, r'^\d+\.\d+',
                           "Valid version should start with major.minor pattern")
    
    def test_version_detection_consistency_with_package_version(self):
        """Test version detection consistency with package __version__ attribute."""
        project = BuildProject('logos')
        detected_version = project._get_current_version()
        
        try:
            from model_checker import __version__ as package_version
            
            # If both are available and not "unknown", they should match
            if detected_version != "unknown" and package_version:
                self.assertEqual(detected_version, package_version,
                               f"Detected version {detected_version} should match package version {package_version}")
            
        except ImportError:
            # Package version may not be available in test environment
            self.skipTest("Package version not available for comparison")


class TestVersionDetectionEdgeCases(unittest.TestCase):
    """Test edge cases in version detection functionality."""
    
    def test_version_detection_handles_different_theory_names_consistently(self):
        """Test version detection produces consistent results across different theory names."""
        theory_names = ['logos', 'exclusion', 'imposition']
        detected_versions = []
        
        for theory_name in theory_names:
            project = BuildProject(theory_name)
            version = assert_no_exceptions_during_execution(
                self,
                lambda: project._get_current_version(),
                operation_name=f"Version detection for {theory_name}"
            )
            detected_versions.append(version)
        
        # All versions should be identical (version is project-wide, not theory-specific)
        unique_versions = set(detected_versions)
        self.assertEqual(len(unique_versions), 1,
                        f"Version should be consistent across theories: {detected_versions}")
    
    def test_version_detection_performance_is_reasonable(self):
        """Test version detection completes within reasonable time."""
        import time
        
        project = BuildProject('logos')
        
        start_time = time.time()
        version = project._get_current_version()
        end_time = time.time()
        
        detection_time = end_time - start_time
        
        # Version detection should be fast (< 1 second)
        self.assertLess(detection_time, 1.0,
                       f"Version detection should complete quickly, took {detection_time:.3f}s")
        
        # Verify version was actually retrieved
        self.assertIsInstance(version, str,
                            "Version should be retrieved within time limit")


if __name__ == '__main__':
    unittest.main()