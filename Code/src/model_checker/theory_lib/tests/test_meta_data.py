"""
Tests for the metadata management system.

This module contains tests for the theory_lib metadata functionality,
including version tracking, license file generation, and citation management.
"""

import os
import pytest
import tempfile
import shutil
from unittest import mock

# Since the test_package.py sets up PYTHONPATH properly, we can use regular imports
from model_checker.theory_lib.meta_data import (
    update_all_theory_versions,
    create_all_license_files,
    create_all_citation_files,
    verify_metadata_consistency,
    print_metadata_report
)

from model_checker.utils import (
    get_model_checker_version,
    get_theory_version
)

class TestMetadataSystem:
    """Test suite for the metadata management system."""
    
    @pytest.fixture
    def temp_theories(self):
        """Create temporary theory directories for testing."""
        # Create a temporary directory to simulate theory directories
        temp_dir = tempfile.mkdtemp()
        
        # Create test theory directories
        for theory_name in ["test_theory1", "test_theory2"]:
            theory_dir = os.path.join(temp_dir, theory_name)
            os.makedirs(theory_dir, exist_ok=True)
            
            # Create __init__.py file
            with open(os.path.join(theory_dir, "__init__.py"), "w") as f:
                f.write('"""Test theory for metadata tests."""\n\n__version__ = "0.1.0"\n')
        
        yield temp_dir
        
        # Clean up
        shutil.rmtree(temp_dir)
    
    def test_version_utilities(self):
        """Test version utility functions."""
        # Test getting model_checker version
        version = get_model_checker_version()
        assert version is not None
        assert isinstance(version, str)
        
        # Get theory version for a known theory
        # This test may be fragile if the default theory version changes
        theory_version = get_theory_version("default")
        assert theory_version is not None
        assert isinstance(theory_version, str)
    
    def test_verification(self):
        """Test metadata verification functionality."""
        # Verify metadata consistency 
        result = verify_metadata_consistency()
        
        # Basic checks
        assert result is not None
        assert isinstance(result, dict)
        assert "default" in result
        
        # Check structure
        theory_data = result["default"]
        assert "version" in theory_data
        assert "license" in theory_data
        assert "citation" in theory_data
        
        # Check version info
        assert theory_data["version"]["found"] is True
        assert theory_data["version"]["value"] is not None
        
    @mock.patch('sys.stdout')  # Redirect stdout to prevent output during tests
    def test_print_report(self, mock_stdout):
        """Test report printing functionality."""
        # This should run without errors
        print_metadata_report()
        
        # Verify that output was captured
        assert mock_stdout.write.called
    
    @pytest.mark.parametrize(
        "theory_name", 
        ["default", "exclusion", "imposition", "bimodal"]
    )
    def test_theory_version_format(self, theory_name):
        """Test that theory versions follow the expected format."""
        # Get the version
        version = get_theory_version(theory_name)
        
        # Check format (should be semver: major.minor.patch)
        import re
        assert re.match(r"^\d+\.\d+\.\d+$", version) is not None, \
            f"Theory '{theory_name}' version '{version}' does not follow semver format"

    def test_metadata_files_exist(self):
        """Test that all theories have required metadata files."""
        # Get verification results
        result = verify_metadata_consistency()
        
        # Check that all theories have licenses and citations
        for theory_name, theory_data in result.items():
            assert theory_data["license"]["found"], \
                f"Theory '{theory_name}' is missing LICENSE.md file"
            assert theory_data["citation"]["found"], \
                f"Theory '{theory_name}' is missing CITATION.md file"
            assert theory_data["version"]["found"], \
                f"Theory '{theory_name}' is missing version information"
            assert theory_data["version"]["model_checker_version_found"], \
                f"Theory '{theory_name}' is missing model_checker_version information"

# Add more tests here as needed for specific metadata functionality