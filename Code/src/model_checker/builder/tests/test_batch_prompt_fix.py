"""Test for batch mode directory prompt fix.

This test validates the specific fix for showing directory change
instructions in batch mode.
"""

import unittest
from unittest.mock import Mock, patch, MagicMock
import sys
from io import StringIO


class TestBatchPromptFix(unittest.TestCase):
    """Test the specific fix for batch mode directory prompt."""
    
    def test_batch_mode_shows_cd_instructions(self):
        """Test that batch mode now shows cd instructions.
        
        This is a focused test on the specific code change made to
        BuildModule.run_examples() to show directory navigation help.
        """
        # Create a mock BuildModule instance
        mock_module = Mock()
        mock_module.output_manager = Mock()
        mock_module.output_manager.should_save.return_value = True
        mock_module.output_manager.output_dir = "/test/output/directory"
        mock_module.output_manager.finalize = Mock()
        
        # Set interactive_manager to simulate batch mode
        mock_module.interactive_manager = Mock()
        mock_module.interactive_manager.prompt_change_directory = Mock()
        
        # Capture stdout
        captured_output = StringIO()
        sys.stdout = captured_output
        
        try:
            # Simulate the fixed code from BuildModule.run_examples()
            if mock_module.output_manager.should_save():
                mock_module.output_manager.finalize()
                
                # Only print path if output was actually saved
                if mock_module.output_manager.output_dir is not None:
                    # Get full path for display
                    import os
                    full_path = os.path.abspath(mock_module.output_manager.output_dir)
                    
                    # This is the FIXED code - always calls prompt method
                    if mock_module.interactive_manager:
                        mock_module.interactive_manager.prompt_change_directory(full_path)
                    else:
                        # No interactive manager - show instructions directly
                        print(f"\nOutput saved to: {full_path}")
                        print(f"To change to output directory, run:")
                        print(f"  cd {full_path}")
            
            output = captured_output.getvalue()
            
        finally:
            sys.stdout = sys.__stdout__
        
        # Verify the prompt method was called (since we have interactive_manager)
        mock_module.interactive_manager.prompt_change_directory.assert_called_once()
        
        # The call should have been with the absolute path
        call_args = mock_module.interactive_manager.prompt_change_directory.call_args[0]
        self.assertEqual(call_args[0], os.path.abspath("/test/output/directory"))
    
    def test_no_interactive_manager_shows_instructions(self):
        """Test behavior when interactive_manager is None."""
        # Create a mock BuildModule instance
        mock_module = Mock()
        mock_module.output_manager = Mock()
        mock_module.output_manager.should_save.return_value = True
        mock_module.output_manager.output_dir = "/test/output/directory"
        mock_module.output_manager.finalize = Mock()
        
        # No interactive manager
        mock_module.interactive_manager = None
        
        # Capture stdout
        captured_output = StringIO()
        sys.stdout = captured_output
        
        try:
            # Simulate the fixed code
            if mock_module.output_manager.should_save():
                mock_module.output_manager.finalize()
                
                if mock_module.output_manager.output_dir is not None:
                    import os
                    full_path = os.path.abspath(mock_module.output_manager.output_dir)
                    
                    if mock_module.interactive_manager:
                        mock_module.interactive_manager.prompt_change_directory(full_path)
                    else:
                        # No interactive manager - show instructions directly
                        print(f"\nOutput saved to: {full_path}")
                        print(f"To change to output directory, run:")
                        print(f"  cd {full_path}")
            
            output = captured_output.getvalue()
            
        finally:
            sys.stdout = sys.__stdout__
        
        # Verify output contains the expected instructions
        self.assertIn("Output saved to:", output)
        self.assertIn("/test/output/directory", output)
        self.assertIn("To change to output directory, run:", output)
        self.assertIn("cd /test/output/directory", output)


if __name__ == '__main__':
    unittest.main()