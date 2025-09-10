"""Sequential output strategy implementation."""

import os
from typing import Dict
from ..constants import SEQUENTIAL_SINGLE, SEQUENTIAL_MULTIPLE


class SequentialOutputStrategy:
    """Save outputs immediately as they are generated.
    
    This strategy writes each output to disk as soon as it's formatted,
    either to individual files or appending to a single file based on
    configuration.
    """
    
    def __init__(self, sequential_files: str = SEQUENTIAL_MULTIPLE):
        """Initialize sequential strategy.
        
        Args:
            sequential_files: 'single' to append to one file,
                            'multiple' for separate files per example
        """
        self.sequential_files = sequential_files
        self.saved_count = 0
        
    def should_save_immediately(self) -> bool:
        """Sequential mode always saves immediately.
        
        Returns:
            True - save outputs as soon as they're generated
        """
        return True
    
    def accumulate(self, example_name: str, formatted_outputs: Dict[str, str]):
        """Sequential mode doesn't accumulate (saves immediately).
        
        This method is not used in sequential mode but is required
        by the protocol.
        
        Args:
            example_name: Name of the example (unused)
            formatted_outputs: Formatted outputs (unused)
        """
        pass  # Not used in sequential mode
    
    def prepare_directory(self, output_dir: str):
        """Create sequential subdirectory if using multiple files.
        
        Args:
            output_dir: Path to the base output directory
        """
        if self.sequential_files == SEQUENTIAL_MULTIPLE:
            sequential_dir = os.path.join(output_dir, 'sequential')
            os.makedirs(sequential_dir, exist_ok=True)
    
    def finalize(self, save_callback) -> None:
        """No finalization needed for sequential mode.
        
        Since outputs are saved immediately, there's nothing to finalize.
        
        Args:
            save_callback: Save callback (unused in sequential mode)
        """
        pass  # Nothing to finalize - already saved
    
    def get_file_path(self, output_dir: str, example_name: str, 
                     format_name: str, extension: str) -> str:
        """Get file path for sequential outputs.
        
        Args:
            output_dir: Base output directory
            example_name: Name of the example
            format_name: Format being saved
            extension: File extension
            
        Returns:
            Path where the file should be saved
        """
        if self.sequential_files == SEQUENTIAL_MULTIPLE:
            # Save to individual files in sequential subdirectory
            sequential_dir = os.path.join(output_dir, 'sequential')
            filename = f"{example_name}.{extension}"
            return os.path.join(sequential_dir, filename)
        else:
            # Append to single file
            filename_map = {
                'markdown': 'EXAMPLES.md',
                'json': 'MODELS.json'
            }
            filename = filename_map.get(format_name, f"output.{extension}")
            return os.path.join(output_dir, filename)