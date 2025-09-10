"""Batch output strategy implementation."""

import os
from typing import Dict, List, Tuple
from ..constants import DEFAULT_MARKDOWN_FILE, DEFAULT_JSON_FILE


class BatchOutputStrategy:
    """Accumulate all outputs and save them at the end.
    
    This strategy collects all formatted outputs in memory and writes
    them to consolidated files when finalize() is called. This is the
    default mode for non-interactive execution.
    """
    
    def __init__(self):
        """Initialize batch strategy with empty accumulator."""
        self.accumulated_outputs: List[Tuple[str, Dict[str, str]]] = []
        
    def should_save_immediately(self) -> bool:
        """Batch mode never saves immediately.
        
        Returns:
            False - always accumulate for later saving
        """
        return False
    
    def accumulate(self, example_name: str, formatted_outputs: Dict[str, str]):
        """Add outputs to the accumulator.
        
        Args:
            example_name: Name of the example
            formatted_outputs: Dictionary mapping format names to formatted content
        """
        self.accumulated_outputs.append((example_name, formatted_outputs))
    
    def prepare_directory(self, output_dir: str):
        """Batch mode doesn't need special directory structure.
        
        Args:
            output_dir: Path to the base output directory (unused)
        """
        pass  # No special directory structure needed
    
    def finalize(self, save_callback) -> None:
        """Save all accumulated outputs to consolidated files.
        
        In batch mode, we combine all outputs into single files:
        - EXAMPLES.md for all markdown content
        - MODELS.json for all JSON data
        - NOTEBOOK.ipynb for all notebook cells (via separate generator)
        
        Args:
            save_callback: Function to save the consolidated outputs
        """
        if not self.accumulated_outputs:
            return
            
        # Combine outputs by format
        combined_outputs = {
            'markdown': [],
            'json': []
        }
        
        for example_name, outputs in self.accumulated_outputs:
            for format_name, content in outputs.items():
                if format_name in combined_outputs:
                    combined_outputs[format_name].append(content)
        
        # Pass combined outputs to save callback
        # The callback will handle joining and saving appropriately
        save_callback('batch_combined', combined_outputs)
    
    def get_file_path(self, output_dir: str, example_name: str, 
                     format_name: str, extension: str) -> str:
        """Get file path for batch outputs.
        
        Batch mode uses consolidated files regardless of example name.
        
        Args:
            output_dir: Base output directory
            example_name: Name of the example (ignored in batch mode)
            format_name: Format being saved
            extension: File extension
            
        Returns:
            Path to the consolidated file for this format
        """
        # Map format names to default filenames
        filename_map = {
            'markdown': DEFAULT_MARKDOWN_FILE,
            'json': DEFAULT_JSON_FILE
        }
        
        filename = filename_map.get(format_name, f"output.{extension}")
        return os.path.join(output_dir, filename)