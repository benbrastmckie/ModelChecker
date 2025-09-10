"""Base protocol for output strategies."""

from typing import Protocol, Dict, Any, List, Optional


class IOutputStrategy(Protocol):
    """Protocol defining the interface for output save strategies.
    
    Output strategies determine when and how model checking results
    are saved to disk. Different strategies provide different workflows:
    - Batch: Accumulate all results and save at the end
    - Sequential: Save each result immediately
    - Interactive: Prompt user for each save decision
    """
    
    def should_save_immediately(self) -> bool:
        """Determine if output should be saved immediately.
        
        Returns:
            True if outputs should be saved as soon as they're generated,
            False if they should be accumulated for later saving
        """
        ...
    
    def accumulate(self, example_name: str, formatted_outputs: Dict[str, str]):
        """Accumulate formatted outputs for later saving.
        
        Used by strategies that don't save immediately (like batch mode).
        
        Args:
            example_name: Name of the example
            formatted_outputs: Dictionary mapping format names to formatted content
        """
        ...
    
    def prepare_directory(self, output_dir: str):
        """Prepare the output directory structure if needed.
        
        Some strategies may need special directory structures.
        
        Args:
            output_dir: Path to the base output directory
        """
        ...
    
    def finalize(self, save_callback) -> None:
        """Finalize the output process.
        
        Called at the end of processing to handle any accumulated outputs
        or perform cleanup tasks.
        
        Args:
            save_callback: Function to call for saving outputs
                          Signature: (example_name: str, outputs: Dict[str, str]) -> None
        """
        ...
    
    def get_file_path(self, output_dir: str, example_name: str, 
                     format_name: str, extension: str) -> str:
        """Get the file path for a specific output.
        
        Different strategies may organize files differently.
        
        Args:
            output_dir: Base output directory
            example_name: Name of the example
            format_name: Format being saved (markdown, json, notebook)
            extension: File extension
            
        Returns:
            Full path where the file should be saved
        """
        ...