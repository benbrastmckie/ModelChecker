"""Prompted output strategy implementation."""

import os
from typing import Dict, Optional


class PromptedOutputStrategy:
    """Save outputs with user prompts for each model.
    
    This strategy prompts the user after each model to decide whether
    to save it, allowing selective output generation in sequential mode.
    """
    
    def __init__(self, sequential_manager=None):
        """Initialize prompted strategy.
        
        Args:
            sequential_manager: SequentialSaveManager instance for user prompts
        """
        self.sequential_manager = sequential_manager
        self.saved_models = {}  # Track what was saved per example
        
    def should_save_immediately(self) -> bool:
        """Prompted mode saves based on user decision.
        
        Returns:
            True - outputs are handled immediately (with user prompt)
        """
        return True
    
    def accumulate(self, example_name: str, formatted_outputs: Dict[str, str]):
        """Prompted mode doesn't accumulate (handles immediately).
        
        Args:
            example_name: Name of the example (unused)
            formatted_outputs: Formatted outputs (unused)
        """
        pass  # Not used in prompted mode
    
    def prepare_directory(self, output_dir: str):
        """Prompted mode creates directories per example as needed.
        
        Args:
            output_dir: Path to the base output directory
        """
        # Directories are created on-demand when user chooses to save
        pass
    
    def create_example_directory(self, output_dir: str, example_name: str) -> str:
        """Create directory for an example.
        
        Args:
            output_dir: Base output directory
            example_name: Name of the example
            
        Returns:
            Path to the created directory
        """
        example_dir = os.path.join(output_dir, example_name)
        os.makedirs(example_dir, exist_ok=True)
        return example_dir
    
    def track_save(self, example_name: str, model_num: int):
        """Track that a model was saved.
        
        Args:
            example_name: Name of the example
            model_num: Model number that was saved
        """
        if example_name not in self.saved_models:
            self.saved_models[example_name] = []
        self.saved_models[example_name].append(model_num)
    
    def finalize(self, save_callback) -> None:
        """Create summary of what was saved in prompted mode.
        
        Args:
            save_callback: Function to save the summary
        """
        if self.saved_models:
            # Create summary data
            summary = {
                'mode': 'sequential',
                'saved_models': self.saved_models,
                'total_examples': len(self.saved_models),
                'total_models': sum(len(models) for models in self.saved_models.values())
            }
            
            # Save summary via callback
            save_callback('summary', {'json': summary})
    
    def get_file_path(self, output_dir: str, example_name: str, 
                     format_name: str, extension: str, model_num: Optional[int] = None) -> str:
        """Get file path for prompted outputs.
        
        Prompted mode saves to example-specific directories with
        model numbers in the filename.
        
        Args:
            output_dir: Base output directory
            example_name: Name of the example
            format_name: Format being saved
            extension: File extension
            model_num: Optional model number for multiple models
            
        Returns:
            Path where the file should be saved
        """
        example_dir = os.path.join(output_dir, example_name)
        
        if model_num is not None:
            # Include model number in filename
            filename = f"MODEL_{model_num}.{extension}"
        else:
            # No model number
            filename = f"{example_name}.{extension}"
            
        return os.path.join(example_dir, filename)