"""Sequential save manager for user prompting."""

from typing import Optional
from .prompts import prompt_yes_no


class SequentialSaveManager:
    """Manages user prompting for sequential save decisions.
    
    This class handles all user interactions related to saving models,
    including prompting for individual saves and additional models.
    """
    
    def __init__(self, input_provider=None):
        """Initialize prompt manager.
        
        Args:
            input_provider: Optional input provider for testing
        """
        self.input_provider = input_provider
        self.saved_count = {}  # Track saves per example
        
    def should_save(self, example_name: str) -> bool:
        """Ask user if they want to save this model.
        
        Args:
            example_name: Name of the example to save
            
        Returns:
            True if user wants to save, False otherwise
        """
        return prompt_yes_no(
            f"\nSave model for {example_name}?",
            default=True
        )
    
    def should_find_more(self) -> bool:
        """Ask if user wants to find additional models.
        
        Returns:
            True if user wants more models, False otherwise
        """
        return prompt_yes_no(
            "Find additional models?",
            default=False
        )
    
    def get_next_model_number(self, example_name: str) -> int:
        """Get the next model number for an example.
        
        Args:
            example_name: Name of the example
            
        Returns:
            Next model number (1-based)
        """
        if example_name not in self.saved_count:
            self.saved_count[example_name] = 0
        self.saved_count[example_name] += 1
        return self.saved_count[example_name]
    
    def prompt_directory_change(self, output_dir: str) -> bool:
        """Ask if user wants to change to output directory.
        
        Args:
            output_dir: Path to the output directory
            
        Returns:
            True if user wants to change directory
        """
        print(f"\nAll models saved to: {output_dir}")
        print("To change directory, run:")
        print(f"  cd {output_dir}")
        
        return prompt_yes_no(
            "Change to output directory?",
            default=False
        )