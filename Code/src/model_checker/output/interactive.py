"""Interactive save workflow manager."""

import os
from typing import Optional, Dict

from .prompts import prompt_yes_no, prompt_choice
from .input_provider import InputProvider


class InteractiveSaveManager:
    """Manages interactive save workflow for model checking results.
    
    This class handles user prompts for saving models, finding additional
    models, and navigating to output directories.
    """
    
    def __init__(self, input_provider: InputProvider):
        """Initialize the interactive save manager.
        
        Args:
            input_provider: Provider for user input (required)
        """
        self.input_provider = input_provider
        self.mode: Optional[str] = None  # 'batch' or 'interactive'
        self.current_example: Optional[str] = None
        self.model_count: Dict[str, int] = {}  # Track models per example
        
    def set_mode(self, mode: str):
        """Set the save mode directly.
        
        Args:
            mode: Either 'batch' or 'interactive'
        """
        if mode not in ['batch', 'interactive']:
            raise ValueError(f"Invalid mode: {mode}. Must be 'batch' or 'interactive'")
        self.mode = mode
        
    def prompt_save_mode(self) -> str:
        """Prompt user to select save mode.
        
        Returns:
            str: Selected mode ('batch' or 'interactive')
        """
        # Use input provider for testable input
        response = self.input_provider.get_input("Save all examples (a) or run in sequence (s)? ").strip().lower()
        
        # Handle response
        if response == 'a':
            self.mode = 'batch'
        elif response == 's':
            self.mode = 'interactive'
        else:
            # Default to batch if invalid input
            print("Invalid choice. Defaulting to save all.")
            self.mode = 'batch'
            
        return self.mode
        
    def prompt_save_model(self, example_name: str) -> bool:
        """Prompt whether to save current model.
        
        Args:
            example_name: Name of the current example
            
        Returns:
            bool: True to save, False to skip
        """
        # Always save in batch mode
        if self.mode != 'interactive':
            return True
            
        return prompt_yes_no(
            f"\nSave model for {example_name}?",
            default=True
        )
        
    def prompt_find_more_models(self) -> bool:
        """Prompt whether to find additional models.
        
        Returns:
            bool: True to find more, False to continue
        """
        # Never iterate in batch mode (handled elsewhere)
        if self.mode != 'interactive':
            return False
            
        return prompt_yes_no(
            "Find additional models?",
            default=False
        )
        
    def prompt_change_directory(self, output_path: str) -> bool:
        """Prompt whether to change to output directory.
        
        Args:
            output_path: Full path to output directory
            
        Returns:
            bool: True if user wants to change directory
        """
        # Display full path
        print(f"\nAll models saved to: {output_path}")
        
        # Ask if they want to cd
        result = prompt_yes_no(
            "Change to output directory?",
            default=False
        )
        
        if result:
            print("To change directory, run:")
            print(f"  cd {output_path}")
            
        return result
        
    def get_next_model_number(self, example_name: str) -> int:
        """Get the next model number for an example.
        
        Args:
            example_name: Name of the example
            
        Returns:
            int: Next model number (1-based)
        """
        if example_name not in self.model_count:
            self.model_count[example_name] = 0
            
        self.model_count[example_name] += 1
        return self.model_count[example_name]
        
    def reset_for_new_example(self, example_name: str) -> None:
        """Reset state for a new example.
        
        Args:
            example_name: Name of the new example
        """
        self.current_example = example_name
        # Model count persists across examples
        
    def is_interactive(self) -> bool:
        """Check if in interactive mode.
        
        Returns:
            bool: True if interactive mode is active
        """
        return self.mode == 'interactive'