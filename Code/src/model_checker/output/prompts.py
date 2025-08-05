"""Interactive prompt utilities for user input."""

import sys
from typing import List, Optional


def prompt_yes_no(message: str, default: bool = False) -> bool:
    """Prompt user for yes/no response.
    
    Args:
        message: The prompt message to display
        default: Default value if user presses Enter (False = no, True = yes)
        
    Returns:
        bool: True for yes, False for no
    """
    # Format prompt with default indicator
    if default:
        prompt = f"{message} (Y/n): "
        default_str = 'y'
    else:
        prompt = f"{message} (y/N): "
        default_str = 'n'
    
    while True:
        try:
            # Show prompt and get input
            response = input(prompt).strip().lower()
            
            # Handle empty input (use default)
            if not response:
                response = default_str
            
            # Check for affirmative responses
            if response in ['y', 'yes']:
                return True
            elif response in ['n', 'no']:
                return False
            else:
                print("Please answer 'y' or 'n'")
                
        except KeyboardInterrupt:
            # Handle Ctrl+C gracefully
            print("\nCancelled")
            return False
        except EOFError:
            # Handle end of input
            print("\nNo input available")
            return False


def prompt_choice(message: str, choices: List[str]) -> Optional[str]:
    """Prompt user to select from a list of choices.
    
    Args:
        message: The prompt message to display
        choices: List of string choices
        
    Returns:
        str: Selected choice, or None if cancelled
        
    Raises:
        ValueError: If choices list is empty
    """
    if not choices:
        raise ValueError("No choices provided")
    
    # Auto-select if only one choice
    if len(choices) == 1:
        return choices[0]
    
    # Display message and choices
    print(message)
    for i, choice in enumerate(choices, 1):
        print(f"  {i}. {choice}")
    
    # Create prompt showing valid range
    prompt = f"Choice (1-{len(choices)}): "
    
    while True:
        try:
            response = input(prompt).strip()
            
            # Try to parse as number
            try:
                choice_num = int(response)
                if 1 <= choice_num <= len(choices):
                    return choices[choice_num - 1]
            except ValueError:
                pass
            
            # Try to match by first letter
            response_lower = response.lower()
            for choice in choices:
                if choice.lower().startswith(response_lower):
                    return choice
            
            # Invalid input
            print(f"Please enter a number 1-{len(choices)} or the first letter of your choice")
            
        except KeyboardInterrupt:
            print("\nCancelled")
            return None
        except EOFError:
            print("\nNo input available")
            return None