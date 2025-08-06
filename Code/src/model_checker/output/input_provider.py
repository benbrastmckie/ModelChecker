"""Input provider abstraction for testable user input."""

from typing import List, Union


class InputProvider:
    """Base class for input providers.
    
    This abstraction enables proper testing by allowing input() calls
    to be mocked during tests while using real console input in production.
    """
    
    def get_input(self, prompt: str) -> str:
        """Get input from the user.
        
        Args:
            prompt: The prompt to display to the user
            
        Returns:
            The user's input as a string
        """
        raise NotImplementedError("Subclasses must implement get_input")


class ConsoleInputProvider(InputProvider):
    """Production input provider that uses builtin input()."""
    
    def get_input(self, prompt: str) -> str:
        """Get input from the console using builtin input().
        
        Args:
            prompt: The prompt to display to the user
            
        Returns:
            The user's input as a string
        """
        return input(prompt)


class MockInputProvider(InputProvider):
    """Mock input provider for testing.
    
    Provides predefined responses and tracks prompts received.
    """
    
    def __init__(self, responses: Union[str, List[str]]):
        """Initialize with predefined responses.
        
        Args:
            responses: Either a single response string or a list of responses
        """
        if isinstance(responses, str):
            self.responses = [responses]
        else:
            self.responses = responses
        self.current_index = 0
        self.prompts_received = []
        
    def get_input(self, prompt: str) -> str:
        """Return the next predefined response.
        
        Args:
            prompt: The prompt to display (tracked for assertions)
            
        Returns:
            The next response in the list
            
        Raises:
            IndexError: When out of predefined responses
        """
        self.prompts_received.append(prompt)
        
        if self.current_index >= len(self.responses):
            raise IndexError(
                f"No more mock responses available. "
                f"Used {self.current_index} of {len(self.responses)} responses."
            )
            
        response = self.responses[self.current_index]
        self.current_index += 1
        return response
        
    def reset(self):
        """Reset the provider for reuse."""
        self.current_index = 0
        self.prompts_received = []