"""Base protocol for output formatters."""

from typing import Protocol, Dict, Any


class IOutputFormatter(Protocol):
    """Protocol defining the interface for output formatters.
    
    Output formatters convert model checking results into specific
    file formats (markdown, JSON, Jupyter notebooks, etc.).
    """
    
    def format_example(self, example_data: Dict[str, Any], 
                      model_output: str) -> str:
        """Format a model checking example for output.
        
        Args:
            example_data: Dictionary containing model data including:
                - example: Name of the example
                - theory: Theory used
                - has_model: Whether a model was found
                - premises: List of premises
                - conclusions: List of conclusions
                - settings: Model checking settings
                - states: State information
                - relations: Relation information
                - propositions: Proposition values
            model_output: Raw text output from model checking
            
        Returns:
            Formatted string ready to be written to file
        """
        ...
    
    def format_batch(self, examples: list) -> str:
        """Format multiple examples for batch output.
        
        Some formatters may need special handling for combining
        multiple examples into a single file.
        
        Args:
            examples: List of formatted example strings
            
        Returns:
            Combined formatted string
        """
        ...
    
    def get_file_extension(self) -> str:
        """Get the file extension for this format.
        
        Returns:
            File extension without the dot (e.g., 'md', 'json', 'ipynb')
        """
        ...