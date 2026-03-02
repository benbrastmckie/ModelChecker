"""Markdown formatter for model checking output."""

import re
from typing import Dict, Any, List


class MarkdownFormatter:
    """Format model checking results as markdown documentation.
    
    This formatter converts model data and output into human-readable
    markdown format suitable for documentation and reports.
    """
    
    def __init__(self, use_colors: bool = False):
        """Initialize markdown formatter.
        
        Args:
            use_colors: Whether to use color indicators in output
        """
        self.use_colors = use_colors
        
    def format_example(self, example_data: Dict[str, Any], 
                      model_output: str) -> str:
        """Format a model checking example as markdown.
        
        Args:
            example_data: Dictionary containing model data
            model_output: Raw text output from model checking
            
        Returns:
            Formatted markdown string
        """
        # If we have raw output, return it as-is
        if model_output:
            return model_output.strip()
            
        # Otherwise, create a simple summary
        example = example_data.get("example", "Unknown")
        if not example_data.get("has_model", False):
            return f"EXAMPLE {example}: there is no countermodel."
        else:
            return f"EXAMPLE {example}: model found but no output available."
    
    def format_batch(self, examples: List[str]) -> str:
        """Combine multiple examples with markdown separators.
        
        Args:
            examples: List of formatted example strings
            
        Returns:
            Combined markdown with separators
        """
        return '\n\n---\n\n'.join(examples)
    
    def get_file_extension(self) -> str:
        """Get markdown file extension.
        
        Returns:
            'md' for markdown files
        """
        return 'md'
    
    def format_state_type(self, state: str, state_type: str) -> str:
        """Format state with type indicator.
        
        Args:
            state: State name (e.g., "s0")
            state_type: Type of state ("possible", "impossible", "world", "evaluation")
            
        Returns:
            Formatted state string
        """
        if self.use_colors:
            return self._with_color_indicator(state, state_type)
        else:
            return f"{state} [{state_type.upper()}]"
            
    def _with_color_indicator(self, state: str, state_type: str) -> str:
        """Add color indicator based on state type.
        
        Args:
            state: State name
            state_type: Type of state
            
        Returns:
            State with type indicator
        """
        indicator_map = {
            "possible": "•",
            "impossible": "○",
            "world": "▪",
            "evaluation": "★"
        }
        
        indicator = indicator_map.get(state_type, "")
        if indicator:
            return f"{indicator} {state}"
        return state


class ANSIToMarkdown:
    """Converts ANSI escape codes to markdown formatting.
    
    This class handles the conversion of ANSI color codes commonly used
    in terminal output to markdown-friendly formatting.
    """
    
    def convert(self, ansi_text: str) -> str:
        """Convert ANSI escape codes to markdown.
        
        Args:
            ansi_text: Text containing ANSI escape codes
            
        Returns:
            Markdown formatted text
        """
        # Pattern to match ANSI escape sequences
        ansi_pattern = re.compile(r'\033\[([0-9;]+)m')
        
        # First pass: identify color regions
        # Red (31) -> Bold in markdown
        # Green (32) -> Italic in markdown
        # Reset (0) -> End formatting
        
        result = ansi_text
        
        # Convert red text to bold (non-greedy match)
        result = re.sub(r'\033\[31m([^\033]*?)\033\[0m', r'**\1**', result)
        
        # Convert green text to italic (non-greedy match)
        result = re.sub(r'\033\[32m([^\033]*?)\033\[0m', r'_\1_', result)
        
        # Handle unclosed color codes at boundaries
        result = re.sub(r'\033\[31m(.*?)$', r'**\1**', result)
        result = re.sub(r'\033\[32m(.*?)$', r'_\1_', result)
        
        # Strip any remaining ANSI codes
        result = ansi_pattern.sub('', result)
        
        return result