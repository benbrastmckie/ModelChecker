"""Error hierarchy for output package."""

from typing import Dict, Any


class OutputError(Exception):
    """Base exception for output-related errors."""
    
    def __init__(self, message: str, context: Dict[str, Any] = None):
        """Initialize with message and optional context.
        
        Args:
            message: Error message
            context: Optional dictionary with error context
        """
        super().__init__(message)
        self.context = context or {}


class OutputDirectoryError(OutputError):
    """Error creating or accessing output directory."""
    
    def __init__(self, directory: str, reason: str, suggestion: str = None):
        """Initialize with directory path, reason, and suggestion.
        
        Args:
            directory: The directory path that caused the error
            reason: Explanation of what went wrong
            suggestion: Actionable step to resolve (optional)
        """
        message = f"Output directory error for '{directory}': {reason}"
        
        if suggestion:
            message += f"\n  Suggestion: {suggestion}"
        else:
            # Provide default suggestions based on reason
            if "permission" in reason.lower():
                message += "\n  Suggestion: Check write permissions or use --output-dir flag"
            elif "exists" in reason.lower():
                message += "\n  Suggestion: Use a different directory or remove existing files"
            elif "space" in reason.lower():
                message += "\n  Suggestion: Free up disk space or use a different location"
                
        super().__init__(message, {
            'directory': directory, 
            'reason': reason,
            'suggestion': suggestion
        })


class OutputFormatError(OutputError):
    """Error with output format generation."""
    
    def __init__(self, format_name: str, reason: str, suggestion: str = None):
        """Initialize with format name, reason, and suggestion.
        
        Args:
            format_name: The format that failed (markdown, json, notebook)
            reason: Explanation of what went wrong
            suggestion: Actionable step to resolve (optional)
        """
        message = f"Format generation error for '{format_name}': {reason}"
        
        if suggestion:
            message += f"\n  Suggestion: {suggestion}"
        else:
            # Provide default suggestions based on format
            if format_name == "json" and "serializ" in reason.lower():
                message += "\n  Suggestion: Ensure all data is JSON-serializable (no custom objects)"
            elif format_name == "markdown":
                message += "\n  Suggestion: Check for invalid markdown syntax or ANSI codes"
            elif format_name == "notebook":
                message += "\n  Suggestion: Verify notebook template exists and is valid JSON"
                
        super().__init__(message, {
            'format': format_name, 
            'reason': reason,
            'suggestion': suggestion
        })


class OutputIOError(OutputError):
    """Error writing output files."""
    
    def __init__(self, filename: str, reason: str, suggestion: str = None):
        """Initialize with filename, reason, and suggestion.
        
        Args:
            filename: The file that couldn't be written
            reason: Explanation of what went wrong
            suggestion: Actionable step to resolve (optional)
        """
        message = f"Failed to write '{filename}': {reason}"
        
        if suggestion:
            message += f"\n  Suggestion: {suggestion}"
        else:
            # Provide default suggestions based on reason
            if "permission" in reason.lower():
                message += "\n  Suggestion: Check file permissions in output directory"
            elif "exist" in reason.lower():
                message += "\n  Suggestion: Ensure output directory exists and is writable"
            elif "space" in reason.lower():
                message += "\n  Suggestion: Free up disk space or choose different output location"
                
        super().__init__(message, {
            'filename': filename, 
            'reason': reason,
            'suggestion': suggestion
        })


class OutputStrategyError(OutputError):
    """Error with output strategy execution."""
    
    def __init__(self, strategy: str, reason: str):
        """Initialize with strategy name and reason.
        
        Args:
            strategy: The strategy that failed
            reason: Explanation of what went wrong
        """
        message = f"Strategy '{strategy}' failed: {reason}"
        super().__init__(message, {'strategy': strategy, 'reason': reason})


class NotebookGenerationError(OutputError):
    """Error generating Jupyter notebook."""
    
    def __init__(self, example_name: str, reason: str):
        """Initialize with example name and reason.
        
        Args:
            example_name: The example being converted to notebook
            reason: Explanation of what went wrong
        """
        message = f"Failed to generate notebook for '{example_name}': {reason}"
        super().__init__(message, {'example': example_name, 'reason': reason})