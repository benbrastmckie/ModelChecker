"""JSON formatter for model checking output."""

import json
from typing import Dict, Any, List
from datetime import datetime


class JSONFormatter:
    """Format model checking results as structured JSON.
    
    This formatter converts model data into JSON format suitable
    for programmatic access and data analysis.
    """
    
    def __init__(self, indent: int = 4, ensure_ascii: bool = False):
        """Initialize JSON formatter.
        
        Args:
            indent: Number of spaces for indentation
            ensure_ascii: Whether to escape non-ASCII characters
        """
        self.indent = indent
        self.ensure_ascii = ensure_ascii
        
    def format_example(self, example_data: Dict[str, Any], 
                      model_output: str) -> str:
        """Format a model checking example as JSON.
        
        The JSON structure preserves all model data for programmatic access.
        
        Args:
            example_data: Dictionary containing model data
            model_output: Raw text output (included as 'output' field)
            
        Returns:
            JSON string representation
        """
        # Add the text output to the data
        data = example_data.copy()
        if model_output:
            data['output'] = model_output
            
        # Convert to JSON
        return json.dumps(data, indent=self.indent, ensure_ascii=self.ensure_ascii)
    
    def format_batch(self, examples: List[str]) -> str:
        """Combine multiple JSON examples into a single document.
        
        Args:
            examples: List of JSON strings (one per example)
            
        Returns:
            Combined JSON document with metadata
        """
        # Parse individual JSON strings
        parsed_examples = []
        for example_json in examples:
            try:
                parsed_examples.append(json.loads(example_json))
            except json.JSONDecodeError:
                # Skip malformed JSON
                continue
        
        # Create combined structure
        combined = {
            "metadata": {
                "timestamp": datetime.now().isoformat(),
                "version": "1.0",
                "total_examples": len(parsed_examples)
            },
            "models": parsed_examples
        }
        
        return json.dumps(combined, indent=self.indent, ensure_ascii=self.ensure_ascii)
    
    def get_file_extension(self) -> str:
        """Get JSON file extension.
        
        Returns:
            'json' for JSON files
        """
        return 'json'