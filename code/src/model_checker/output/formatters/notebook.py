"""Notebook formatter that integrates with StreamingNotebookGenerator.

This formatter acts as an adapter between the IOutputFormatter interface
and the StreamingNotebookGenerator, allowing notebook generation to be
managed through the unified OutputManager system.
"""

from typing import Dict, Any, Optional
from pathlib import Path
import tempfile
import json

from .base import IOutputFormatter
from ..notebook import StreamingNotebookGenerator


class NotebookFormatter(IOutputFormatter):
    """Adapter to integrate notebook generation with formatter pattern.
    
    This formatter bridges the gap between the batch-oriented formatter
    interface and the streaming notebook generation system.
    """
    
    def __init__(self):
        """Initialize the notebook formatter."""
        self.generator = StreamingNotebookGenerator()
        self._module_vars: Optional[Dict] = None
        self._source_path: Optional[str] = None
        self._collected_examples: list = []
        
    def set_context(self, module_vars: Dict, source_path: str):
        """Set the module context for notebook generation.
        
        This must be called before formatting examples.
        
        Args:
            module_vars: Module variables including semantic_theories
            source_path: Path to the source examples file
        """
        self._module_vars = module_vars
        self._source_path = source_path
        
    def format_example(self, example_data: Dict[str, Any], 
                      model_output: str) -> str:
        """Format a model checking example for notebook output.
        
        Since notebooks require all examples together, this method
        collects examples for later batch processing.
        
        Args:
            example_data: Dictionary containing model data
            model_output: Raw text output from model checking
            
        Returns:
            Empty string (actual output generated in format_batch)
        """
        # Collect example data for batch generation
        self._collected_examples.append({
            'data': example_data,
            'output': model_output
        })
        
        # Return placeholder since actual generation happens in batch
        return ""
    
    def format_batch(self, examples: list) -> str:
        """Generate complete notebook from collected examples.
        
        Args:
            examples: List of formatted example strings (ignored)
            
        Returns:
            Path to generated notebook file
        """
        if not self._module_vars or not self._source_path:
            raise ValueError("Context not set. Call set_context() before formatting.")
        
        # Create temporary file for notebook output
        with tempfile.NamedTemporaryFile(
            mode='w', 
            suffix='.ipynb', 
            delete=False
        ) as temp_file:
            temp_path = temp_file.name
        
        try:
            # Generate notebook using streaming generator
            self.generator.generate_notebook_stream(
                self._module_vars,
                self._source_path,
                temp_path
            )
            
            # Read the generated notebook to return as string
            with open(temp_path, 'r') as f:
                notebook_content = f.read()
            
            return notebook_content
            
        finally:
            # Clean up temporary file
            Path(temp_path).unlink(missing_ok=True)
            # Reset for next batch
            self._collected_examples = []
    
    def get_file_extension(self) -> str:
        """Get the file extension for notebook format.
        
        Returns:
            'ipynb' for Jupyter notebook files
        """
        return 'ipynb'
    
    def format_for_streaming(self, output_path: str) -> None:
        """Generate notebook directly to output path using streaming.
        
        This method bypasses the string-based interface for efficiency.
        
        Args:
            output_path: Path where notebook should be written
        """
        if not self._module_vars or not self._source_path:
            raise ValueError("Context not set. Call set_context() before formatting.")
        
        self.generator.generate_notebook_stream(
            self._module_vars,
            self._source_path,
            output_path
        )