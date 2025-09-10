"""Independent notebook generator working directly with module variables.

This generator creates Jupyter notebooks directly from the variables
defined in examples.py files, without any intermediate data transformation
or dependency on the output pipeline.
"""

import json
import os
from datetime import datetime
from typing import Dict, List, Any, Union, Tuple
from pathlib import Path


class IndependentNotebookGenerator:
    """Generate notebooks directly from module variables.
    
    This generator works independently from the output pipeline,
    using only the module variables and theory templates.
    """
    
    def __init__(self):
        """Initialize the generator."""
        self.template_cache = {}
    
    def generate_from_module_vars(self, module_vars: Dict, source_path: str) -> str:
        """Generate notebook from module variables.
        
        Args:
            module_vars: Dictionary containing:
                - semantic_theories: dict of theory configurations
                - example_range: dict of example definitions
                - general_settings: optional settings dict
            source_path: Path to source file for metadata
            
        Returns:
            JSON string of complete notebook
        """
        # Extract components
        semantic_theories = module_vars.get('semantic_theories', {})
        example_range = module_vars.get('example_range', {})
        
        if not semantic_theories:
            raise ValueError("No semantic theories found in module variables")
        
        if not example_range:
            raise ValueError("No examples found in module variables")
        
        # Get appropriate template
        template = self._get_template(semantic_theories)
        
        # Generate cells directly from module data
        cells = []
        
        # Title cell
        cells.append(self._create_title_cell(source_path, semantic_theories))
        
        # Setup cell from template
        setup_cell = template.create_setup_cell(semantic_theories, example_range)
        cells.append(setup_cell)
        
        # Example cells
        for name, definition in example_range.items():
            example_cells = template.create_example_cells(name, definition)
            cells.extend(example_cells)
        
        # Create notebook structure
        return self._create_notebook_json(cells)
    
    def _get_template(self, semantic_theories: Dict):
        """Get the appropriate template based on semantic theory.
        
        Args:
            semantic_theories: Dictionary of semantic theory configurations
            
        Returns:
            Template instance for the theory type
        """
        # Determine theory type from semantic class
        theory_name, theory_config = next(iter(semantic_theories.items()))
        semantics_class = theory_config.get('semantics')
        
        if not semantics_class:
            raise ValueError("No semantics class found in theory configuration")
        
        # Get class name for template selection
        class_name = semantics_class.__name__ if hasattr(semantics_class, '__name__') else str(semantics_class)
        
        # Check cache first
        if class_name in self.template_cache:
            return self.template_cache[class_name]
        
        # Import and instantiate appropriate template
        from model_checker.notebook.template_loader import TemplateLoader
        loader = TemplateLoader()
        template = loader.get_template_for_class(semantics_class)
        
        # Cache and return
        self.template_cache[class_name] = template
        return template
    
    def _create_title_cell(self, source_path: str, semantic_theories: Dict) -> Dict:
        """Create the title cell for the notebook.
        
        Args:
            source_path: Path to the source examples.py file
            semantic_theories: Dictionary of semantic theories for display name
            
        Returns:
            Markdown cell dictionary with title
        """
        # Get theory name for display
        theory_name = next(iter(semantic_theories.keys())) if semantic_theories else "Theory"
        
        # Get source file name
        source_name = os.path.basename(source_path) if source_path else "examples.py"
        
        title_text = f"""# {theory_name} Examples

Generated from {source_name} - {datetime.now():%Y-%m-%d}

This notebook contains runnable examples for the {theory_name} theory.
Execute each cell to see countermodels or theorem validations."""
        
        return {
            'cell_type': 'markdown',
            'metadata': {},
            'source': title_text.split('\n')
        }
    
    def _create_notebook_json(self, cells: List[Dict]) -> str:
        """Create the complete notebook JSON structure.
        
        Args:
            cells: List of cell dictionaries
            
        Returns:
            JSON string of the complete notebook
        """
        notebook = {
            "cells": cells,
            "metadata": {
                "kernelspec": {
                    "display_name": "Python 3",
                    "language": "python",
                    "name": "python3"
                },
                "language_info": {
                    "codemirror_mode": {
                        "name": "ipython",
                        "version": 3
                    },
                    "file_extension": ".py",
                    "mimetype": "text/x-python",
                    "name": "python",
                    "nbconvert_exporter": "python",
                    "pygments_lexer": "ipython3",
                    "version": "3.8.0"
                }
            },
            "nbformat": 4,
            "nbformat_minor": 4
        }
        
        return json.dumps(notebook, indent=2, ensure_ascii=False)