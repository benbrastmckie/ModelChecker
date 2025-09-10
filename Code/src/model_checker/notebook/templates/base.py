"""Base template for direct notebook generation.

Templates work directly with module variables without any intermediate
data transformation or JSON serialization.
"""

from typing import Dict, List, Any, Union, Tuple, Set


class DirectNotebookTemplate:
    """Base template for direct notebook generation.
    
    Templates work directly with module variables without
    any intermediate data transformation.
    """
    
    def create_setup_cell(self, semantic_theories: Dict, example_range: Dict) -> Dict:
        """Create setup cell with imports and theory configuration.
        
        Args:
            semantic_theories: Raw semantic theories from module
            example_range: Raw example definitions from module
            
        Returns:
            Cell dictionary for Jupyter notebook
        """
        # Generate imports
        imports = self.get_required_imports()
        
        # Generate theory setup
        setup_code = self.generate_theory_setup(semantic_theories)
        
        # Combine into single code cell
        code_lines = imports + [''] + setup_code
        
        return {
            'cell_type': 'code',
            'metadata': {},
            'source': [line + '\n' for line in code_lines],
            'outputs': [],
            'execution_count': None
        }
    
    def create_example_cells(self, name: str, definition: Union[List, Tuple]) -> List[Dict]:
        """Create cells for a single example.
        
        Args:
            name: Example name from example_range keys
            definition: Raw definition (premises, conclusions, settings)
            
        Returns:
            List of cell dictionaries
        """
        cells = []
        
        # Header cell
        cells.append(self._create_header_cell(name))
        
        # Code cell with example
        cells.append(self._create_example_code_cell(name, definition))
        
        # Result interpretation placeholder
        cells.append(self._create_interpretation_cell())
        
        return cells
    
    def get_required_imports(self) -> List[str]:
        """Get the list of import statements needed.
        
        Returns:
            List of import statement strings
        """
        # Default imports for any theory
        return [
            "import sys",
            "from model_checker.jupyter import create_build_example"
        ]
    
    def generate_theory_setup(self, semantic_theories: Dict) -> List[str]:
        """Generate theory setup code.
        
        Args:
            semantic_theories: Dictionary of semantic theories
            
        Returns:
            List of code lines for theory setup
        """
        # For generic template, just create a simple theory dict
        lines = []
        lines.append("# Theory setup")
        
        # Get first theory
        theory_name, theory_config = next(iter(semantic_theories.items()))
        
        lines.append(f"# Using {theory_name}")
        lines.append("theory = semantic_theories[list(semantic_theories.keys())[0]]")
        lines.append("")
        lines.append(f'print("=" * 70)')
        lines.append(f'print("{theory_name.upper()} LOADED")')
        lines.append(f'print("=" * 70)')
        
        return lines
    
    def _create_header_cell(self, name: str) -> Dict:
        """Create a markdown header cell for an example.
        
        Args:
            name: Example name
            
        Returns:
            Markdown cell dictionary
        """
        # Determine example type from name
        example_type = self._get_example_type(name)
        
        header_text = f"""## {name}

### {example_type}"""
        
        return {
            'cell_type': 'markdown',
            'metadata': {},
            'source': header_text.split('\n')
        }
    
    def _create_example_code_cell(self, name: str, definition: Union[List, Tuple]) -> Dict:
        """Create code cell for an example.
        
        Args:
            name: Example name
            definition: Example definition (premises, conclusions, settings)
            
        Returns:
            Code cell dictionary
        """
        # Parse definition
        if isinstance(definition, (list, tuple)):
            premises = definition[0] if len(definition) > 0 else []
            conclusions = definition[1] if len(definition) > 1 else []
            settings = definition[2] if len(definition) > 2 else {}
        else:
            raise ValueError(f"Invalid example format for {name}")
        
        # Generate code
        code_lines = []
        
        # Comment describing the example
        example_desc = self._get_example_description(name)
        code_lines.append(f"# {name}: {example_desc}")
        
        # Variable name from example name
        var_name = name.replace('-', '_').replace(' ', '_').lower()
        
        # Example definition
        code_lines.append(f"{var_name} = [")
        
        # Premises
        code_lines.append("    [  # Premises")
        for premise in premises:
            # Escape backslashes for LaTeX in Python strings
            escaped = premise.replace('\\', '\\\\')
            code_lines.append(f"        '{escaped}',")
        code_lines.append("    ],")
        
        # Conclusions
        code_lines.append("    [  # Conclusions")
        for conclusion in conclusions:
            # Escape backslashes for LaTeX in Python strings
            escaped = conclusion.replace('\\', '\\\\')
            code_lines.append(f"        '{escaped}',")
        code_lines.append("    ],")
        
        # Settings
        if settings:
            code_lines.append("    {  # Settings")
            for key, value in settings.items():
                comment = self._get_setting_comment(key)
                if isinstance(value, str):
                    code_lines.append(f"        '{key}': '{value}',{comment}")
                else:
                    code_lines.append(f"        '{key}': {value},{comment}")
            code_lines.append("    }")
        else:
            code_lines.append("    {}  # Default settings")
        
        code_lines.append("]")
        code_lines.append("")
        
        # Run model checker
        code_lines.append("print('Running model checker...')")
        code_lines.append(f"model = create_build_example('{name}', theory, {var_name})")
        code_lines.append("")
        
        # Display results
        code_lines.append("# Display the results")
        code_lines.append("if model.model_structure.z3_model:")
        code_lines.append("    model.model_structure.print_to(")
        code_lines.append("        model.settings,")
        code_lines.append(f"        '{name}',")
        code_lines.append("        theory['semantics'].__name__,")
        code_lines.append("        output=sys.stdout")
        code_lines.append("    )")
        code_lines.append("else:")
        code_lines.append("    print('=' * 70)")
        code_lines.append(f"    print('THEOREM VALIDATED: {name}')")
        code_lines.append("    print('=' * 70)")
        code_lines.append("    print('No countermodel found - the inference is VALID')")
        code_lines.append("    print('=' * 70)")
        
        return {
            'cell_type': 'code',
            'metadata': {},
            'source': [line + '\n' for line in code_lines],
            'outputs': [],
            'execution_count': None
        }
    
    def _create_interpretation_cell(self) -> Dict:
        """Create a markdown cell for result interpretation.
        
        Returns:
            Markdown cell dictionary
        """
        text = """### Result Interpretation

[To be added after running the example]"""
        
        return {
            'cell_type': 'markdown',
            'metadata': {},
            'source': text.split('\n')
        }
    
    def _get_example_type(self, name: str) -> str:
        """Determine the type of example from its name.
        
        Args:
            name: Example name
            
        Returns:
            Description of what the example tests
        """
        # Check for common patterns with underscores
        if 'CM_' in name or '_CM_' in name:
            return "Test for Countermodel"
        elif 'TH_' in name or '_TH_' in name:
            return "Test for Theorem Validity"
        else:
            return "Model Checking Example"
    
    def _get_example_description(self, name: str) -> str:
        """Generate description based on example name.
        
        Args:
            name: Example name
            
        Returns:
            Brief description of what the example tests
        """
        # Use same logic as _get_example_type for consistency
        if 'CM_' in name or '_CM_' in name:
            return "Test for countermodel"
        elif 'TH_' in name or '_TH_' in name:
            return "Test theorem validity"
        else:
            return "Model checking example"
    
    def _get_setting_comment(self, key: str) -> str:
        """Get helpful comment for a setting key.
        
        Args:
            key: Setting key name
            
        Returns:
            Comment string (including leading spaces)
        """
        comments = {
            'N': '  # Number of atomic states',
            'contingent': '  # Force contingent propositions',
            'non_null': '  # Exclude null state',
            'non_empty': '  # Exclude empty state',
            'disjoint': '  # Force disjoint subject matters',
            'max_time': '  # Timeout in seconds',
            'iterate': '  # Number of models to find',
            'expectation': '  # Expected result (for testing)',
            'max_world_id': '  # Maximum world ID',
            'simple_worlds': '  # Use simplified world structure',
            'times': '  # Number of time points (bimodal)',
            'restrict_flow': '  # Restrict temporal flow (bimodal)'
        }
        return comments.get(key, '')