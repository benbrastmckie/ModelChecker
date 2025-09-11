"""Streaming notebook generator for memory-efficient generation.

This module provides a streaming approach to notebook generation that
processes examples one at a time and writes directly to output files,
maintaining constant memory usage regardless of example count.
"""

import json
import os
import copy
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Any, Union, Tuple

from .notebook_writer import NotebookWriter


class StreamingNotebookGenerator:
    """Generate notebooks using streaming template decomposition.
    
    This generator processes templates that are decomposed into sections
    (setup, example pattern, conclusion) and streams the output directly
    to files without loading all examples into memory at once.
    """
    
    def __init__(self):
        """Initialize the streaming generator."""
        self.template_cache = {}
    
    def generate_notebook_stream(self, module_vars: Dict, source_path: str, output_path: str):
        """Generate notebook by streaming sections and examples.
        
        Args:
            module_vars: Dictionary containing semantic_theories, example_range
            source_path: Path to source examples.py file  
            output_path: Path where notebook will be written
        """
        # Extract components
        semantic_theories = module_vars.get('semantic_theories', {})
        example_range = module_vars.get('example_range', {})
        
        if not semantic_theories:
            raise ValueError("No semantic theories found in module variables")
        
        if not example_range:
            raise ValueError("No examples found in module variables") 
        
        print(f"Streaming notebook with {len(example_range)} examples")
        
        # Load template sections
        template_sections = self._load_template_sections(source_path, semantic_theories)
        
        # Stream generation with constant memory usage
        with NotebookWriter(output_path) as writer:
            # Write setup section
            for cell in template_sections['setup_cells']:
                substituted_cell = self._substitute_placeholders(cell, module_vars, source_path)
                writer.write_cell(substituted_cell)
            
            # Stream examples one at a time (memory efficient)
            for name, definition in example_range.items():
                example_cells = self._generate_example_from_template(
                    name, definition, template_sections['example_template']
                )
                for cell in example_cells:
                    writer.write_cell(cell)
                # Memory for this example is freed here
            
            # Write conclusion section
            for cell in template_sections['conclusion_cells']:
                substituted_cell = self._substitute_placeholders(cell, module_vars, source_path)
                writer.write_cell(substituted_cell)
        
        print(f"Notebook streamed successfully: {len(example_range)} examples")
    
    def _load_template_sections(self, source_path: str, semantic_theories: Dict) -> Dict:
        """Load decomposed template sections from appropriate template.json.
        
        Args:
            source_path: Path to examples file to determine theory type
            semantic_theories: Theory configuration for template discovery
            
        Returns:
            Dictionary with setup_cells, example_template, conclusion_cells
        """
        template_path = self._discover_template_path(source_path, semantic_theories)
        
        if template_path in self.template_cache:
            return self.template_cache[template_path]
        
        try:
            with open(template_path, 'r', encoding='utf-8') as f:
                template_sections = json.load(f)
                
            # Validate template structure
            required_sections = ['setup_cells', 'example_template', 'conclusion_cells']
            for section in required_sections:
                if section not in template_sections:
                    raise ValueError(f"Template missing required section: {section}")
                    
            self.template_cache[template_path] = template_sections
            return template_sections
            
        except FileNotFoundError:
            # Provide helpful error message with expected path
            raise FileNotFoundError(
                f"No template found for notebook generation.\\n"
                f"Expected template at: {template_path}\\n"
                f"Please create a template.json file at this location.\\n"
                f"You can reference existing templates or the counterfactual example."
            )
        except json.JSONDecodeError as e:
            raise ValueError(f"Invalid JSON in template {template_path}: {e}")
    
    def _discover_template_path(self, source_path: str, semantic_theories: Dict) -> str:
        """Discover the correct template path based on theory structure.
        
        Args:
            source_path: Path to examples file
            semantic_theories: Theory configuration
            
        Returns:
            Path to appropriate template.json file
        """
        # Convert to Path for easier manipulation
        source = Path(source_path)
        
        # Navigate up to find theory_lib
        current = source.parent
        while current.name != 'theory_lib' and current.parent != current:
            current = current.parent
            
        if current.name != 'theory_lib':
            raise ValueError(f"Could not locate theory_lib from {source_path}")
        
        # Check if this is a subtheory (has subtheories in path)
        if 'subtheories' in source.parts:
            # Extract theory and subtheory from path
            parts = source.parts
            subtheory_idx = parts.index('subtheories')
            theory_name = parts[subtheory_idx - 1]  
            subtheory_name = parts[subtheory_idx + 1]
            
            template_path = current / theory_name / 'subtheories' / subtheory_name / 'notebooks' / 'template.json'
        else:
            # Standalone theory - extract theory name from path  
            parts = source.parts
            theory_lib_idx = parts.index('theory_lib')
            theory_name = parts[theory_lib_idx + 1]
            
            template_path = current / theory_name / 'notebooks' / 'template.json'
            
        return str(template_path)
    
    def _generate_example_from_template(self, name: str, definition: tuple, 
                                      example_template: Dict) -> List[Dict]:
        """Generate 3 cells for a single example from template.
        
        Args:
            name: Example name (CF_CM_1, etc.)
            definition: (premises, conclusions, settings) tuple
            example_template: Template with header_cell, code_cell, interpretation_cell
            
        Returns:
            List of 3 instantiated cell dictionaries
        """
        cells = []
        
        # 1. Generate header cell from template
        header_cell = copy.deepcopy(example_template['header_cell'])
        header_cell['source'] = self._substitute_example_placeholders(
            header_cell['source'], name, definition
        )
        cells.append(header_cell)
        
        # 2. Generate code cell from template  
        code_cell = copy.deepcopy(example_template['code_cell'])
        code_cell['source'] = self._substitute_example_placeholders(
            code_cell['source'], name, definition
        )
        code_cell['outputs'] = []
        code_cell['execution_count'] = None
        cells.append(code_cell)
        
        # 3. Generate interpretation cell from template
        interp_cell = copy.deepcopy(example_template['interpretation_cell'])
        interp_cell['source'] = self._substitute_example_placeholders(
            interp_cell['source'], name, definition
        )
        cells.append(interp_cell)
        
        return cells
    
    def _substitute_placeholders(self, cell: Dict, module_vars: Dict, source_path: str) -> Dict:
        """Substitute global placeholders in setup/conclusion cells.
        
        Args:
            cell: Cell dictionary to process
            module_vars: Module variables for theory information
            source_path: Source file path for metadata
            
        Returns:
            Cell with placeholders substituted
        """
        cell_copy = copy.deepcopy(cell)
        
        # Create global substitutions
        theory_name = self._extract_theory_display_name(module_vars)
        substitutions = {
            '{{THEORY_NAME}}': theory_name,
            '{{DATE}}': datetime.now().strftime('%Y-%m-%d'),
            '{{EXAMPLE_COUNT}}': str(len(module_vars.get('example_range', {})))
        }
        
        # Apply substitutions to source lines
        if 'source' in cell_copy:
            for i, line in enumerate(cell_copy['source']):
                for placeholder, value in substitutions.items():
                    line = line.replace(placeholder, value)
                # Ensure line ends with newline
                if not line.endswith('\n'):
                    line += '\n'
                cell_copy['source'][i] = line
                
        return cell_copy
    
    def _substitute_example_placeholders(self, source_lines: List[str], 
                                       name: str, definition: tuple) -> List[str]:
        """Substitute placeholders in source lines with example data.
        
        Args:
            source_lines: Lines of source code/markdown
            name: Example name
            definition: Example definition tuple
            
        Returns:
            Source lines with placeholders substituted (with newlines)
        """
        # Create substitution mapping
        var_name = name.lower().replace('_', '_')
        example_type = self._get_example_type(name)
        example_code_lines = self._format_example_definition_as_lines(var_name, definition)
        
        # Apply substitutions to each line
        result = []
        for line in source_lines:
            # Handle multi-line substitutions specially
            if '{{EXAMPLE_CODE}}' in line:
                # Replace the line with multiple lines
                indent = line[:line.index('{{EXAMPLE_CODE}}')]
                for code_line in example_code_lines:
                    # Add newline to each code line
                    result.append(indent + code_line + '\n')
            else:
                # Simple substitutions
                line = line.replace('{{EXAMPLE_NAME}}', name)
                line = line.replace('{{EXAMPLE_TYPE}}', example_type)
                line = line.replace('{{EXAMPLE_VAR}}', var_name)
                # Ensure line ends with newline
                if not line.endswith('\n'):
                    line += '\n'
                result.append(line)
            
        return result
    
    def _get_example_type(self, name: str) -> str:
        """Determine example type from name for display purposes.
        
        Args:
            name: Example name like CF_CM_1, CF_TH_5
            
        Returns:
            Human-readable example type
        """
        if '_CM_' in name:
            return 'Test for Countermodel'
        elif '_TH_' in name:
            return 'Test for Theorem'
        else:
            return 'Logic Example'
    
    def _format_example_definition_as_lines(self, var_name: str, definition: tuple) -> List[str]:
        """Format example definition as Python code lines.
        
        Args:
            var_name: Variable name for the example
            definition: (premises, conclusions, settings) tuple
            
        Returns:
            List of Python code lines
        """
        premises, conclusions = definition[0], definition[1]
        settings = definition[2] if len(definition) > 2 else {}
        
        lines = [f"{var_name} = ["]
        
        # Format premises - need to double-escape backslashes
        # Two backslashes in Python string for LaTeX
        premises_str = '[' + ', '.join(f'"{p.replace(chr(92), chr(92)*2)}"' for p in premises) + ']'
        lines.append(f"    {premises_str},")
        
        # Format conclusions - same double-escaping
        conclusions_str = '[' + ', '.join(f'"{c.replace(chr(92), chr(92)*2)}"' for c in conclusions) + ']'
        lines.append(f"    {conclusions_str},")
        
        # Format settings
        if settings:
            lines.append("    {")
            for key, value in settings.items():
                if isinstance(value, str):
                    lines.append(f"        '{key}': '{value}',")
                elif isinstance(value, bool):
                    lines.append(f"        '{key}': {str(value)},")
                else:
                    lines.append(f"        '{key}': {value},")
            lines.append("    }")
        else:
            lines.append("    {}")
        
        lines.append("]")
        
        return lines
    
    def _format_example_definition(self, var_name: str, definition: tuple) -> str:
        """Format example definition as Python code.
        
        Args:
            var_name: Variable name for the example
            definition: (premises, conclusions, settings) tuple
            
        Returns:
            Formatted Python code string
        """
        premises, conclusions = definition[0], definition[1]
        settings = definition[2] if len(definition) > 2 else {}
        
        lines = [f"{var_name} = ["]
        
        # Format premises - need to double-escape backslashes for JSON->Python
        # Each backslash in the original LaTeX needs to become 4 backslashes in JSON
        # so that when JSON is parsed, we get 2 backslashes in the Python string
        premises_str = '[' + ', '.join(f'"{p.replace(chr(92), chr(92)*4)}"' for p in premises) + ']'
        lines.append(f"    {premises_str},")
        
        # Format conclusions - same double-escaping needed
        conclusions_str = '[' + ', '.join(f'"{c.replace(chr(92), chr(92)*4)}"' for c in conclusions) + ']'
        lines.append(f"    {conclusions_str},")
        
        # Format settings
        if settings:
            lines.append("    {")
            for key, value in settings.items():
                if isinstance(value, str):
                    lines.append(f"        '{key}': '{value}',")
                elif isinstance(value, bool):
                    lines.append(f"        '{key}': {str(value)},")
                else:
                    lines.append(f"        '{key}': {value},")
            lines.append("    }")
        else:
            lines.append("    {}")
        
        lines.append("]")
        
        return '\\n'.join(lines)
    
    def _extract_theory_display_name(self, module_vars: Dict) -> str:
        """Extract a display name for the theory from module variables.
        
        Args:
            module_vars: Module variables containing semantic theories
            
        Returns:
            Human-readable theory name
        """
        semantic_theories = module_vars.get('semantic_theories', {})
        if not semantic_theories:
            return 'Logic Theory'
            
        # Get first theory name and try to make it readable
        theory_key = next(iter(semantic_theories.keys()))
        
        # Convert key to readable name
        theory_lower = theory_key.lower()
        if 'counterfactual' in theory_lower or 'brast' in theory_lower:
            return 'Counterfactual Logic'
        elif 'modal' in theory_lower:
            return 'Modal Logic'
        elif 'exclusion' in theory_lower:
            return 'Exclusion Logic'
        elif 'imposition' in theory_lower:
            return 'Imposition Logic'
        else:
            return theory_key.replace('_', ' ').title()