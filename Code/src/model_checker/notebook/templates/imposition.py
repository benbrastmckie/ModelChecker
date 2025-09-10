"""Notebook template for Imposition theory."""

from typing import Dict, List
from model_checker.notebook.templates.base import DirectNotebookTemplate


class ImpositionNotebookTemplate(DirectNotebookTemplate):
    """Notebook template for Imposition theory."""
    
    def get_required_imports(self) -> List[str]:
        """Get imports needed for Imposition theory.
        
        Returns:
            List of import statements
        """
        return [
            "import sys",
            "from model_checker.jupyter import create_build_example",
            "from model_checker.theory_lib.imposition.semantic import ImpositionSemantics",
            "from model_checker.theory_lib.imposition.proposition import ImpositionProposition",
            "from model_checker.theory_lib.imposition.model_structure import ImpositionModelStructure",
            "from model_checker.theory_lib.imposition.operators import imposition_operators"
        ]
    
    def generate_theory_setup(self, semantic_theories: Dict) -> List[str]:
        """Generate Imposition theory setup.
        
        Args:
            semantic_theories: Dictionary of semantic theories
            
        Returns:
            List of code lines for theory setup
        """
        lines = []
        
        # Get theory name
        theory_name = next(iter(semantic_theories.keys()))
        
        lines.append("# Imposition Theory")
        lines.append("# Based on Kit Fine's imposition semantics")
        lines.append("")
        lines.append("# Build the semantic theory dictionary")
        lines.append("theory = {")
        lines.append('    "semantics": ImpositionSemantics,')
        lines.append('    "proposition": ImpositionProposition,')
        lines.append('    "model": ImpositionModelStructure,')
        lines.append('    "operators": imposition_operators')
        lines.append("}")
        lines.append("")
        lines.append('print("=" * 70)')
        lines.append(f'print("{theory_name.upper()} LOADED")')
        lines.append('print("=" * 70)')
        lines.append('print("Using imposition-based semantics")')
        lines.append('print("=" * 70)')
        
        return lines