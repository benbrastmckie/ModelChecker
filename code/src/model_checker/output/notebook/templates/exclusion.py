"""Notebook template for Exclusion theory with witness semantics."""

from typing import Dict, List
from .base import DirectNotebookTemplate


class ExclusionNotebookTemplate(DirectNotebookTemplate):
    """Notebook template for Exclusion theory."""
    
    def get_required_imports(self) -> List[str]:
        """Get imports needed for Exclusion theory.
        
        Returns:
            List of import statements
        """
        return [
            "import sys",
            "from model_checker.jupyter import create_build_example",
            "from model_checker.theory_lib.exclusion.semantic import WitnessSemantics",
            "from model_checker.theory_lib.exclusion.proposition import WitnessProposition",
            "from model_checker.theory_lib.exclusion.model_structure import WitnessStructure",
            "from model_checker.theory_lib.exclusion.operators import witness_operators"
        ]
    
    def generate_theory_setup(self, semantic_theories: Dict) -> List[str]:
        """Generate Exclusion theory setup.
        
        Args:
            semantic_theories: Dictionary of semantic theories
            
        Returns:
            List of code lines for theory setup
        """
        lines = []
        
        # Get theory name
        theory_name = next(iter(semantic_theories.keys()))
        
        lines.append("# Exclusion Theory with Witness Semantics")
        lines.append("# This theory uses witness predicates for unilateral semantics")
        lines.append("")
        lines.append("# Build the semantic theory dictionary")
        lines.append("theory = {")
        lines.append('    "semantics": WitnessSemantics,')
        lines.append('    "proposition": WitnessProposition,')
        lines.append('    "model": WitnessStructure,')
        lines.append('    "operators": witness_operators')
        lines.append("}")
        lines.append("")
        lines.append('print("=" * 70)')
        lines.append(f'print("{theory_name.upper()} LOADED")')
        lines.append('print("=" * 70)')
        lines.append('print("Using witness-based unilateral semantics")')
        lines.append('print("Witness predicates determine proposition truth/falsity")')
        lines.append('print("=" * 70)')
        
        return lines