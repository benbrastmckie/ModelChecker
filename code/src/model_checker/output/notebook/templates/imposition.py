"""Notebook template for Imposition semantics theory.

This template handles notebook generation for theories using
ImpositionSemantics, which implements imposition-based reasoning.
"""

from typing import Dict, List
from .base import DirectNotebookTemplate


class ImpositionNotebookTemplate(DirectNotebookTemplate):
    """Notebook template for Imposition semantics theory."""

    def get_required_imports(self) -> List[str]:
        """Get imports needed for Imposition theory.

        Returns:
            List of import statements
        """
        return [
            "import sys",
            "from model_checker.jupyter import create_build_example",
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

        lines.append("# Imposition theory setup")
        lines.append("theory = semantic_theories[list(semantic_theories.keys())[0]]")
        lines.append("")
        lines.append('print("=" * 70)')
        lines.append(f'print("{theory_name.upper()} LOADED")')
        lines.append('print("=" * 70)')
        lines.append('print("Using Imposition semantics")')
        lines.append('print("=" * 70)')

        return lines
