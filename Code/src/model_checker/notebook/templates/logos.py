"""Notebook template for Logos hyperintensional theory.

This template handles the complexity of Logos' modular architecture with
multiple subtheories that can be selectively loaded based on the operators
used in examples.
"""

from typing import Dict, List, Set
from model_checker.notebook.templates.base import DirectNotebookTemplate


class LogosNotebookTemplate(DirectNotebookTemplate):
    """Notebook template for Logos theory with subtheory detection."""
    
    def get_required_imports(self) -> List[str]:
        """Get imports needed for Logos theory.
        
        Returns:
            List of import statements
        """
        return [
            "import sys",
            "from model_checker.jupyter import create_build_example",
            "from model_checker.theory_lib.logos.semantic import LogosSemantics, LogosProposition, LogosModelStructure",
            "from model_checker.theory_lib.logos.operators import LogosOperatorRegistry"
        ]
    
    def generate_theory_setup(self, semantic_theories: Dict) -> List[str]:
        """Generate Logos theory setup with appropriate subtheories.
        
        Args:
            semantic_theories: Dictionary of semantic theories
            
        Returns:
            List of code lines for theory setup
        """
        lines = []
        
        # Get theory name
        theory_name = next(iter(semantic_theories.keys()))
        
        # For now, detect if this is counterfactual based on theory name
        # In the future, we could analyze the example_range to detect operators
        is_counterfactual = 'counterfactual' in theory_name.lower()
        
        if is_counterfactual:
            # Counterfactual-specific setup
            lines.append("# Create operator registry for counterfactual theory")
            lines.append("# We need modal operators as well since counterfactuals build on modal logic")
            lines.append("counterfactual_registry = LogosOperatorRegistry()")
            lines.append("counterfactual_registry.load_subtheories(['extensional', 'modal', 'counterfactual'])")
            lines.append("")
            lines.append("# Build the semantic theory dictionary")
            lines.append("cf_theory = {")
            lines.append('    "semantics": LogosSemantics,')
            lines.append('    "proposition": LogosProposition,')
            lines.append('    "model": LogosModelStructure,')
            lines.append('    "operators": counterfactual_registry.get_operators(),')
            lines.append("}")
            lines.append("")
            lines.append("# Use consistent name for examples")
            lines.append("theory = cf_theory")
            lines.append("")
            lines.append('print("=" * 70)')
            lines.append(f'print("{theory_name.upper()} LOADED")')
            lines.append('print("=" * 70)')
            lines.append('print("\\nAvailable counterfactual operators:")')
            lines.append('print("  - Would-counterfactual: \\\\\\\\boxright (□→)")')
            lines.append('print("  - Might-counterfactual: \\\\\\\\diamondright (◇→)")')
            lines.append('print("\\nThe theory also includes classical and modal operators.")')
            lines.append('print("=" * 70)')
        else:
            # Standard Logos setup
            lines.append("# Create operator registry and load required subtheories")
            lines.append("registry = LogosOperatorRegistry()")
            
            # For generic Logos, load common subtheories
            lines.append("registry.load_subtheories(['extensional', 'modal'])")
            lines.append("")
            lines.append("# Build the semantic theory dictionary")
            lines.append("theory = {")
            lines.append('    "semantics": LogosSemantics,')
            lines.append('    "proposition": LogosProposition,')
            lines.append('    "model": LogosModelStructure,')
            lines.append('    "operators": registry.get_operators(),')
            lines.append("}")
            lines.append("")
            lines.append('print("=" * 70)')
            lines.append(f'print("{theory_name.upper()} LOADED")')
            lines.append('print("=" * 70)')
            lines.append('print("Using Logos framework with standard operators")')
            lines.append('print("Available operators:", ", ".join(theory["operators"].keys()))')
            lines.append('print("=" * 70)')
        
        return lines
    
    def _detect_subtheories_from_examples(self, example_range: Dict) -> Set[str]:
        """Detect required subtheories from operator usage in examples.
        
        Args:
            example_range: Dictionary of example definitions
            
        Returns:
            Set of subtheory names to load
        """
        subtheories = set(['extensional'])  # Always include extensional
        
        # Collect all formulas
        for name, definition in example_range.items():
            if isinstance(definition, (list, tuple)):
                premises = definition[0] if len(definition) > 0 else []
                conclusions = definition[1] if len(definition) > 1 else []
                
                # Check each formula for operator indicators
                for formula in premises + conclusions:
                    if isinstance(formula, str):
                        # Modal operators
                        if '\\Box' in formula or '\\Diamond' in formula:
                            subtheories.add('modal')
                        
                        # Counterfactual operators
                        if ('\\boxright' in formula or '\\diamondright' in formula or
                            '\\leadstoright' in formula or '\\leadstoleft' in formula):
                            subtheories.add('counterfactual')
                        
                        # Relevance operators
                        if ('\\sqsubseteq' in formula or '\\vDash' in formula or
                            '\\circledast' in formula or '\\preceq' in formula):
                            subtheories.add('relevance')
                        
                        # Constitutive operators
                        if ('\\square' in formula or '\\lozenge' in formula or
                            '\\sqsupseteq' in formula):
                            subtheories.add('constitutive')
        
        return subtheories