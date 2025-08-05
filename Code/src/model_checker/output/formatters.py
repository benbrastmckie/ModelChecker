"""Formatters for converting model output to different formats."""

import re
from typing import Dict, Any, List


class MarkdownFormatter:
    """Formats model data and output as markdown.
    
    This class converts model data into human-readable markdown format
    with support for color indicators (emojis) or text-based state type
    indicators.
    """
    
    def __init__(self, use_colors: bool = True):
        """Initialize formatter.
        
        Args:
            use_colors: Whether to use color emojis for state types
        """
        self.use_colors = use_colors
        
    def format_example(self, example_data: Dict[str, Any], 
                      model_output: str) -> str:
        """Format complete example with markdown.
        
        Args:
            example_data: Dictionary containing model data
            model_output: Raw model output text
            
        Returns:
            Formatted markdown string
        """
        # Just return the model output without any headers or emoji sections
        if model_output:
            return model_output.strip()
        else:
            # If no model output, return a simple message
            example = example_data.get("example", "Unknown")
            if not example_data.get("has_model", False):
                return f"EXAMPLE {example}: there is no countermodel."
            else:
                return f"EXAMPLE {example}: model found but no output available."
        
    def format_state_type(self, state: str, state_type: str) -> str:
        """Format state with type indicator.
        
        Args:
            state: State name (e.g., "s0")
            state_type: Type of state ("possible", "impossible", "world", "evaluation")
            
        Returns:
            Formatted state string
        """
        if self.use_colors:
            return self._with_color_emoji(state, state_type)
        else:
            return f"{state} [{state_type.upper()}]"
            
    def _with_color_emoji(self, state: str, state_type: str) -> str:
        """Add color emoji based on state type.
        
        Args:
            state: State name
            state_type: Type of state
            
        Returns:
            State with emoji prefix
        """
        emoji_map = {
            "possible": "🟢",
            "impossible": "🔴",
            "world": "🔵",
            "evaluation": "⭐"
        }
        
        label_map = {
            "possible": "Possible",
            "impossible": "Impossible",
            "world": "World State",
            "evaluation": "Evaluation World"
        }
        
        emoji = emoji_map.get(state_type, "")
        label = label_map.get(state_type, state_type.title())
        
        return f"{emoji} {state} ({label})"
        
    def _format_header(self, example_data: Dict[str, Any]) -> str:
        """Format example header section."""
        example = example_data.get("example", "Unknown")
        theory = example_data.get("theory", "Unknown")
        has_model = example_data.get("has_model", False)
        
        # Just the example name as the header
        header = f"## {example}\\n\\n"
        
        # Add metadata as regular text
        header += f"**Theory**: {theory}\\n"
        header += f"**Model Found**: {'Yes' if has_model else 'No'}"
        
        return header
        
    def _format_states(self, example_data: Dict[str, Any]) -> str:
        """Format states section."""
        lines = ["### States\\n"]
        
        states = example_data.get("states", {})
        eval_world = example_data.get("evaluation_world")
        
        all_states = []
        
        # Collect all states with their types
        # First add world states
        for state in states.get("worlds", []):
            state_type = "evaluation" if state == eval_world else "world"
            all_states.append((state, state_type))
            
        # Then add possible states (non-world)
        for state in states.get("possible", []):
            if state not in states.get("worlds", []):
                state_type = "evaluation" if state == eval_world else "possible"
                all_states.append((state, state_type))
            
        # Finally add impossible states
        for state in states.get("impossible", []):
            all_states.append((state, "impossible"))
            
        # Sort states by number
        all_states.sort(key=lambda x: int(x[0][1:]) if x[0][1:].isdigit() else 0)
        
        # Format each state
        for state, state_type in all_states:
            lines.append(f"- {self.format_state_type(state, state_type)}")
            
        return "\\n".join(lines)
        
    def _format_relations(self, example_data: Dict[str, Any]) -> str:
        """Format relations section."""
        lines = ["### Relations\\n"]
        
        relations = example_data.get("relations", {})
        
        for rel_name, connections in relations.items():
            lines.append(f"#### {rel_name} Relation\\n")
            
            # Handle different relation structures
            if rel_name == "time_shift":
                # Bimodal time shift relations: {world: {shift: target}}
                sorted_worlds = sorted(connections.items(), 
                                     key=lambda x: int(x[0][1:]) if x[0][1:].isdigit() else 0)
                
                for world, shifts in sorted_worlds:
                    for shift, target in sorted(shifts.items(), key=lambda x: int(x[0]) if x[0].lstrip('-').isdigit() else 0):
                        lines.append(f"- {world} →_{{{shift}}} {target}")
                        
            elif rel_name == "imposition":
                # Imposition relations: {world: {state: outcome}}
                sorted_worlds = sorted(connections.items(), 
                                     key=lambda x: int(x[0][1:]) if x[0][1:].isdigit() else 0)
                
                for world, impositions in sorted_worlds:
                    for state, outcome in sorted(impositions.items(), 
                                               key=lambda x: int(x[0][1:]) if x[0][1:].isdigit() else 0):
                        lines.append(f"- {world} →_{{{state}}} {outcome}")
                        
            elif rel_name == "excludes":
                # Exclusion relations: {state: [excluded_states]}
                sorted_states = sorted(connections.items(), 
                                     key=lambda x: int(x[0][1:]) if x[0][1:].isdigit() else 0)
                
                for state, excluded in sorted_states:
                    if excluded:
                        excluded_str = ", ".join(sorted(excluded))
                        lines.append(f"- {state} ⊥ {excluded_str}")
                        
            else:
                # Default handling for R relations and others
                sorted_connections = sorted(connections.items(), 
                                          key=lambda x: int(x[0][1:]) if x[0][1:].isdigit() else 0)
                
                for source, targets in sorted_connections:
                    if isinstance(targets, list):
                        if targets:
                            target_str = ", ".join(sorted(targets))
                            lines.append(f"- {source} → {target_str}")
                        else:
                            lines.append(f"- {source} → ∅")
                    else:
                        # Single target
                        lines.append(f"- {source} → {targets}")
                    
        return "\\n".join(lines)
        
    def _format_propositions(self, example_data: Dict[str, Any]) -> str:
        """Format propositions section."""
        lines = ["### Propositions\\n"]
        
        propositions = example_data.get("propositions", {})
        
        for prop, truth_values in sorted(propositions.items()):
            truth_str = ", ".join(
                f"{world} {'✓' if is_true else '✗'}"
                for world, is_true in sorted(truth_values.items())
            )
            lines.append(f"- **{prop}**: {truth_str}")
            
        return "\\n".join(lines)
        
    def _format_output(self, model_output: str) -> str:
        """Format raw model output section."""
        lines = ["### Model Output\\n"]
        lines.append("```")
        lines.append(model_output.strip())
        lines.append("```")
        
        return "\\n".join(lines)


class ANSIToMarkdown:
    """Converts ANSI escape codes to markdown formatting.
    
    This class handles the conversion of ANSI color codes commonly used
    in terminal output to markdown-friendly formatting.
    """
    
    def convert(self, ansi_text: str) -> str:
        """Convert ANSI escape codes to markdown.
        
        Args:
            ansi_text: Text containing ANSI escape codes
            
        Returns:
            Markdown formatted text
        """
        # Pattern to match ANSI escape sequences
        ansi_pattern = re.compile(r'\033\[([0-9;]+)m')
        
        # First pass: identify color regions
        # Red (31) -> Bold in markdown
        # Green (32) -> Italic in markdown
        # Reset (0) -> End formatting
        
        result = ansi_text
        
        # Convert red text to bold (non-greedy match)
        result = re.sub(r'\033\[31m([^\033]*?)\033\[0m', r'**\1**', result)
        
        # Convert green text to italic (non-greedy match)
        result = re.sub(r'\033\[32m([^\033]*?)\033\[0m', r'_\1_', result)
        
        # Handle unclosed color codes at boundaries
        result = re.sub(r'\033\[31m(.*?)$', r'**\1**', result)
        result = re.sub(r'\033\[32m(.*?)$', r'_\1_', result)
        
        # Strip any remaining ANSI codes
        result = ansi_pattern.sub('', result)
        
        return result