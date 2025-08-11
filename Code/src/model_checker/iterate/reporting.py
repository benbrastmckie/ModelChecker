"""Results formatting and reporting for model iteration.

This module handles calculating differences between models, formatting
results for output, and generating iteration reports.
"""

import logging

logger = logging.getLogger(__name__)


class DifferenceCalculator:
    """Calculates differences between model structures."""
    
    def calculate_differences(self, new_structure, previous_structure):
        """Calculate differences between two model structures.
        
        Args:
            new_structure: New model structure
            previous_structure: Previous model structure to compare against
            
        Returns:
            dict: Dictionary containing all calculated differences
        """
        differences = {}
        
        try:
            # Calculate basic differences
            basic_diffs = self._calculate_basic_differences(new_structure, previous_structure)
            differences.update(basic_diffs)
            
            # Calculate semantic differences if available
            semantic_diffs = self._calculate_semantic_differences(new_structure, previous_structure)
            differences.update(semantic_diffs)
            
            # Calculate state differences
            state_diffs = self._calculate_state_differences(new_structure, previous_structure)
            differences.update(state_diffs)
            
        except Exception as e:
            logger.warning(f"Error calculating differences: {e}")
            differences['error'] = str(e)
            
        return differences
    
    def _calculate_basic_differences(self, new_structure, previous_structure):
        """Calculate basic structural differences.
        
        Args:
            new_structure: New model structure
            previous_structure: Previous model structure
            
        Returns:
            dict: Basic difference information
        """
        differences = {}
        
        try:
            # World state differences
            new_worlds = set(getattr(new_structure, 'z3_world_states', []))
            prev_worlds = set(getattr(previous_structure, 'z3_world_states', []))
            
            world_added = new_worlds - prev_worlds
            world_removed = prev_worlds - new_worlds
            
            differences['world_changes'] = {
                'added': list(world_added),
                'removed': list(world_removed),
                'total_change_count': len(world_added) + len(world_removed)
            }
            
            # Possible state differences
            new_possible = set(getattr(new_structure, 'z3_possible_states', []))
            prev_possible = set(getattr(previous_structure, 'z3_possible_states', []))
            
            possible_added = new_possible - prev_possible
            possible_removed = prev_possible - new_possible
            
            differences['possible_changes'] = {
                'added': list(possible_added),
                'removed': list(possible_removed),
                'total_change_count': len(possible_added) + len(possible_removed)
            }
            
        except Exception as e:
            logger.warning(f"Error calculating basic differences: {e}")
            differences['basic_error'] = str(e)
            
        return differences
    
    def _calculate_semantic_differences(self, new_structure, previous_structure):
        """Calculate semantic differences between models.
        
        Args:
            new_structure: New model structure
            previous_structure: Previous model structure
            
        Returns:
            dict: Semantic difference information
        """
        differences = {}
        
        try:
            # Get atomic propositions that have changed
            atom_changes = self._calculate_atomic_changes(new_structure, previous_structure)
            if atom_changes:
                differences['atomic_changes'] = atom_changes
                
        except Exception as e:
            logger.warning(f"Error calculating semantic differences: {e}")
            differences['semantic_error'] = str(e)
            
        return differences
    
    def _calculate_state_differences(self, new_structure, previous_structure):
        """Calculate detailed state-by-state differences.
        
        Args:
            new_structure: New model structure
            previous_structure: Previous model structure
            
        Returns:
            dict: State difference information
        """
        differences = {}
        
        try:
            # Get state evaluation differences
            state_evals = self._compare_state_evaluations(new_structure, previous_structure)
            if state_evals:
                differences['state_evaluations'] = state_evals
                
        except Exception as e:
            logger.warning(f"Error calculating state differences: {e}")
            differences['state_error'] = str(e)
            
        return differences
    
    def _calculate_atomic_changes(self, new_structure, previous_structure):
        """Calculate changes in atomic proposition evaluations.
        
        Args:
            new_structure: New model structure
            previous_structure: Previous model structure
            
        Returns:
            dict: Atomic proposition changes
        """
        changes = {}
        
        try:
            # This would require access to the verification/falsification results
            # For now, we'll return a placeholder
            changes['verification_changes'] = self._get_verification_changes(new_structure, previous_structure)
            changes['falsification_changes'] = self._get_falsification_changes(new_structure, previous_structure)
            
        except Exception as e:
            logger.warning(f"Error calculating atomic changes: {e}")
            
        return changes
    
    def _get_verification_changes(self, new_structure, previous_structure):
        """Get verification changes between models.
        
        Args:
            new_structure: New model structure
            previous_structure: Previous model structure
            
        Returns:
            dict: Verification changes by letter
        """
        # This is a placeholder - real implementation would need to access
        # the verification results from the model structures
        return {}
    
    def _get_falsification_changes(self, new_structure, previous_structure):
        """Get falsification changes between models.
        
        Args:
            new_structure: New model structure
            previous_structure: Previous model structure
            
        Returns:
            dict: Falsification changes by letter
        """
        # This is a placeholder - real implementation would need to access
        # the falsification results from the model structures
        return {}
    
    def _compare_state_evaluations(self, new_structure, previous_structure):
        """Compare state-by-state evaluations between models.
        
        Args:
            new_structure: New model structure
            previous_structure: Previous model structure
            
        Returns:
            dict: State evaluation comparisons
        """
        comparisons = {}
        
        try:
            # Get all states from both structures
            new_worlds = set(getattr(new_structure, 'z3_world_states', []))
            prev_worlds = set(getattr(previous_structure, 'z3_world_states', []))
            all_states = new_worlds.union(prev_worlds)
            
            for state in all_states:
                state_info = {}
                
                # Check world status change
                was_world = state in prev_worlds
                is_world = state in new_worlds
                
                if was_world != is_world:
                    state_info['world_status_changed'] = {
                        'was_world': was_world,
                        'is_world': is_world
                    }
                
                if state_info:
                    comparisons[f'state_{state}'] = state_info
                    
        except Exception as e:
            logger.warning(f"Error comparing state evaluations: {e}")
            
        return comparisons


class ResultFormatter:
    """Formats iteration results for display."""
    
    def format_iteration_summary(self, model_structures, statistics, elapsed_time):
        """Format a complete iteration summary.
        
        Args:
            model_structures: List of found model structures
            statistics: Iteration statistics object
            elapsed_time: Total elapsed time
            
        Returns:
            str: Formatted summary
        """
        lines = []
        
        # Header
        found_count = len(model_structures)
        lines.append(f"\n{'='*50}")
        lines.append(f"ITERATION SUMMARY")
        lines.append(f"{'='*50}")
        
        # Basic stats
        lines.append(f"Models found: {found_count}")
        lines.append(f"Total time: {elapsed_time:.2f} seconds")
        
        if hasattr(statistics, 'get_summary'):
            summary = statistics.get_summary()
            
            # Detailed statistics
            lines.append(f"Models checked: {summary.get('total_checked', 'N/A')}")
            lines.append(f"Success rate: {summary.get('success_rate', 0):.1%}")
            
            if 'average_model_time' in summary:
                lines.append(f"Average time per model: {summary['average_model_time']:.3f}s")
        
        lines.append(f"{'='*50}")
        
        return "\n".join(lines)
    
    def format_difference_report(self, differences):
        """Format differences between models for display.
        
        Args:
            differences: Difference dictionary from DifferenceCalculator
            
        Returns:
            str: Formatted difference report
        """
        lines = []
        
        lines.append("\n=== DIFFERENCES FROM PREVIOUS MODEL ===")
        
        # World changes
        if 'world_changes' in differences:
            world_changes = differences['world_changes']
            if world_changes['added'] or world_changes['removed']:
                lines.append("\nWorld Changes:")
                for state in world_changes['added']:
                    lines.append(f"  + State {state} (now a world)")
                for state in world_changes['removed']:
                    lines.append(f"  - State {state} (no longer a world)")
        
        # Possible state changes
        if 'possible_changes' in differences:
            possible_changes = differences['possible_changes']
            if possible_changes['added'] or possible_changes['removed']:
                lines.append("\nPossible State Changes:")
                for state in possible_changes['added']:
                    lines.append(f"  + State {state} (now possible)")
                for state in possible_changes['removed']:
                    lines.append(f"  - State {state} (now impossible)")
        
        # Atomic changes
        if 'atomic_changes' in differences:
            atomic_changes = differences['atomic_changes']
            if atomic_changes.get('verification_changes'):
                lines.append("\nVerification Changes:")
                # Format verification changes
            if atomic_changes.get('falsification_changes'):
                lines.append("\nFalsification Changes:")
                # Format falsification changes
        
        if len(lines) == 1:  # Only header was added
            lines.append("No significant differences detected.")
        
        return "\n".join(lines)
    
    def format_progress_update(self, current, total, checked, elapsed_time):
        """Format a progress update message.
        
        Args:
            current: Current number of models found
            total: Total models requested
            checked: Total models checked so far
            elapsed_time: Elapsed time in seconds
            
        Returns:
            str: Formatted progress message
        """
        progress_bar = self._create_progress_bar(current, total)
        return f"Finding {total} models: {progress_bar} {current}/{total} (checked {checked}) {elapsed_time:.1f}s"
    
    def _create_progress_bar(self, current, total, width=30):
        """Create a text-based progress bar.
        
        Args:
            current: Current progress value
            total: Total/maximum value
            width: Width of progress bar in characters
            
        Returns:
            str: Progress bar string
        """
        if total == 0:
            return "[" + "░" * width + "]"
            
        progress = current / total
        filled_width = int(progress * width)
        
        bar = "█" * filled_width + "░" * (width - filled_width)
        return f"[{bar}]"