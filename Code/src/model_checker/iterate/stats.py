"""Statistics collection for model iteration."""

from typing import List, Dict, Any
import time


class IterationStatistics:
    """Collect and analyze statistics about found models."""
    
    def __init__(self):
        self.model_stats = []
    
    def add_model(self, model_structure, differences: Dict[str, Any]):
        """Add statistics for a found model."""
        stats = {
            'world_count': len(getattr(model_structure, 'z3_world_states', [])),
            'possible_count': len(getattr(model_structure, 'z3_possible_states', [])),
            'difference_count': self._count_differences(differences),
            'timestamp': time.time(),
        }
        self.model_stats.append(stats)
    
    def _count_differences(self, differences: Dict[str, Any]) -> int:
        """Count total number of differences."""
        count = 0
        for category, changes in differences.items():
            if isinstance(changes, dict):
                if 'added' in changes:
                    count += len(changes['added'])
                if 'removed' in changes:
                    count += len(changes['removed'])
                # Count other changes
                for k, v in changes.items():
                    if k not in ['added', 'removed'] and isinstance(v, dict):
                        count += len(v)
        return count
    
    def get_summary(self) -> Dict[str, Any]:
        """Get summary statistics."""
        if not self.model_stats:
            return {}
        
        world_counts = [m['world_count'] for m in self.model_stats]
        diff_counts = [m['difference_count'] for m in self.model_stats[1:]]
        
        # Calculate average safely
        avg_worlds = sum(world_counts) / len(world_counts) if world_counts else 0
        avg_differences = sum(diff_counts) / len(diff_counts) if diff_counts else 0
        
        return {
            'total_models': len(self.model_stats),
            'avg_worlds': avg_worlds,
            'world_diversity': len(set(world_counts)),
            'avg_differences': avg_differences,
            'max_differences': max(diff_counts) if diff_counts else 0,
        }
    
    def print_summary(self):
        """Print a summary of iteration statistics."""
        stats = self.get_summary()
        if not stats:
            return
        
        print("\n=== Iteration Statistics ===")
        print(f"Total models found: {stats['total_models']}")
        print(f"Average worlds per model: {stats['avg_worlds']:.1f}")
        print(f"World count diversity: {stats['world_diversity']} different counts")
        if stats['avg_differences'] > 0:
            print(f"Average differences between consecutive models: {stats['avg_differences']:.1f}")
            print(f"Maximum differences: {stats['max_differences']}")