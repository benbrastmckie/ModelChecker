"""Search statistics tracking for model iteration.

This module provides data structures and utilities for tracking detailed
statistics about the search process for each model during iteration.
"""

from dataclasses import dataclass
from typing import Optional, List


@dataclass
class SearchStatistics:
    """Statistics for a single model search.
    
    Tracks the effort required to find (or fail to find) a specific model
    during the iteration process.
    
    Attributes:
        model_number: The model number being searched for (1-based)
        found: Whether the model was successfully found
        isomorphic_skipped: Number of isomorphic models skipped during this search
        models_checked: Total number of models checked during this search
        search_duration: Time taken for this search in seconds
        termination_reason: Reason for search termination if not found
    """
    model_number: int
    found: bool
    isomorphic_skipped: int
    models_checked: int
    search_duration: float
    termination_reason: Optional[str] = None
    
    def summary_line(self) -> str:
        """Generate a summary line for this search."""
        if self.model_number == 1:
            return "Model 1: Initial model (given)"
            
        if self.found:
            plural = 's' if self.isomorphic_skipped != 1 else ''
            return (f"Model {self.model_number}: Found after skipping "
                   f"{self.isomorphic_skipped} isomorphic model{plural} "
                   f"({self.search_duration:.2f}s)")
        else:
            reason = self.termination_reason or "exhausted search space"
            return (f"Model {self.model_number}: Not found - {reason} "
                   f"after checking {self.models_checked} models "
                   f"({self.search_duration:.2f}s)")


class IterationReportGenerator:
    """Generates comprehensive iteration search reports."""
    
    def generate_report(self, search_stats: List[SearchStatistics], 
                       total_requested: int, total_elapsed: float, 
                       initial_search_time: float = 0.0) -> str:
        """Generate formatted report of iteration search statistics.
        
        Args:
            search_stats: List of search statistics for each model search
            total_requested: Total number of models requested
            total_elapsed: Total elapsed time for entire iteration
            initial_search_time: Time taken to find the initial model
            
        Returns:
            Formatted report string
        """
        lines = []
        lines.append("ITERATION REPORT")
        
        # Model 1 shows actual search time
        lines.append(f"    Model 1: Initial model ({initial_search_time:.2f}s)")
        
        # Report on each search with indentation
        for stat in search_stats:
            if stat.model_number > 1:  # Skip model 1 as it's handled above
                lines.append("    " + stat.summary_line())
        
        # Summary line
        total_found = sum(1 for s in search_stats if s.found) + 1  # +1 for initial
        # Only count skipped from successful searches
        total_skipped = sum(s.isomorphic_skipped for s in search_stats if s.found)
        
        plural_models = 's' if total_skipped != 1 else ''
        lines.append(f"\nTotal: {total_found}/{total_requested} models found, "
                    f"{total_skipped} isomorphic model{plural_models} skipped, "
                    f"{total_elapsed:.2f}s elapsed")
        
        # Add final divider
        lines.append("\n" + "="*40)
        
        return "\n".join(lines)
