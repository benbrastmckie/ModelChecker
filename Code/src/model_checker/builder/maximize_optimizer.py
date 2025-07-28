"""
Optimizer for maximize mode performance improvements.

This module provides optimizations for the maximize comparison mode including:
1. Adaptive timeout strategies
2. Early termination conditions
3. Parallel processing improvements
4. Caching mechanisms
"""

import concurrent.futures
import time
from typing import Dict, List, Tuple, Any


class MaximizeOptimizer:
    """
    Provides optimization strategies for maximize mode.
    """
    
    def __init__(self):
        self.performance_cache = {}
        self.timeout_multiplier = 1.5
        self.max_n_limit = 7  # Stop at N=7 to prevent excessive computation
        self.early_termination_threshold = 10  # Stop if runtime > 10x max_time
    
    def get_adaptive_timeout(self, initial_n: int, current_n: int, base_timeout: float) -> float:
        """
        Calculate adaptive timeout based on N growth.
        
        As N increases, the state space grows exponentially (2^N),
        so we increase the timeout accordingly.
        """
        n_difference = current_n - initial_n
        # Exponential timeout growth matching state space growth
        return base_timeout * (self.timeout_multiplier ** n_difference)
    
    def should_terminate_early(self, runtime: float, max_time: float, n: int) -> bool:
        """
        Determine if we should stop testing higher N values.
        
        Early termination conditions:
        1. N exceeds maximum limit
        2. Runtime is significantly over timeout
        3. Performance degradation detected
        """
        if n >= self.max_n_limit:
            return True
        
        if runtime > max_time * self.early_termination_threshold:
            return True
        
        # Check performance cache for degradation patterns
        if n > 3 and n-1 in self.performance_cache:
            prev_runtime = self.performance_cache[n-1]
            if runtime > prev_runtime * 4:  # 4x slower than previous N
                return True
        
        return False
    
    def optimize_example_order(self, example_cases: List[Tuple]) -> List[Tuple]:
        """
        Reorder examples to process simpler ones first.
        
        This helps establish performance baselines and can lead to
        earlier termination for complex examples.
        """
        def complexity_score(case):
            _, _, (premises, conclusions, settings) = case
            # Score based on formula count and initial N
            return len(premises) + len(conclusions) + settings.get('N', 3)
        
        return sorted(example_cases, key=complexity_score)
    
    def create_optimized_settings(self, original_settings: Dict, n: int) -> Dict:
        """
        Create optimized settings for a specific N value.
        """
        settings = original_settings.copy()
        settings['N'] = n
        
        # Adjust timeout based on N
        initial_n = original_settings.get('N', 3)
        base_timeout = original_settings.get('max_time', 1)
        settings['max_time'] = self.get_adaptive_timeout(initial_n, n, base_timeout)
        
        return settings
    
    def parallel_n_search(self, theory_configs: List[Tuple], max_workers: int = None) -> Dict:
        """
        Optimized parallel search for maximum N values.
        
        Uses binary search strategy instead of linear increment
        for faster convergence to maximum N.
        """
        results = {}
        
        with concurrent.futures.ProcessPoolExecutor(max_workers=max_workers) as executor:
            # Use binary search for each theory
            futures = {}
            
            for theory_name, theory_config, example_case in theory_configs:
                # Initialize binary search bounds
                min_n = example_case[2]['N']  # Starting N
                max_n = self.max_n_limit
                
                # Submit initial probe at middle point
                mid_n = (min_n + max_n) // 2
                settings = self.create_optimized_settings(example_case[2], mid_n)
                future = executor.submit(
                    self._test_single_n, 
                    theory_name, theory_config, 
                    [example_case[0], example_case[1], settings]
                )
                futures[future] = (theory_name, min_n, max_n, mid_n)
            
            # Process results and refine search
            while futures:
                done, _ = concurrent.futures.wait(
                    futures, 
                    return_when=concurrent.futures.FIRST_COMPLETED
                )
                
                for future in done:
                    theory_name, min_n, max_n, test_n = futures.pop(future)
                    
                    try:
                        success, runtime = future.result()
                        
                        # Update performance cache
                        self.performance_cache[test_n] = runtime
                        
                        if success and not self.should_terminate_early(runtime, 
                                                                      example_case[2]['max_time'], 
                                                                      test_n):
                            # Success - try higher N
                            new_min_n = test_n + 1
                            if new_min_n <= max_n:
                                mid_n = (new_min_n + max_n) // 2
                                settings = self.create_optimized_settings(example_case[2], mid_n)
                                future = executor.submit(
                                    self._test_single_n,
                                    theory_name, theory_config,
                                    [example_case[0], example_case[1], settings]
                                )
                                futures[future] = (theory_name, new_min_n, max_n, mid_n)
                            else:
                                # Found maximum
                                results[theory_name] = test_n
                        else:
                            # Failure - try lower N
                            new_max_n = test_n - 1
                            if min_n <= new_max_n:
                                mid_n = (min_n + new_max_n) // 2
                                settings = self.create_optimized_settings(example_case[2], mid_n)
                                future = executor.submit(
                                    self._test_single_n,
                                    theory_name, theory_config,
                                    [example_case[0], example_case[1], settings]
                                )
                                futures[future] = (theory_name, min_n, new_max_n, mid_n)
                            else:
                                # Found maximum
                                results[theory_name] = min_n - 1
                    
                    except Exception as e:
                        print(f"Error testing {theory_name} at N={test_n}: {e}")
                        results[theory_name] = min_n - 1
        
        return results
    
    def _test_single_n(self, theory_name, theory_config, example_case):
        """
        Test a single N value (stub - would call actual test method).
        """
        # This would call the actual try_single_N_static method
        # For now, return mock results
        import random
        success = random.random() > 0.3
        runtime = random.uniform(0.1, 2.0)
        return success, runtime


class SmartMaximizeStrategy:
    """
    Implements smart strategies for maximize mode.
    """
    
    def __init__(self):
        self.optimizer = MaximizeOptimizer()
        self.results_cache = {}
    
    def run_smart_comparison(self, example_theory_tuples: List[Tuple]) -> List[Tuple]:
        """
        Run comparison with smart optimizations.
        
        1. Reorder examples by complexity
        2. Use binary search for N values
        3. Apply early termination
        4. Cache and reuse results
        """
        # Check cache first
        cache_key = str(example_theory_tuples)
        if cache_key in self.results_cache:
            return self.results_cache[cache_key]
        
        # Optimize order
        optimized_tuples = self.optimizer.optimize_example_order(example_theory_tuples)
        
        # Run parallel search with optimizations
        results = self.optimizer.parallel_n_search(optimized_tuples)
        
        # Convert to expected format
        formatted_results = [(name, max_n) for name, max_n in results.items()]
        
        # Cache results
        self.results_cache[cache_key] = formatted_results
        
        return formatted_results
    
    def estimate_runtime(self, n: int, base_time: float = 0.1) -> float:
        """
        Estimate runtime for a given N value.
        
        Assumes exponential growth: O(2^N)
        """
        return base_time * (2 ** (n - 3))  # Normalized to N=3
    
    def suggest_settings(self, example_complexity: int) -> Dict:
        """
        Suggest optimal settings based on example complexity.
        """
        if example_complexity < 5:
            return {
                'initial_n': 3,
                'max_time': 1,
                'max_n_limit': 6
            }
        elif example_complexity < 10:
            return {
                'initial_n': 2,
                'max_time': 2,
                'max_n_limit': 5
            }
        else:
            return {
                'initial_n': 2,
                'max_time': 5,
                'max_n_limit': 4
            }