"""Model checking comparison engine.

This module handles comparison of different semantic theories by testing
their performance at increasing model sizes.
"""

# Standard library imports
import os
import time
from concurrent.futures import ProcessPoolExecutor, TimeoutError
from typing import List, Tuple, Dict, Any, TYPE_CHECKING

# Relative imports
from .serialize import serialize_semantic_theory

if TYPE_CHECKING:
    from .module import BuildModule


def _find_max_N_static(theory_name: str, theory_config: Dict[str, Any], example_case: List[Any]) -> int:
    """Static method to find maximum N for a theory (can be pickled).
    
    This static method is designed for use with ProcessPoolExecutor.
    It deserializes the theory configuration and tests incrementally larger
    values of N until a timeout occurs.
    
    Args:
        theory_name: Name of the theory being tested
        theory_config: Serialized theory configuration
        example_case: Example case with premises, conclusions, and settings
        
    Returns:
        int: Maximum N value that succeeded within time limit
    """
    # Import here to avoid circular imports in subprocess
    from model_checker.builder.runner import ModelRunner
    
    premises, conclusions, settings = example_case
    current_N = settings.get('N', 2)
    max_N = 0
    
    # Create a mock build module for the runner
    class MockBuildModule:
        def __init__(self):
            self.general_settings = settings
            
            
            
        def _capture_and_save_output(self, example, example_name, theory_name, model_num=None):
            # No-op for comparison
            pass
    
    mock_module = MockBuildModule()
    
    while True:
        # Update N in settings
        test_settings = settings.copy()
        test_settings['N'] = current_N
        test_case = [premises, conclusions, test_settings]
        
        # Use runner's static method
        from model_checker.builder.runner import try_single_N_static
        success, runtime = try_single_N_static(
            theory_name,
            theory_config,
            test_case
        )
        
        if success:
            max_N = current_N
            current_N += 1
        else:
            break
    
    return max_N


class ModelComparison:
    """Compares performance of different semantic theories."""
    
    def __init__(self, build_module: 'BuildModule') -> None:
        """Initialize with reference to parent BuildModule for settings.
        
        Args:
            build_module: Parent BuildModule instance for accessing settings
                          and utility methods
        """
        self.build_module = build_module
        self.settings = build_module.general_settings
    
    def compare_semantics(self, example_theory_tuples: List[Tuple[str, Dict[str, Any], List[Any]]]) -> List[Tuple[str, int]]:
        """Compare different semantic theories by finding maximum model sizes.
        
        This method attempts to find the maximum model size (N) for each semantic theory
        by incrementally testing larger values of N until a timeout occurs. It runs the
        tests concurrently using a ProcessPoolExecutor for better performance.
        
        The method now uses serialization to avoid pickle errors with complex objects.
        
        Args:
            example_theory_tuples: List of tuples containing (theory_name, semantic_theory, example_case)
                where example_case is [premises, conclusions, settings]
                
        Returns:
            list: List of tuples containing (theory_name, max_N) where max_N is the largest
                  number of worlds for which a model was found within the time limit
        """
        results = []
        max_workers = min(os.cpu_count(), len(example_theory_tuples))
        
        with ProcessPoolExecutor(max_workers=max_workers) as executor:
            # Prepare serialized data for each theory
            futures = []
            
            for theory_name, semantic_theory, example_case in example_theory_tuples:
                # Serialize the semantic theory configuration
                theory_config = serialize_semantic_theory(theory_name, semantic_theory)
                
                future = executor.submit(
                    _find_max_N_static,
                    theory_name, 
                    theory_config,
                    example_case
                )
                futures.append((future, theory_name))
            
            # Collect results
            for future, theory_name in futures:
                try:
                    max_N = future.result(timeout=300)  # 5-minute overall timeout
                    results.append((theory_name, max_N))
                except TimeoutError:
                    results.append((theory_name, 0))
                except Exception as e:
                    print(f"Error processing {theory_name}: {e}")
                    results.append((theory_name, 0))
        
        return results
    
    def run_comparison(self) -> None:
        """Compare different semantic theories by running examples and printing results.
        
        Iterates through each example in example_range and runs it against all semantic theories.
        For each example:
        1. Prints example name and details (premises and conclusions)  
        2. Translates operators according to each theory's dictionary
        3. Compares semantic theories by finding maximum model sizes
        4. Prints results showing which theories could handle larger models
        """
        from model_checker.models.constraints import ModelConstraints
        
        print()
        for example_name, example_case in self.build_module.example_range.items():
            premises, conclusions, settings = example_case
            print(f"{'='*40}\n")
            print(f"EXAMPLE {example_name}:")
            print(f"  Premises: {premises}")
            print(f"  Conclusions: {conclusions}\n")
            
            # Create list of (theory_name, semantic_theory, example_case) tuples
            example_theory_tuples = []
            for theory_name, semantic_theory in self.build_module.semantic_theories.items():
                # Apply translation if needed
                dictionary = semantic_theory.get("dictionary", None)
                if dictionary:
                    translated_case = self.build_module.translation.translate(example_case, dictionary)
                else:
                    translated_case = example_case
                
                example_theory_tuples.append((theory_name, semantic_theory, translated_case))
            
            # Compare semantic theories
            comparison_results = self.compare_semantics(example_theory_tuples)
            
            # Sort results by max_N (descending)
            comparison_results.sort(key=lambda x: x[1], reverse=True)
            
            # Print results
            print("Comparison Results:")
            for theory_name, max_N in comparison_results:
                print(f"  {theory_name}: Maximum N = {max_N}")
            print()
        
        print(f"{'='*40}\n")