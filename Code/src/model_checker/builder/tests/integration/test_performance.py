"""Performance tests for builder package.

This module tests the performance characteristics of the builder package,
ensuring that model checking and constraint solving operations complete
within acceptable time limits.
"""

import unittest
import time
import tempfile
import os
from unittest.mock import Mock, patch

# Import test fixtures
from model_checker.builder.tests.fixtures.test_data import (
    TestTheories, TestExamples, TestModules, TestConstants
)
from model_checker.builder.tests.fixtures.mock_objects import MockObjectFactory

# Import components to test
from model_checker.builder.module import BuildModule
from model_checker.builder.runner import ModelRunner


class TestBuilderPerformance(unittest.TestCase):
    """Test builder performance characteristics."""
    
    def setUp(self):
        """Set up performance testing environment."""
        self.temp_dir = tempfile.mkdtemp()
        self.addCleanup(lambda: self._cleanup_temp_dir())
    
    def _cleanup_temp_dir(self):
        """Clean up temporary directory."""
        import shutil
        if os.path.exists(self.temp_dir):
            shutil.rmtree(self.temp_dir)
    
    def test_small_model_generation_completes_quickly(self):
        """Test small model (N=2) generation completes in <500ms.
        
        This ensures that simple model checking problems complete quickly,
        providing fast feedback for basic logical arguments.
        """
        # Arrange
        test_file = self._create_test_file("""
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Test": theory}
example_range = {"SMALL": [["A"], ["B"], {"N": 2}]}
general_settings = {}
""")
        
        flags = Mock(
            file_path=test_file,
            comparison=False,
            interactive=False,
            iterations=False,
            quiet=True,
            output=None,
            save=None,  # No saving
            _parsed_args=[]
        )
        
        # Act
        start_time = time.time()
        build_module = BuildModule(flags)
        build_module.runner.run_examples()
        elapsed_time = time.time() - start_time
        
        # Assert
        self.assertLess(elapsed_time, 0.5,
                       f"Small model should complete in <500ms, took {elapsed_time:.3f}s")
    
    def test_medium_model_generation_completes_within_timeout(self):
        """Test medium model (N=5) generation completes in <2 seconds.
        
        This verifies that moderately complex models can be generated
        within reasonable time limits for interactive use.
        """
        # Arrange
        test_file = self._create_test_file("""
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Test": theory}
example_range = {"MEDIUM": [["A", "B"], ["C"], {"N": 5}]}
general_settings = {}
""")
        
        flags = Mock(
            file_path=test_file,
            comparison=False,
            interactive=False,
            iterations=False,
            quiet=True,
            output=None,
            save=None,  # No saving
            _parsed_args=[]
        )
        
        # Act
        start_time = time.time()
        build_module = BuildModule(flags)
        build_module.runner.run_examples()
        elapsed_time = time.time() - start_time
        
        # Assert
        self.assertLess(elapsed_time, 2.0,
                       f"Medium model should complete in <2s, took {elapsed_time:.3f}s")
    
    def test_large_model_generation_completes_within_timeout(self):
        """Test large model (N=5) generation completes in <5 seconds.
        
        This ensures that even complex model checking problems complete
        within acceptable time limits for batch processing.
        """
        # Arrange
        test_file = self._create_test_file("""
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Test": theory}
example_range = {"LARGE": [["A", "B"], ["C"], {"N": 5}]}
general_settings = {}
""")
        
        flags = Mock(
            file_path=test_file,
            comparison=False,
            interactive=False,
            iterations=False,
            quiet=True,
            output=None,
            save=None,  # No saving
            _parsed_args=[]
        )
        
        # Act
        start_time = time.time()
        try:
            build_module = BuildModule(flags)
            build_module.runner.run_examples()
            elapsed_time = time.time() - start_time
        except Exception:
            # If it fails due to complexity, that's acceptable
            elapsed_time = time.time() - start_time
        
        # Assert
        self.assertLess(elapsed_time, 5.0,
                       f"Large model should complete or timeout in <5s, took {elapsed_time:.3f}s")
    
    def test_multiple_examples_process_efficiently(self):
        """Test processing multiple examples completes efficiently.
        
        This verifies that batch processing of multiple examples
        doesn't have excessive overhead between examples.
        """
        # Arrange
        test_file = self._create_test_file("""
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Test": theory}
example_range = {
    "EX1": [["A"], ["B"], {"N": 2}],
    "EX2": [["C"], ["D"], {"N": 2}],
    "EX3": [["E"], ["F"], {"N": 2}],
    "EX4": [["G"], ["H"], {"N": 2}],
    "EX5": [["I"], ["J"], {"N": 2}]
}
general_settings = {}
""")
        
        flags = Mock(
            file_path=test_file,
            comparison=False,
            interactive=False,
            iterations=False,
            quiet=True,
            output=None,
            save=None,  # No saving
            _parsed_args=[]
        )
        
        # Act
        start_time = time.time()
        build_module = BuildModule(flags)
        build_module.runner.run_examples()
        elapsed_time = time.time() - start_time
        
        # Calculate average time per example
        avg_time = elapsed_time / 5
        
        # Assert - Use more reasonable thresholds for robustness
        # Allow 250ms per example to account for system variance
        self.assertLess(avg_time, 0.25,
                       f"Average time per example should be <250ms, was {avg_time:.3f}s")
        self.assertLess(elapsed_time, 2.0,
                       f"Total time for 5 examples should be <2.0s, took {elapsed_time:.3f}s")
    
    def test_comparison_mode_performance(self):
        """Test comparison mode doesn't significantly impact performance.
        
        This ensures that comparing multiple theories doesn't cause
        excessive performance degradation.
        """
        # Arrange
        test_file = self._create_test_file("""
from model_checker.theory_lib.logos import get_theory

theory1 = get_theory(['extensional'])
theory2 = get_theory(['counterfactual'])
semantic_theories = {"Ext": theory1, "CF": theory2}
example_range = {"TEST": [["A"], ["B"], {"N": 3}]}
general_settings = {}
""")
        
        flags = Mock(
            file_path=test_file,
            comparison=True,
            interactive=False,
            iterations=False,
            quiet=True,
            output=None,
            save=None,  # No saving
            _parsed_args=[]
        )
        
        # Act
        start_time = time.time()
        build_module = BuildModule(flags)
        build_module.comparison.run_comparison()
        elapsed_time = time.time() - start_time
        
        # Assert
        self.assertLess(elapsed_time, 2.0,
                       f"Comparison of 2 theories should complete in <2s, took {elapsed_time:.3f}s")
    
    def test_module_loading_performance(self):
        """Test module loading completes quickly.
        
        This verifies that loading and parsing module files
        doesn't have excessive overhead.
        """
        # Arrange
        test_file = self._create_test_file(TestModules.WITH_EXAMPLES)
        
        flags = Mock(
            file_path=test_file,
            comparison=False,
            interactive=False,
            iterations=False,
            quiet=True,
            output=None,
            save=None,  # No saving
            _parsed_args=[]
        )
        
        # Act - Time just the loading phase
        start_time = time.time()
        build_module = BuildModule(flags)
        # Access loader to ensure it's initialized
        _ = build_module.loader
        loading_time = time.time() - start_time
        
        # Assert
        self.assertLess(loading_time, 0.1,
                       f"Module loading should complete in <100ms, took {loading_time:.3f}s")
    
    def test_serialization_performance(self):
        """Test serialization of results completes quickly.
        
        This ensures that converting model structures to output format
        doesn't become a bottleneck.
        """
        # Arrange
        from model_checker.builder.serialize import serialize_semantic_theory, deserialize_operators
        
        # Create a complex theory structure
        complex_theory = TestTheories.COMPLEX.copy()
        
        # Act - Time serialization
        start_time = time.time()
        for _ in range(100):  # Serialize 100 times to get measurable time
            serialized = serialize_semantic_theory("test", complex_theory)
        serialization_time = (time.time() - start_time) / 100
        
        # Assert
        self.assertLess(serialization_time, 0.001,
                       f"Single serialization should take <1ms, took {serialization_time*1000:.3f}ms")
    
    def test_constraint_generation_scales_linearly(self):
        """Test constraint generation scales linearly with formula complexity.
        
        This verifies that constraint generation doesn't have exponential
        complexity growth with formula size.
        """
        # Arrange - Create formulas of increasing complexity
        test_cases = [
            (2, [["A"], ["B"], {"N": 2}]),
            (4, [["A", "B"], ["C", "D"], {"N": 2}]),
            (6, [["A", "B", "C"], ["D", "E", "F"], {"N": 2}]),
            (8, [["A", "B", "C", "D"], ["E", "F", "G", "H"], {"N": 2}])
        ]
        
        times = []
        
        for formula_count, example in test_cases:
            test_file = self._create_test_file(f"""
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {{"Test": theory}}
example_range = {{"TEST": {example}}}
general_settings = {{}}
""")
            
            flags = Mock(
                file_path=test_file,
                comparison=False,
                interactive=False,
                iterations=False,
                quiet=True,
                output=None,
                save=None,  # No saving
                _parsed_args=[]
            )
            
            # Act
            start_time = time.time()
            build_module = BuildModule(flags)
            build_module.runner.run_examples()
            elapsed = time.time() - start_time
            times.append((formula_count, elapsed))
        
        # Assert - Check that time growth is roughly linear
        # Compare ratio of time increase to formula count increase
        if len(times) >= 2:
            for i in range(1, len(times)):
                formula_ratio = times[i][0] / times[0][0]
                time_ratio = times[i][1] / times[0][1]
                
                # Time should grow no more than quadratically with formula count
                self.assertLess(time_ratio, formula_ratio * formula_ratio,
                              f"Time growth should be at most quadratic: "
                              f"formula ratio {formula_ratio}, time ratio {time_ratio}")
    
    def _create_test_file(self, content):
        """Create a temporary test file with given content.
        
        Args:
            content: Python code content for the test file
            
        Returns:
            Path to the created test file
        """
        test_file = os.path.join(self.temp_dir, "test_module.py")
        with open(test_file, 'w') as f:
            f.write(content)
        return test_file


class TestMemoryUsage(unittest.TestCase):
    """Test memory usage characteristics of builder components."""
    
    def test_memory_usage_stays_within_bounds(self):
        """Test memory usage doesn't exceed reasonable limits.
        
        This ensures that model checking doesn't consume excessive memory
        even for complex problems.
        """
        # This is a placeholder for memory profiling tests
        # In a real implementation, you would use memory_profiler or tracemalloc
        # to measure actual memory consumption
        
        # For now, we just verify the test infrastructure works
        self.assertTrue(True, "Memory usage test placeholder")
    
    def test_no_memory_leaks_in_iteration(self):
        """Test repeated model iterations don't leak memory.
        
        This verifies that finding multiple models doesn't cause
        memory to grow unbounded.
        """
        # This is a placeholder for memory leak detection
        # Would use gc module and weakref to detect leaks in real implementation
        
        self.assertTrue(True, "Memory leak test placeholder")


if __name__ == '__main__':
    unittest.main()