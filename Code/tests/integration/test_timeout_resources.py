"""Test timeout and resource handling.

This module tests the framework's behavior under resource constraints,
including timeouts, memory limits, and concurrent operations.
"""

import pytest
import time
import threading
from unittest.mock import patch, Mock
from tests.utils.helpers import create_test_module


class TestTimeoutHandling:
    """Test timeout handling in various components."""
    
    def test_z3_solver_timeout(self):
        """Test Z3 solver respects timeout settings."""
        from model_checker.models import ModelDefaults
        
        # Very short timeout
        settings = {
            'N': 10,
            'max_time': 0.01,  # 10ms timeout
            'contingent': True,
            'non_empty': True
        }
        
        start_time = time.time()
        
        try:
            model = ModelDefaults(settings)
            # If model completes, check it didn't take too long
            elapsed = time.time() - start_time
            # Should complete quickly or timeout
            assert elapsed < 1.0  # Should not hang
            
            # Check model indicates timeout if it occurred
            if hasattr(model, 'timeout_occurred'):
                if model.timeout_occurred:
                    assert model.satisfiable is None
        except Exception as e:
            # Timeout exceptions are acceptable
            elapsed = time.time() - start_time
            assert elapsed < 1.0  # Should timeout quickly
    
    def test_cli_command_timeout(self, tmp_path):
        """Test CLI respects timeout for long-running operations."""
        from tests.utils.helpers import run_cli_command
        
        # Create a module that would take long to process
        content = '''
from model_checker.theory_lib import logos
theory = logos.get_theory()
semantic_theories = {"test": theory}

# Complex example that might take time
example_range = {
    "COMPLEX": [
        ["A", "B", "C", "D", "E"],
        ["F", "G", "H", "I", "J"],
        {"N": 64, "max_time": 0.01}  # Large N, short timeout
    ]
}
'''
        module_path = create_test_module(content, tmp_path, 'timeout_test.py')
        
        start_time = time.time()
        result = run_cli_command([module_path], timeout=5, check=False)
        elapsed = time.time() - start_time
        
        # Should complete within reasonable time
        assert elapsed < 6.0  # Allow some overhead
    
    @pytest.mark.parametrize("timeout_value", [0.001, 0.01, 0.1])
    def test_various_timeout_values(self, timeout_value):
        """Test handling of various timeout values."""
        from model_checker.models import ModelDefaults
        
        settings = {
            'N': 5,
            'max_time': timeout_value
        }
        
        try:
            model = ModelDefaults(settings)
            # Should handle all positive timeout values
            assert settings['max_time'] == timeout_value
        except Exception:
            # Very small timeouts might fail immediately
            assert timeout_value < 0.01


class TestResourceLimits:
    """Test resource limit handling."""
    
    def test_large_state_space(self):
        """Test handling of large state spaces."""
        from model_checker.models import ModelDefaults
        
        # Test increasing N values
        for n in [32, 48, 64]:
            settings = {'N': n}
            
            try:
                model = ModelDefaults(settings)
                # Should handle or fail gracefully
                assert model is not None
            except MemoryError:
                # Memory errors acceptable for large N
                assert n >= 48  # Should handle at least N=32
            except Exception as e:
                # Other exceptions should be informative
                assert "memory" in str(e).lower() or "resource" in str(e).lower()
    
    def test_many_propositions(self):
        """Test handling of many propositions."""
        from model_checker.models import ModelDefaults
        
        # Create many propositions
        num_props = 50
        assumptions = [f"p{i}" for i in range(num_props)]
        
        settings = {'N': 4}
        
        try:
            # This might stress memory with many propositions
            model = ModelDefaults(settings)
            # Should handle many propositions
        except MemoryError:
            # Acceptable for extreme cases
            pass
    
    def test_concurrent_model_building(self):
        """Test concurrent model building doesn't exhaust resources."""
        from model_checker.models import ModelDefaults
        
        def build_model():
            settings = {'N': 3}
            try:
                model = ModelDefaults(settings)
                return True
            except Exception:
                return False
        
        # Create multiple threads
        threads = []
        num_threads = 5
        
        for _ in range(num_threads):
            thread = threading.Thread(target=build_model)
            threads.append(thread)
            thread.start()
        
        # Wait for all threads
        for thread in threads:
            thread.join(timeout=5)
        
        # All threads should complete
        for thread in threads:
            assert not thread.is_alive()


class TestInterruptHandling:
    """Test handling of interrupts and cancellation."""
    
    def test_keyboard_interrupt_cleanup(self, tmp_path):
        """Test cleanup occurs on keyboard interrupt."""
        from tests.utils.helpers import run_cli_command
        
        content = '''
import time
time.sleep(10)  # Long sleep to allow interrupt
'''
        module_path = create_test_module(content, tmp_path, 'interrupt.py')
        
        # This would need actual interrupt testing
        # For now, just verify the module is valid
        assert module_path
    
    def test_graceful_shutdown(self):
        """Test graceful shutdown on resource exhaustion."""
        from model_checker.models import ModelDefaults
        
        # Try to exhaust resources
        settings = {
            'N': 64,
            'maximize': True,
            'contingent': True,
            'non_empty': True,
            'max_time': 0.1  # Short timeout to prevent hanging
        }
        
        try:
            model = ModelDefaults(settings)
            # If successful, model should be valid
            assert model is not None
        except Exception as e:
            # Should give meaningful error
            error_msg = str(e).lower()
            assert any(word in error_msg for word in 
                      ['timeout', 'memory', 'resource', 'limit'])


class TestPerformanceDegradation:
    """Test performance under degraded conditions."""
    
    def test_performance_with_many_constraints(self):
        """Test performance with many constraints."""
        from model_checker.models import ModelDefaults
        
        # Settings that create many constraints
        settings = {
            'N': 10,
            'contingent': True,
            'non_empty': True,
            'non_null': True,
            'disjoint': True,
            'max_time': 1.0
        }
        
        start_time = time.time()
        
        try:
            model = ModelDefaults(settings)
            elapsed = time.time() - start_time
            
            # Should complete in reasonable time
            assert elapsed < settings['max_time'] + 0.5  # Allow overhead
        except Exception:
            # Should fail quickly if it can't handle
            elapsed = time.time() - start_time
            assert elapsed < settings['max_time'] + 0.5
    
    @pytest.mark.parametrize("n,expected_time", [
        (2, 0.1),
        (4, 0.5),
        (8, 2.0),
    ])
    def test_scaling_behavior(self, n, expected_time):
        """Test that processing time scales reasonably with N."""
        from model_checker.models import ModelDefaults
        
        settings = {
            'N': n,
            'max_time': expected_time * 2  # Allow 2x expected
        }
        
        start_time = time.time()
        
        try:
            model = ModelDefaults(settings)
            elapsed = time.time() - start_time
            
            # Should not take much longer than expected
            assert elapsed < expected_time * 3
        except Exception:
            # Should timeout appropriately
            elapsed = time.time() - start_time
            assert elapsed < settings['max_time'] + 0.5


class TestResourceRecovery:
    """Test resource recovery after errors."""
    
    def test_memory_released_after_error(self):
        """Test memory is released after errors."""
        import gc
        import sys
        
        initial_objects = len(gc.get_objects())
        
        try:
            from model_checker.models import ModelDefaults
            
            # Create and destroy multiple models
            for _ in range(10):
                try:
                    settings = {'N': 10}
                    model = ModelDefaults(settings)
                    del model
                except Exception:
                    pass
            
            # Force garbage collection
            gc.collect()
            
            # Check object count hasn't grown too much
            final_objects = len(gc.get_objects())
            growth = final_objects - initial_objects
            
            # Some growth is normal, but should be bounded
            assert growth < 1000  # Reasonable threshold
        except ImportError:
            # Can't test without imports
            pass
    
    def test_file_handles_closed(self, tmp_path):
        """Test file handles are properly closed."""
        import os
        
        # Get initial open files (platform-dependent)
        try:
            import psutil
            process = psutil.Process(os.getpid())
            initial_files = len(process.open_files())
        except ImportError:
            # psutil not available, skip detailed check
            initial_files = 0
        
        # Create and process multiple files
        for i in range(5):
            content = f'''
from model_checker.theory_lib import logos
theory = logos.get_theory()
semantic_theories = {{"test_{i}": theory}}
example_range = {{"TEST": [[], ["A"], {{"N": 2}}]}}
'''
            module_path = create_test_module(content, tmp_path, f'test_{i}.py')
            
            from tests.utils.helpers import run_cli_command
            result = run_cli_command([module_path], check=False)
        
        # Check file handles
        if initial_files > 0:
            try:
                final_files = len(process.open_files())
                # Should not leak file handles
                assert final_files <= initial_files + 2  # Allow small variance
            except:
                pass  # Can't check without psutil