#!/usr/bin/env python3
"""Minimal relevance theory test case for debugging iterator issues.

This example should find exactly 2 models:
- MODEL 1: A and B both true (validates premise and conclusion)
- MODEL 2: A true, B false (validates conclusion but not premise)
"""

from model_checker.builder import BuildModule
from model_checker.iterate.debug import DebugModelIterator, ConstraintComparator

# Minimal relevance example
MINIMAL_EXAMPLE = """
# Settings
N = 2
iterate = 2

# Syntax  
A prop
B prop

# Semantics
rule: classical

# Logic
{A and B} premise
A conclusion

# This should find:
# MODEL 1: A=true, B=true (satisfies premise and conclusion)
# MODEL 2: A=true, B=false (satisfies conclusion but not premise)
"""


def test_with_debug_iterator():
    """Run test with debug iterator to capture constraint flow."""
    print("=== TESTING WITH DEBUG ITERATOR ===\n")
    
    # Build the module
    module = BuildModule({"raw_text": MINIMAL_EXAMPLE})
    examples = module.valid_examples()
    
    if not examples:
        print("ERROR: No valid examples found!")
        return None
    
    example = examples[0]
    print(f"Testing example: {example}")
    
    # Replace the iterator with debug version
    original_iterator_class = None
    theory_module = example.model_structure.__class__.__module__
    
    # Get the theory's iterate module
    if "relevance" in theory_module:
        from model_checker.theory_lib.logos.subtheories.relevance import iterate as relevance_iterate
        original_iterator_class = relevance_iterate.RelevanceModelIterator
        
        # Create debug wrapper
        class DebugRelevanceIterator(DebugModelIterator):
            """Debug wrapper for relevance iterator."""
            
            def _calculate_differences(self, new_structure, previous_structure):
                """Use relevance-specific difference calculation."""
                # Call the original relevance implementation
                return original_iterator_class._calculate_differences(self, new_structure, previous_structure)
            
            def _create_difference_constraint(self, previous_models):
                """Use relevance-specific constraint generation."""
                return original_iterator_class._create_difference_constraint(self, previous_models)
            
            def _create_non_isomorphic_constraint(self, z3_model):
                """Use relevance-specific isomorphism constraint."""
                return original_iterator_class._create_non_isomorphic_constraint(self, z3_model)
        
        # Replace iterator for this test
        relevance_iterate.RelevanceModelIterator = DebugRelevanceIterator
    
    try:
        # Run with debugging
        result = module.print_all()
        
        # Get the debug iterator from the example
        if hasattr(example, '_iterator'):
            return example._iterator
        else:
            print("WARNING: No iterator found on example")
            return None
            
    finally:
        # Restore original iterator
        if original_iterator_class:
            relevance_iterate.RelevanceModelIterator = original_iterator_class


def test_monolithic_vs_modular():
    """Compare monolithic vs modular implementations."""
    print("\n=== COMPARING MONOLITHIC VS MODULAR ===\n")
    
    comparator = ConstraintComparator()
    
    # First, run with current monolithic implementation
    print("1. Running with monolithic core.py...")
    monolithic_iterator = test_with_debug_iterator()
    if monolithic_iterator:
        comparator.capture_run("monolithic", monolithic_iterator)
        print(f"   Found {len(monolithic_iterator.found_models)} models")
    
    # TODO: After implementing modular version, run it here
    # print("\n2. Running with modular implementation...")
    # modular_iterator = test_with_modular_implementation()
    # if modular_iterator:
    #     comparator.capture_run("modular", modular_iterator)
    #     print(f"   Found {len(modular_iterator.found_models)} models")
    #
    # # Compare the runs
    # print("\n3. Comparing runs...")
    # comparator.print_comparison("monolithic", "modular")
    
    return comparator


def check_basic_functionality():
    """Basic check that the example works without debugging."""
    print("=== BASIC FUNCTIONALITY CHECK ===\n")
    
    module = BuildModule({"raw_text": MINIMAL_EXAMPLE})
    examples = module.valid_examples()
    
    if not examples:
        print("ERROR: No valid examples found!")
        return False
    
    # Check settings
    example = examples[0]
    iterate_setting = example.settings.get('iterate', 1)
    print(f"Iterate setting: {iterate_setting}")
    
    # Get model count by parsing output
    import io
    output = io.StringIO()
    module.print_all(output=output)
    output_text = output.getvalue()
    
    # Count MODEL occurrences
    model_count = output_text.count("MODEL ")
    print(f"Models found: {model_count}")
    
    # Check for MODEL 2
    has_model_2 = "MODEL 2" in output_text
    print(f"Has MODEL 2: {has_model_2}")
    
    if model_count >= 2 and has_model_2:
        print("\n✓ Basic functionality PASSED")
        return True
    else:
        print("\n✗ Basic functionality FAILED")
        print("\nOutput preview:")
        print(output_text[:500] + "..." if len(output_text) > 500 else output_text)
        return False


if __name__ == "__main__":
    # First check basic functionality
    if check_basic_functionality():
        print("\n" + "="*60 + "\n")
        # Then run with debugging
        test_with_debug_iterator()
    else:
        print("\nSkipping debug test due to basic functionality failure")