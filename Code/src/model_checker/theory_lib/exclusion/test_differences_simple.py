"""Simple test to check if strategies differ on specific examples."""

import time
from semantic import ExclusionSemantics
from syntactic import UnilateralProposition
from model import ExclusionStructure
from operators import create_operator_collection, STRATEGY_REGISTRY
from model_checker import ModelConstraints, Syntax
from model_checker.utils import run_test

# Test a specific complex example
def test_example_with_strategy(premises, conclusions, settings, strategy_name):
    """Test an example with a specific strategy."""
    operator_collection = create_operator_collection(strategy_name)
    
    start_time = time.time()
    result = run_test(
        [premises, conclusions, settings],
        ExclusionSemantics,
        UnilateralProposition,
        operator_collection,
        Syntax,
        ModelConstraints,
        ExclusionStructure
    )
    elapsed = time.time() - start_time
    
    return result, elapsed

# Complex test cases
test_cases = [
    {
        "name": "Triple Exclusion",
        "premises": [],
        "conclusions": ["\\exclude \\exclude \\exclude A"],
        "settings": {'N': 3, 'max_time': 10}
    },
    {
        "name": "Nested Complex",
        "premises": ["\\exclude (A \\uniwedge (B \\univee \\exclude C))"],
        "conclusions": ["(\\exclude A \\univee \\exclude (B \\univee \\exclude C))"],
        "settings": {'N': 4, 'max_time': 15}
    },
    {
        "name": "Five Variable",
        "premises": [],
        "conclusions": ["(\\exclude (A \\uniwedge (B \\univee (C \\uniwedge (D \\univee E)))))"],
        "settings": {'N': 6, 'max_time': 20}
    }
]

# Test each strategy
strategies = ["SK", "CD", "MS", "UF"]
print("Testing strategies on complex examples...")
print("=" * 60)

for test_case in test_cases:
    print(f"\nTest: {test_case['name']}")
    print("-" * 40)
    
    results = {}
    for strategy in strategies:
        result, elapsed = test_example_with_strategy(
            test_case["premises"],
            test_case["conclusions"],
            test_case["settings"],
            strategy
        )
        
        results[strategy] = (result, elapsed)
        print(f"{strategy}: {'Pass' if result else 'Fail'} ({elapsed:.3f}s)")
    
    # Check if results differ
    result_values = [r[0] for r in results.values()]
    if len(set(result_values)) > 1:
        print(">>> DIFFERENCE FOUND! <<<")

print("\nDone.")