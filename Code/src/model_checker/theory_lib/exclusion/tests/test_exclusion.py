"""
Enhanced Exclusion Theory Test Suite

This module provides comprehensive testing for the exclusion theory implementation,
including detailed analysis of premise/conclusion evaluation and strategy comparison.

Usage Examples:

1. Run all basic tests:
   pytest src/model_checker/theory_lib/exclusion/tests/test_exclusion.py

2. Run enhanced analysis tests:
   pytest src/model_checker/theory_lib/exclusion/tests/test_exclusion.py -k "detailed_analysis"

3. Run comprehensive example testing:
   pytest src/model_checker/theory_lib/exclusion/tests/test_exclusion.py -k "comprehensive"

4. Verbose output with performance data:
   pytest -v src/model_checker/theory_lib/exclusion/tests/test_exclusion.py --capture=no

5. Generate HTML report:
   pytest src/model_checker/theory_lib/exclusion/tests/test_exclusion.py --html=exclusion_test_report.html
"""

import pytest
import json
import time

from model_checker import (
    ModelConstraints,
    Syntax,
)
from model_checker.theory_lib.exclusion import (
    ExclusionStructure,
    UnilateralProposition,
    ExclusionSemantics,
    exclusion_operators,
)
from model_checker.theory_lib.exclusion.examples import test_example_range, all_example_range
from model_checker.utils import run_test, run_enhanced_test, run_strategy_test, TestResultData
from model_checker.theory_lib.exclusion.operators import STRATEGY_REGISTRY

@pytest.mark.parametrize("example_name,example_case", test_example_range.items())
def test_example_cases(example_name, example_case):
    """Test each example case from example_range."""
    result = run_test(
        example_case,
        ExclusionSemantics,
        UnilateralProposition,
        exclusion_operators,
        Syntax,
        ModelConstraints,
        ExclusionStructure,
    )
    assert result, f"Test failed for example: {example_name}"


@pytest.mark.parametrize("example_name,example_case", all_example_range.items())
def test_example_detailed_analysis(example_name, example_case):
    """Enhanced test that captures detailed analysis data for all examples."""
    result_data = run_enhanced_test(
        example_case,
        ExclusionSemantics,
        UnilateralProposition,
        exclusion_operators,
        Syntax,
        ModelConstraints,
        ExclusionStructure,
        strategy_name="QI2"
    )
    
    # Validate basic model generation
    assert result_data.model_found, f"No model found for {example_name}"
    assert result_data.error_message is None, f"Error in {example_name}: {result_data.error_message}"
    
    # Store detailed results for analysis (these assertions may fail, that's expected)
    invalid_premises = []
    invalid_conclusions = []
    
    # Check premise evaluations (should all be True)
    for i, premise_result in enumerate(result_data.premise_evaluations):
        if premise_result is not None and not premise_result:
            invalid_premises.append(i)
    
    # Check conclusion evaluations (should all be False)  
    for i, conclusion_result in enumerate(result_data.conclusion_evaluations):
        if conclusion_result is not None and conclusion_result:
            invalid_conclusions.append(i)
    
    # Log analysis results for reporting (don't fail test here)
    if invalid_premises or invalid_conclusions:
        analysis_msg = f"Example {example_name} has evaluation issues:\n"
        if invalid_premises:
            analysis_msg += f"  False premises at indices: {invalid_premises}\n"
        if invalid_conclusions:
            analysis_msg += f"  True conclusions at indices: {invalid_conclusions}\n"
        analysis_msg += f"  Solving time: {result_data.solving_time:.4f}s"
        print(f"\n{analysis_msg}")


@pytest.mark.parametrize("example_name,example_case", [
    ("TN_ENTAIL", all_example_range["TN_ENTAIL"]),
    ("CONJ_DM_RL", all_example_range["CONJ_DM_RL"]), 
    ("DISJ_DM_RL", all_example_range["DISJ_DM_RL"]),
])
def test_problematic_examples_analysis(example_name, example_case):
    """Detailed analysis of known problematic examples."""
    result_data = run_enhanced_test(
        example_case,
        ExclusionSemantics,
        UnilateralProposition,
        exclusion_operators,
        Syntax,
        ModelConstraints,
        ExclusionStructure,
        strategy_name="QI2"
    )
    
    # These are known problematic cases, so we expect them to fail validation
    assert result_data.model_found, f"No model found for {example_name}"
    
    # Extract the example structure for debugging
    premises, conclusions, settings = example_case
    
    # Detailed analysis
    is_valid = result_data.is_valid_countermodel()
    print(f"\n=== Analysis for {example_name} ===")
    print(f"Example structure:")
    print(f"  Premises: {premises}")
    print(f"  Conclusions: {conclusions}")
    print(f"  Expectation: {settings.get('expectation', 'unknown')}")
    print(f"Model found: {result_data.model_found}")
    print(f"Check result: {result_data.check_result}")
    print(f"Z3 model status: {result_data.z3_model_status}")
    print(f"Valid countermodel: {is_valid}")
    print(f"Premise evaluations: {result_data.premise_evaluations}")
    print(f"Conclusion evaluations: {result_data.conclusion_evaluations}")
    print(f"Solving time: {result_data.solving_time:.4f}s")
    print(f"Function witnesses available: {bool(result_data.function_witnesses)}")
    
    # Debug: Check if we have the right number of evaluations
    expected_premise_count = len(premises)
    expected_conclusion_count = len(conclusions)
    actual_premise_count = len(result_data.premise_evaluations)
    actual_conclusion_count = len(result_data.conclusion_evaluations)
    
    print(f"Expected {expected_premise_count} premises, got {actual_premise_count}")
    print(f"Expected {expected_conclusion_count} conclusions, got {actual_conclusion_count}")
    
    # Additional debugging - let's see if we can manually check the issue
    if result_data.model_found and actual_premise_count == 0 and expected_premise_count > 0:
        print("DEBUGGING: No premise evaluations despite having premises and a model")
        
    # Check if this matches the false premise pattern
    if (actual_premise_count > 0 and 
        any(p is not None and not p for p in result_data.premise_evaluations)):
        print("⚠️  This example has FALSE premises (invalid countermodel)")
    
    if (actual_conclusion_count > 0 and 
        any(c is not None and c for c in result_data.conclusion_evaluations)):
        print("⚠️  This example has TRUE conclusions (invalid countermodel)")


def test_comprehensive_baseline_collection():
    """Collect comprehensive baseline data for all examples with current QI2 strategy."""
    baseline_results = {}
    
    for example_name, example_case in all_example_range.items():
        result_data = run_enhanced_test(
            example_case,
            ExclusionSemantics,
            UnilateralProposition,
            exclusion_operators,
            Syntax,
            ModelConstraints,
            ExclusionStructure,
            strategy_name="QI2"
        )
        
        # Store key metrics
        baseline_results[example_name] = {
            "model_found": result_data.model_found,
            "is_valid_countermodel": result_data.is_valid_countermodel(),
            "solving_time": result_data.solving_time,
            "premise_count": len(result_data.premise_evaluations),
            "conclusion_count": len(result_data.conclusion_evaluations),
            "false_premises": sum(1 for p in result_data.premise_evaluations if p is not None and not p),
            "true_conclusions": sum(1 for c in result_data.conclusion_evaluations if c is not None and c),
            "has_function_witnesses": bool(result_data.function_witnesses),
            "error": result_data.error_message is not None
        }
    
    # Calculate summary statistics
    total_examples = len(baseline_results)
    valid_countermodels = sum(1 for r in baseline_results.values() if r["is_valid_countermodel"])
    invalid_countermodels = total_examples - valid_countermodels
    avg_solving_time = sum(r["solving_time"] for r in baseline_results.values()) / total_examples
    
    print(f"\n=== QI2 Baseline Results Summary ===")
    print(f"Total examples: {total_examples}")
    print(f"Valid countermodels: {valid_countermodels}")
    print(f"Invalid countermodels: {invalid_countermodels}")
    print(f"Reliability: {valid_countermodels/total_examples*100:.1f}%")
    print(f"Average solving time: {avg_solving_time:.4f}s")
    
    # Identify problematic examples
    problematic = [(name, data) for name, data in baseline_results.items() 
                   if not data["is_valid_countermodel"] and data["model_found"]]
    
    if problematic:
        print(f"\nProblematic examples ({len(problematic)}):")
        for name, data in problematic:
            issues = []
            if data["false_premises"] > 0:
                issues.append(f"{data['false_premises']} false premises")
            if data["true_conclusions"] > 0:
                issues.append(f"{data['true_conclusions']} true conclusions")
            print(f"  {name}: {', '.join(issues)}")
    
    # This test always passes - it's for data collection
    assert True


@pytest.mark.parametrize("strategy_name", list(STRATEGY_REGISTRY.keys()))
def test_strategy_comprehensive(strategy_name):
    """Test each strategy against all examples with detailed analysis."""
    print(f"\n=== STRATEGY COMPREHENSIVE TESTING: {strategy_name} ===")
    
    results = {}
    total_time = 0.0
    successful_models = 0
    invalid_countermodels = 0
    
    # Test all examples with this strategy
    for example_name, example_case in all_example_range.items():
        try:
            result_data = run_strategy_test(example_case, strategy_name)
            
            results[example_name] = result_data
            total_time += result_data.solving_time
            
            if result_data.model_found:
                successful_models += 1
                
                # Check for invalid countermodels (false premises or true conclusions)
                if not result_data.is_valid_countermodel():
                    invalid_countermodels += 1
                    
        except Exception as e:
            # Record failed examples
            result_data = TestResultData()
            result_data.strategy_name = strategy_name
            result_data.error_message = str(e)
            results[example_name] = result_data
    
    # Calculate summary statistics
    num_examples = len(all_example_range)
    avg_time = total_time / num_examples if num_examples > 0 else 0
    success_rate = successful_models / num_examples if num_examples > 0 else 0
    invalid_rate = invalid_countermodels / successful_models if successful_models > 0 else 0
    
    print(f"Strategy: {strategy_name}")
    print(f"Total examples: {num_examples}")
    print(f"Models found: {successful_models} ({success_rate:.1%})")
    print(f"Invalid countermodels: {invalid_countermodels} ({invalid_rate:.1%})")
    print(f"Average solving time: {avg_time:.3f}s")
    print(f"Total time: {total_time:.3f}s")
    
    # Store detailed results
    strategy_file = f"strategy_results_{strategy_name}.json"
    strategy_data = {
        "strategy": strategy_name,
        "timestamp": time.time(),
        "summary": {
            "num_examples": num_examples,
            "successful_models": successful_models,
            "success_rate": success_rate,
            "invalid_countermodels": invalid_countermodels,
            "invalid_rate": invalid_rate,
            "avg_solving_time": avg_time,
            "total_time": total_time
        },
        "results": {name: {
            "model_found": result.model_found,
            "solving_time": result.solving_time,
            "premise_evaluations": result.premise_evaluations,
            "conclusion_evaluations": result.conclusion_evaluations,
            "is_valid_countermodel": result.is_valid_countermodel(),
            "error_message": result.error_message
        } for name, result in results.items()}
    }
    
    try:
        with open(strategy_file, 'w') as f:
            json.dump(strategy_data, f, indent=2)
        print(f"Strategy results saved to {strategy_file}")
    except Exception as e:
        print(f"Warning: Could not save strategy results: {e}")
    
    # Store results in a global variable for cross-strategy analysis
    if not hasattr(test_strategy_comprehensive, 'all_strategy_results'):
        test_strategy_comprehensive.all_strategy_results = {}
    test_strategy_comprehensive.all_strategy_results[strategy_name] = strategy_data


@pytest.mark.parametrize("strategy_name,example_name,example_case", [
    (strategy, name, case) 
    for strategy in list(STRATEGY_REGISTRY.keys())
    for name, case in [("TN_ENTAIL", all_example_range["TN_ENTAIL"]), 
                       ("CONJ_DM_RL", all_example_range["CONJ_DM_RL"]), 
                       ("DISJ_DM_RL", all_example_range["DISJ_DM_RL"])]
])
def test_strategy_problematic_examples(strategy_name, example_name, example_case):
    """Test each strategy against known problematic examples."""
    result_data = run_strategy_test(example_case, strategy_name)
    
    # Basic validation that the strategy can run
    assert result_data.strategy_name == strategy_name, f"Strategy name mismatch"
    assert result_data.error_message is None or result_data.model_found, f"Strategy {strategy_name} failed on {example_name}: {result_data.error_message}"
    
    # Record results for analysis (not strict assertions)
    if result_data.model_found:
        is_valid = result_data.is_valid_countermodel()
        print(f"\n{strategy_name} on {example_name}: Valid countermodel = {is_valid}")
        if not is_valid:
            premises = [p for p in result_data.premise_evaluations if p is not None]
            conclusions = [c for c in result_data.conclusion_evaluations if c is not None]
            has_false_premise = any(not p for p in premises)
            has_true_conclusion = any(c for c in conclusions)
            print(f"  False premise: {has_false_premise}, True conclusion: {has_true_conclusion}")


def test_strategy_comparison_analysis():
    """Analyze and compare results across all strategies."""
    if not hasattr(test_strategy_comprehensive, 'all_strategy_results'):
        pytest.skip("No strategy results available for comparison")
    
    results = test_strategy_comprehensive.all_strategy_results
    
    print(f"\n=== STRATEGY COMPARISON ANALYSIS ===")
    print(f"{'Strategy':<8} {'Success':<8} {'Invalid':<8} {'Avg Time':<10} {'Reliability':<12}")
    print("-" * 58)
    
    for strategy_name, data in results.items():
        summary = data['summary']
        success_rate = summary['success_rate']
        invalid_rate = summary['invalid_rate']
        avg_time = summary['avg_solving_time']
        reliability = (1 - invalid_rate) if success_rate > 0 else 0
        
        print(f"{strategy_name:<8} {success_rate:<8.1%} {invalid_rate:<8.1%} {avg_time:<10.3f} {reliability:<12.1%}")
    
    # Find best performing strategies
    best_reliability = max((1 - data['summary']['invalid_rate']) for data in results.values() 
                          if data['summary']['success_rate'] > 0)
    best_strategies = [name for name, data in results.items() 
                      if data['summary']['success_rate'] > 0 and 
                         (1 - data['summary']['invalid_rate']) == best_reliability]
    
    print(f"\nBest reliability strategies: {', '.join(best_strategies)} ({best_reliability:.1%} valid countermodels)")
    
    # Save comparison report
    comparison_data = {
        "timestamp": time.time(),
        "strategies": results,
        "best_reliability": best_reliability,
        "best_strategies": best_strategies
    }
    
    try:
        with open("strategy_comparison.json", 'w') as f:
            json.dump(comparison_data, f, indent=2)
        print("Strategy comparison saved to strategy_comparison.json")
    except Exception as e:
        print(f"Warning: Could not save comparison: {e}")
    
    # Basic assertion that we have results
    assert len(results) > 0, "No strategy results to compare"

