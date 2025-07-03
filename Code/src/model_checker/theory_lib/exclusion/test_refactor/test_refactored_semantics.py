#!/usr/bin/env python3
"""
Test infrastructure for the refactored exclusion semantics.
This file provides utilities to test and validate the refactoring at each phase.
"""

import json
import time
import sys
from pathlib import Path
from typing import Dict, List, Tuple, Optional

# Add parent directories to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent.parent))

from model_checker.syntactic import Syntax
from model_checker.theory_lib.exclusion import (
    ExclusionSemantics,
    UnilateralProposition,
    ExclusionStructure,
    exclusion_operators
)
from model_checker.theory_lib.exclusion.examples import example_range

class ExclusionTestRunner:
    """Test runner for exclusion theory examples."""
    
    def __init__(self):
        self.results = {}
        self.baseline = self._load_baseline()
        
    def _load_baseline(self) -> Dict:
        """Load baseline results for comparison."""
        baseline_path = Path(__file__).parent.parent / "test" / "baseline_results.json"
        if baseline_path.exists():
            with open(baseline_path, 'r') as f:
                data = json.load(f)
                return data.get('examples', {})
        return {}
        
    def run_example(self, name: str, example_data: List) -> Dict:
        """Run a single example and return detailed results."""
        start_time = time.time()
        
        try:
            # Unpack example data
            premises = example_data[0]
            conclusions = example_data[1] 
            settings = example_data[2]
            
            # Create combined settings
            combined_settings = {**ExclusionSemantics.DEFAULT_EXAMPLE_SETTINGS, **settings}
            combined_settings['print_impossible'] = False
            combined_settings['print_constraints'] = False
            combined_settings['print_z3'] = False
            combined_settings['save_output'] = False
            
            # Create semantics
            semantics = ExclusionSemantics(combined_settings)
            
            # Create syntax and parse
            syntax = Syntax(premises, conclusions, exclusion_operators)
            
            # Create model constraints
            from model_checker.model import ModelConstraints
            constraints = ModelConstraints(semantics, syntax, combined_settings, UnilateralProposition)
            
            # Create structure
            structure = ExclusionStructure(constraints, combined_settings)
            
            # Check if model was found
            has_model = structure.z3_model_status
            
            # Initialize result
            result = {
                'name': name,
                'has_model': has_model,
                'false_premises': [],
                'true_conclusions': [],
                'execution_time': time.time() - start_time,
                'error': None
            }
            
            if has_model:
                # Check premise truth values
                for premise in syntax.premises:
                    prop = UnilateralProposition(premise, structure)
                    if not prop.evaluate():
                        result['false_premises'].append(str(premise))
                        
                # Check conclusion truth values
                for conclusion in syntax.conclusions:
                    prop = UnilateralProposition(conclusion, structure)
                    if prop.evaluate():
                        result['true_conclusions'].append(str(conclusion))
                        
            return result
            
        except Exception as e:
            return {
                'name': name,
                'has_model': False,
                'false_premises': [],
                'true_conclusions': [],
                'execution_time': time.time() - start_time,
                'error': str(e)
            }
            
    def run_all_examples(self) -> Dict:
        """Run all examples and collect results."""
        print(f"Running {len(example_range)} examples...")
        
        for name, example_data in example_range.items():
            print(f"  Testing {name}...", end='', flush=True)
            result = self.run_example(name, example_data)
            self.results[name] = result
            
            # Print status
            if result['error']:
                print(f" ERROR: {result['error']}")
            elif result['false_premises'] or result['true_conclusions']:
                print(f" ISSUE: {len(result['false_premises'])} false premises, {len(result['true_conclusions'])} true conclusions")
            elif result['has_model']:
                print(" OK (model found)")
            else:
                print(" OK (no model)")
                
        return self.results
        
    def compare_with_baseline(self) -> Dict:
        """Compare current results with baseline."""
        comparison = {
            'improved': [],
            'regressed': [],
            'unchanged': [],
            'new_issues': []
        }
        
        for name, result in self.results.items():
            baseline_result = self.baseline.get(name, {})
            
            # Check if issues were fixed
            baseline_false = baseline_result.get('false_premises', [])
            current_false = result['false_premises']
            
            if baseline_false and not current_false:
                comparison['improved'].append(name)
            elif not baseline_false and current_false:
                comparison['regressed'].append(name)
            elif baseline_false and current_false:
                if len(current_false) < len(baseline_false):
                    comparison['improved'].append(name)
                elif len(current_false) > len(baseline_false):
                    comparison['regressed'].append(name)
                else:
                    comparison['unchanged'].append(name)
            else:
                comparison['unchanged'].append(name)
                
        return comparison
        
    def generate_report(self, output_file: str = "test_results.json"):
        """Generate a comprehensive test report."""
        # Count issues
        false_premise_count = sum(1 for r in self.results.values() if r['false_premises'])
        true_conclusion_count = sum(1 for r in self.results.values() if r['true_conclusions'])
        error_count = sum(1 for r in self.results.values() if r['error'])
        
        # Compare with baseline
        comparison = self.compare_with_baseline()
        
        # Create report
        report = {
            'timestamp': time.strftime('%Y-%m-%d %H:%M:%S'),
            'summary': {
                'total_examples': len(self.results),
                'false_premise_count': false_premise_count,
                'true_conclusion_count': true_conclusion_count,
                'error_count': error_count,
                'improved_from_baseline': len(comparison['improved']),
                'regressed_from_baseline': len(comparison['regressed'])
            },
            'comparison': comparison,
            'detailed_results': self.results
        }
        
        # Save report
        output_path = Path(__file__).parent / output_file
        with open(output_path, 'w') as f:
            json.dump(report, f, indent=2)
            
        # Print summary
        print("\n" + "="*60)
        print("TEST SUMMARY")
        print("="*60)
        print(f"Total examples: {report['summary']['total_examples']}")
        print(f"False premises: {report['summary']['false_premise_count']}")
        print(f"True conclusions: {report['summary']['true_conclusion_count']}")
        print(f"Errors: {report['summary']['error_count']}")
        print(f"\nComparison with baseline:")
        print(f"  Improved: {len(comparison['improved'])}")
        print(f"  Regressed: {len(comparison['regressed'])}")
        print(f"  Unchanged: {len(comparison['unchanged'])}")
        print(f"\nReport saved to: {output_path}")
        
        return report

def main():
    """Main entry point for testing."""
    runner = ExclusionTestRunner()
    runner.run_all_examples()
    runner.generate_report()

if __name__ == "__main__":
    main()