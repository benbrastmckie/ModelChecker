"""
Systematic exploration of all exclusion theory examples.

This script runs all examples and captures results for analysis.
"""

import subprocess
import re
import sys
import os

# Path to examples file
examples_path = "/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/exclusion/attempt6_incremental/examples.py"
dev_cli_path = "/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/dev_cli.py"

def run_examples():
    """Run all examples and capture results."""
    try:
        # Run the examples with dev_cli
        result = subprocess.run(
            [dev_cli_path, examples_path, "-p"],
            capture_output=True,
            text=True,
            timeout=300  # 5 minute timeout
        )
        
        return result.stdout, result.stderr, result.returncode
    except subprocess.TimeoutExpired:
        return "", "TIMEOUT", -1
    except Exception as e:
        return "", str(e), -1

def parse_results(stdout_text):
    """Parse the results to extract example outcomes."""
    results = []
    current_example = None
    
    lines = stdout_text.split('\n')
    for line in lines:
        # Match example headers
        example_match = re.match(r'EXAMPLE (.+?): there is (.*?)\.', line)
        if example_match:
            name = example_match.group(1)
            outcome = example_match.group(2)
            current_example = {
                'name': name,
                'outcome': outcome,
                'countermodel': outcome == 'a countermodel',
                'valid': outcome == 'no countermodel',
                'runtime': None,
                'premises': [],
                'conclusions': []
            }
            
        # Match runtime
        time_match = re.match(r'Z3 Run Time: ([0-9.]+) seconds', line)
        if time_match and current_example:
            current_example['runtime'] = float(time_match.group(1))
            results.append(current_example)
            current_example = None
    
    return results

def categorize_results(results):
    """Categorize results by type and outcome."""
    categories = {
        'frame_examples': [],
        'negation_examples': [],
        'demorgan_examples': [],
        'distribution_examples': [],
        'absorption_examples': [],
        'associativity_examples': [],
        'identity_examples': [],
        'complex_examples': [],
        'other_examples': []
    }
    
    for result in results:
        name = result['name'].lower()
        
        if any(keyword in name for keyword in ['frame', 'atomic', 'empty', 'gap', 'glut']):
            categories['frame_examples'].append(result)
        elif any(keyword in name for keyword in ['negation', 'double', 'triple', 'quadruple']):
            categories['negation_examples'].append(result)
        elif 'demorgan' in name:
            categories['demorgan_examples'].append(result)
        elif 'distribution' in name:
            categories['distribution_examples'].append(result)
        elif 'absorption' in name:
            categories['absorption_examples'].append(result)
        elif 'associativity' in name:
            categories['associativity_examples'].append(result)
        elif 'identity' in name:
            categories['identity_examples'].append(result)
        elif any(keyword in name for keyword in ['t17', 'complex', 'th_17', 'th_18']):
            categories['complex_examples'].append(result)
        else:
            categories['other_examples'].append(result)
    
    return categories

def analyze_patterns(categories):
    """Analyze patterns in the results."""
    analysis = {}
    
    for category_name, examples in categories.items():
        if not examples:
            continue
            
        valid_count = sum(1 for ex in examples if ex['valid'])
        countermodel_count = sum(1 for ex in examples if ex['countermodel'])
        total_count = len(examples)
        avg_runtime = sum(ex['runtime'] for ex in examples if ex['runtime']) / total_count if total_count > 0 else 0
        
        analysis[category_name] = {
            'total': total_count,
            'valid': valid_count,
            'countermodel': countermodel_count,
            'valid_percentage': (valid_count / total_count * 100) if total_count > 0 else 0,
            'avg_runtime': avg_runtime,
            'examples': examples
        }
    
    return analysis

def print_analysis(analysis):
    """Print detailed analysis of results."""
    print("=" * 80)
    print("SYSTEMATIC EXCLUSION THEORY EXPLORATION RESULTS")
    print("=" * 80)
    
    # Summary statistics
    total_examples = sum(cat['total'] for cat in analysis.values())
    total_valid = sum(cat['valid'] for cat in analysis.values())
    total_countermodel = sum(cat['countermodel'] for cat in analysis.values())
    
    print(f"\nOVERALL SUMMARY:")
    print(f"Total Examples: {total_examples}")
    print(f"Valid (no countermodel): {total_valid} ({total_valid/total_examples*100:.1f}%)")
    print(f"Invalid (countermodel): {total_countermodel} ({total_countermodel/total_examples*100:.1f}%)")
    
    # Category breakdown
    print(f"\nCATEGORY BREAKDOWN:")
    print("-" * 80)
    
    for category_name, data in analysis.items():
        if data['total'] == 0:
            continue
            
        print(f"\n{category_name.replace('_', ' ').title()}:")
        print(f"  Total: {data['total']}")
        print(f"  Valid: {data['valid']} ({data['valid_percentage']:.1f}%)")
        print(f"  Countermodel: {data['countermodel']} ({100-data['valid_percentage']:.1f}%)")
        print(f"  Avg Runtime: {data['avg_runtime']:.4f}s")
        
        # List examples by outcome
        valid_examples = [ex['name'] for ex in data['examples'] if ex['valid']]
        countermodel_examples = [ex['name'] for ex in data['examples'] if ex['countermodel']]
        
        if valid_examples:
            print(f"  Valid Examples: {', '.join(valid_examples)}")
        if countermodel_examples:
            print(f"  Countermodel Examples: {', '.join(countermodel_examples)}")
    
    # Detailed results
    print(f"\nDETAILED RESULTS:")
    print("-" * 80)
    
    for category_name, data in analysis.items():
        if data['total'] == 0:
            continue
            
        print(f"\n{category_name.replace('_', ' ').title()}:")
        for example in data['examples']:
            status = "VALID" if example['valid'] else "COUNTERMODEL"
            print(f"  {example['name']}: {status} ({example['runtime']:.4f}s)")

def main():
    """Main exploration function."""
    print("Running systematic exploration of exclusion theory examples...")
    print("This may take a few minutes...")
    
    # Run examples
    stdout, stderr, returncode = run_examples()
    
    if returncode != 0:
        print(f"Error running examples:")
        print(f"Return code: {returncode}")
        print(f"Stderr: {stderr}")
        if stdout:
            print(f"Stdout: {stdout[:1000]}...")  # First 1000 chars
        return
    
    # Parse results
    results = parse_results(stdout)
    print(f"Parsed {len(results)} examples")
    
    # Categorize and analyze
    categories = categorize_results(results)
    analysis = analyze_patterns(categories)
    
    # Print analysis
    print_analysis(analysis)
    
    # Save detailed results to file
    output_file = "exclusion_exploration_results.txt"
    with open(output_file, 'w') as f:
        # Redirect stdout to file temporarily
        original_stdout = sys.stdout
        sys.stdout = f
        print_analysis(analysis)
        sys.stdout = original_stdout
    
    print(f"\nDetailed results saved to: {output_file}")

if __name__ == "__main__":
    main()