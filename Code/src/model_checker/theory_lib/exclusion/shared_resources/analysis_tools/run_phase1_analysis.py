"""
Phase 1 Analysis Script

This script runs the complete Phase 1 analysis:
1. Analyzes recursive reduction failures
2. Establishes baseline metrics
3. Generates comprehensive reports
"""

import json
import os
import sys
from datetime import datetime

# Add parent directory to path
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from model_checker.theory_lib.exclusion.test.test_recursive_semantics import BaselineTestRunner


def main():
    """Run Phase 1 analysis and generate reports."""
    
    print("="*60)
    print("PHASE 1: FOUNDATION AND ANALYSIS")
    print("="*60)
    print(f"Started: {datetime.now().isoformat()}\n")
    
    # Step 1: Run baseline tests on all examples
    print("Step 1: Running baseline tests on all examples...")
    baseline_runner = BaselineTestRunner()
    baseline_summary = baseline_runner.run_all_examples()
    
    # Step 2: Analyze results
    print("\n" + "="*60)
    print("Step 2: Analyzing baseline results...")
    
    analysis = {
        'phase': 1,
        'timestamp': datetime.now().isoformat(),
        'baseline_summary': baseline_summary,
        'issues_found': {
            'false_premises': baseline_summary['false_premise_count'],
            'true_conclusions': baseline_summary['true_conclusion_count'],
            'total_invalid': baseline_summary['false_premise_count'] + baseline_summary['true_conclusion_count'],
            'error_count': baseline_summary['error_count']
        },
        'performance': {
            'average_time': baseline_summary['average_time'],
            'total_examples': baseline_summary['total_examples'],
            'success_rate': baseline_summary['success_count'] / baseline_summary['total_examples'] if baseline_summary['total_examples'] > 0 else 0
        }
    }
    
    # Step 3: Generate analysis report
    print("\nStep 3: Generating analysis report...")
    
    report = []
    report.append("# Phase 1 Analysis Report: Foundation and Analysis")
    report.append(f"\nGenerated: {analysis['timestamp']}")
    report.append("\n## Executive Summary")
    report.append(f"\nTotal examples tested: {analysis['baseline_summary']['total_examples']}")
    report.append(f"Examples with issues: {analysis['issues_found']['total_invalid']}")
    report.append(f"- False premises: {analysis['issues_found']['false_premises']}")
    report.append(f"- True conclusions: {analysis['issues_found']['true_conclusions']}")
    report.append(f"- Errors: {analysis['issues_found']['error_count']}")
    report.append(f"\nSuccess rate: {analysis['performance']['success_rate']:.1%}")
    report.append(f"Average time per example: {analysis['performance']['average_time']:.3f}s")
    
    report.append("\n## Critical Issues Discovered")
    
    if analysis['issues_found']['false_premises'] > 0:
        report.append("\n### False Premises")
        report.append("The following examples produced models with false premises:")
        for fp in baseline_summary['detailed_results']['false_premises']:
            report.append(f"- **{fp['example']}**: {fp['count']} false premises")
            if 'details' in fp and fp['details']:
                for detail in fp['details'][:2]:  # Show first 2
                    report.append(f"  - {detail.get('sentence', 'Unknown')}")
    
    if analysis['issues_found']['true_conclusions'] > 0:
        report.append("\n### True Conclusions")
        report.append("The following examples produced models with true conclusions:")
        for tc in baseline_summary['detailed_results']['true_conclusions']:
            report.append(f"- **{tc['example']}**: {tc['count']} true conclusions")
            if 'details' in tc and tc['details']:
                for detail in tc['details'][:2]:  # Show first 2
                    report.append(f"  - {detail.get('sentence', 'Unknown')}")
    
    if analysis['issues_found']['error_count'] > 0:
        report.append("\n### Errors")
        report.append(f"Total errors encountered: {analysis['issues_found']['error_count']}")
        # Group errors by type
        error_types = {}
        for error in baseline_summary['detailed_results']['errors']:
            error_msg = error.get('error', 'Unknown error')
            error_type = error_msg.split(':')[0] if ':' in error_msg else 'Unknown'
            if error_type not in error_types:
                error_types[error_type] = []
            error_types[error_type].append(error['example'])
        
        for error_type, examples in error_types.items():
            report.append(f"- {error_type}: {len(examples)} examples")
    
    report.append("\n## Recommendations for Phase 2")
    report.append("\nBased on the Phase 1 findings:")
    
    if analysis['issues_found']['total_invalid'] > 0:
        report.append("1. **Priority**: Fix the recursive reduction issues causing false premises and true conclusions")
        report.append("2. **Focus**: Implement proper verifier existence conditions in operator true_at methods")
        report.append("3. **Strategy**: Start with SK (Skolemized Functions) implementation as planned")
    
    if analysis['issues_found']['error_count'] > 0:
        report.append("4. **Infrastructure**: Address initialization errors in test framework")
    
    report.append("\n## Next Steps")
    report.append("\n1. Review this analysis report")
    report.append("2. Update implementation_plan.md based on findings")
    report.append("3. Begin Phase 2: SK Implementation")
    report.append("4. Focus on eliminating false premises and true conclusions")
    
    # Save report
    report_text = "\n".join(report)
    with open('analysis_report.md', 'w') as f:
        f.write(report_text)
    
    # Save detailed JSON results
    with open('phase1_analysis.json', 'w') as f:
        json.dump(analysis, f, indent=2)
    
    print("\n" + "="*60)
    print("Phase 1 Analysis Complete!")
    print(f"- Analysis report: analysis_report.md")
    print(f"- Detailed results: phase1_analysis.json")
    print(f"- Baseline results: baseline_example_results.json")
    print("="*60)
    
    return analysis


if __name__ == "__main__":
    main()