"""
Recursive Reduction Analyzer for Exclusion Semantics

This module provides tools to analyze how true_at methods reduce recursively
and identify where the reduction fails to reach proper verifier conditions.
"""

import z3
import json
from datetime import datetime
from typing import Dict, List, Any, Optional, Tuple
from dataclasses import dataclass, field
from model_checker import syntactic


@dataclass
class ReductionTrace:
    """Represents a single step in the recursive reduction."""
    depth: int
    operator: str
    sentence: str
    eval_point: Dict[str, Any]
    formula_type: str  # 'true_at', 'verifier_condition', 'constraint'
    z3_formula: Optional[str] = None
    subtraces: List['ReductionTrace'] = field(default_factory=list)
    notes: List[str] = field(default_factory=list)


class RecursiveReductionAnalyzer:
    """
    Analyzes how true_at calls reduce recursively to verifier conditions.
    Traces the reduction tree and identifies problematic patterns.
    """
    
    def __init__(self, semantics):
        self.semantics = semantics
        self.trace_stack = []
        self.current_trace = None
        self.issues_found = []
        self.original_true_at = {}
        self.original_extended_verify = {}
        
    def analyze_true_at(self, operator_class, test_cases):
        """
        Trace how true_at reduces for given operator on test cases.
        
        Args:
            operator_class: The operator class to analyze
            test_cases: List of (sentence, eval_point) tuples to test
            
        Returns:
            Dict with analysis results
        """
        results = {
            'operator': operator_class.__name__,
            'test_cases': len(test_cases),
            'traces': [],
            'issues': [],
            'patterns': {}
        }
        
        # Hook into the operator's true_at method
        self._install_hooks(operator_class)
        
        try:
            for sentence, eval_point in test_cases:
                trace = self._trace_reduction(sentence, eval_point)
                results['traces'].append(trace)
                
                # Analyze the trace for issues
                issues = self._analyze_trace(trace)
                results['issues'].extend(issues)
                
        finally:
            # Restore original methods
            self._remove_hooks(operator_class)
            
        # Identify patterns in the issues
        results['patterns'] = self._identify_patterns(results['issues'])
        
        return results
    
    def _install_hooks(self, operator_class):
        """Install tracing hooks into operator methods."""
        # Save original methods
        if hasattr(operator_class, 'true_at'):
            self.original_true_at[operator_class] = operator_class.true_at
            operator_class.true_at = self._create_traced_true_at(operator_class.true_at)
            
        if hasattr(operator_class, 'extended_verify'):
            self.original_extended_verify[operator_class] = operator_class.extended_verify
            operator_class.extended_verify = self._create_traced_extended_verify(
                operator_class.extended_verify
            )
    
    def _remove_hooks(self, operator_class):
        """Remove tracing hooks from operator methods."""
        if operator_class in self.original_true_at:
            operator_class.true_at = self.original_true_at[operator_class]
            
        if operator_class in self.original_extended_verify:
            operator_class.extended_verify = self.original_extended_verify[operator_class]
    
    def _create_traced_true_at(self, original_method):
        """Create a traced version of true_at method."""
        def traced_true_at(self_operator, *args, **kwargs):
            # Record entry
            depth = len(self.trace_stack)
            trace = ReductionTrace(
                depth=depth,
                operator=self_operator.__class__.__name__,
                sentence=str(args[0]) if args else "unknown",
                eval_point=args[1] if len(args) > 1 else kwargs.get('eval_point', {}),
                formula_type='true_at'
            )
            
            self.trace_stack.append(trace)
            
            try:
                # Call original method
                result = original_method(self_operator, *args, **kwargs)
                
                # Record the Z3 formula if it's returned
                if isinstance(result, z3.BoolRef):
                    trace.z3_formula = str(result)
                    
                    # Check if this properly reduces to verifier conditions
                    if not self._check_verifier_reduction(result, trace):
                        trace.notes.append("WARNING: Does not reduce to verifier existence")
                        
                return result
                
            finally:
                self.trace_stack.pop()
                if self.trace_stack:
                    self.trace_stack[-1].subtraces.append(trace)
                else:
                    self.current_trace = trace
                    
        return traced_true_at
    
    def _create_traced_extended_verify(self, original_method):
        """Create a traced version of extended_verify method."""
        def traced_extended_verify(self_operator, *args, **kwargs):
            depth = len(self.trace_stack)
            trace = ReductionTrace(
                depth=depth,
                operator=self_operator.__class__.__name__,
                sentence=str(args[1]) if len(args) > 1 else "unknown",
                eval_point=args[2] if len(args) > 2 else kwargs.get('eval_point', {}),
                formula_type='extended_verify'
            )
            
            self.trace_stack.append(trace)
            
            try:
                result = original_method(self_operator, *args, **kwargs)
                if isinstance(result, z3.BoolRef):
                    trace.z3_formula = str(result)
                return result
            finally:
                self.trace_stack.pop()
                if self.trace_stack:
                    self.trace_stack[-1].subtraces.append(trace)
                    
        return traced_extended_verify
    
    def _trace_reduction(self, sentence, eval_point):
        """Trace the complete reduction of a sentence at an evaluation point."""
        self.trace_stack = []
        self.current_trace = None
        
        # Trigger the reduction
        try:
            formula = self.semantics.true_at(sentence, eval_point)
        except Exception as e:
            error_trace = ReductionTrace(
                depth=0,
                operator="Error",
                sentence=str(sentence),
                eval_point=eval_point,
                formula_type="error"
            )
            error_trace.notes.append(f"Error during reduction: {str(e)}")
            return error_trace
            
        return self.current_trace
    
    def _check_verifier_reduction(self, formula, trace):
        """
        Check if a formula properly reduces to verifier existence conditions.
        
        A proper reduction should eventually reach formulas of the form:
        Exists([v], And(verify(v, atom), is_part_of(v, world)))
        """
        # This is a simplified check - in practice we'd do more sophisticated analysis
        formula_str = str(formula)
        
        # Check for patterns indicating proper verifier reduction
        has_exists = "Exists" in formula_str
        has_verify = "verify" in formula_str
        has_part_of = "is_part_of" in formula_str or "is-part-of" in formula_str
        
        # For atomic sentences, we expect all three
        if trace.sentence.count('(') == 0:  # Simple heuristic for atomic
            return has_exists and has_verify and has_part_of
            
        # For complex formulas, we need to check the recursive structure
        # This is where we'd analyze the subtraces
        return len(trace.subtraces) > 0
    
    def _analyze_trace(self, trace):
        """Analyze a trace for issues and patterns."""
        issues = []
        
        # Check for missing verifier conditions
        if trace.formula_type == 'true_at' and not trace.subtraces:
            if 'verify' not in str(trace.z3_formula):
                issues.append({
                    'type': 'missing_verifier_condition',
                    'operator': trace.operator,
                    'sentence': trace.sentence,
                    'depth': trace.depth,
                    'note': 'true_at does not reduce to verifier conditions'
                })
        
        # Check for approximations
        if trace.notes:
            for note in trace.notes:
                if 'WARNING' in note:
                    issues.append({
                        'type': 'improper_reduction',
                        'operator': trace.operator,
                        'sentence': trace.sentence,
                        'depth': trace.depth,
                        'note': note
                    })
        
        # Recursively analyze subtraces
        for subtrace in trace.subtraces:
            issues.extend(self._analyze_trace(subtrace))
            
        return issues
    
    def _identify_patterns(self, issues):
        """Identify patterns in the issues found."""
        patterns = {
            'by_operator': {},
            'by_issue_type': {},
            'by_depth': {}
        }
        
        for issue in issues:
            # By operator
            op = issue['operator']
            if op not in patterns['by_operator']:
                patterns['by_operator'][op] = []
            patterns['by_operator'][op].append(issue)
            
            # By issue type
            issue_type = issue['type']
            if issue_type not in patterns['by_issue_type']:
                patterns['by_issue_type'][issue_type] = []
            patterns['by_issue_type'][issue_type].append(issue)
            
            # By depth
            depth = issue['depth']
            if depth not in patterns['by_depth']:
                patterns['by_depth'][depth] = []
            patterns['by_depth'][depth].append(issue)
            
        return patterns
    
    def generate_report(self, results):
        """Generate a human-readable report from analysis results."""
        report = []
        report.append(f"Recursive Reduction Analysis Report")
        report.append(f"Generated: {datetime.now().isoformat()}")
        report.append(f"Operator: {results['operator']}")
        report.append(f"Test Cases: {results['test_cases']}")
        report.append("")
        
        # Summary of issues
        report.append("ISSUES FOUND:")
        if not results['issues']:
            report.append("  No issues found - all reductions appear correct")
        else:
            report.append(f"  Total issues: {len(results['issues'])}")
            
            # Issues by type
            for issue_type, issues in results['patterns']['by_issue_type'].items():
                report.append(f"  - {issue_type}: {len(issues)} occurrences")
                
        report.append("")
        
        # Detailed issues by operator
        report.append("ISSUES BY OPERATOR:")
        for op, issues in results['patterns']['by_operator'].items():
            report.append(f"  {op}:")
            for issue in issues[:3]:  # Show first 3
                report.append(f"    - {issue['type']} at depth {issue['depth']}")
                report.append(f"      Sentence: {issue['sentence']}")
                if 'note' in issue:
                    report.append(f"      Note: {issue['note']}")
                    
        report.append("")
        
        # Trace visualization (simplified)
        report.append("SAMPLE TRACE:")
        if results['traces']:
            self._format_trace(results['traces'][0], report, indent=0)
            
        return "\n".join(report)
    
    def _format_trace(self, trace, report, indent=0):
        """Format a trace for the report."""
        prefix = "  " * indent
        report.append(f"{prefix}{trace.operator}.{trace.formula_type}({trace.sentence})")
        
        if trace.notes:
            for note in trace.notes:
                report.append(f"{prefix}  ! {note}")
                
        for subtrace in trace.subtraces:
            self._format_trace(subtrace, report, indent + 1)
    
    def save_results(self, results, filename):
        """Save analysis results to a JSON file."""
        # Convert traces to serializable format
        def serialize_trace(trace):
            return {
                'depth': trace.depth,
                'operator': trace.operator,
                'sentence': trace.sentence,
                'eval_point': str(trace.eval_point),
                'formula_type': trace.formula_type,
                'z3_formula': trace.z3_formula,
                'notes': trace.notes,
                'subtraces': [serialize_trace(st) for st in trace.subtraces]
            }
        
        serializable_results = {
            'operator': results['operator'],
            'test_cases': results['test_cases'],
            'traces': [serialize_trace(t) for t in results['traces']],
            'issues': results['issues'],
            'patterns': results['patterns'],
            'timestamp': datetime.now().isoformat()
        }
        
        with open(filename, 'w') as f:
            json.dump(serializable_results, f, indent=2)