#!/usr/bin/env python3
"""
Check type hint coverage across theory_lib modules.
"""

import os
import re
from pathlib import Path

def analyze_file_type_coverage(filepath):
    """Analyze type coverage for a Python file."""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
    except UnicodeDecodeError:
        return 0, 0, f"Could not decode {filepath}"

    # Find all function definitions
    function_pattern = r'^[ \t]*def\s+(\w+)\s*\([^)]*\)'
    functions = re.findall(function_pattern, content, re.MULTILINE)

    # Find functions with type hints (either parameter or return types)
    type_hint_pattern = r'^[ \t]*def\s+\w+\s*\([^)]*\)\s*(?:->\s*[^:]+)?:'
    typed_functions = re.findall(type_hint_pattern, content, re.MULTILINE)

    total_functions = len(functions)
    typed_count = len(typed_functions)

    return total_functions, typed_count, None

def main():
    """Check type coverage across theory_lib."""
    theory_lib_path = Path('Code/src/model_checker/theory_lib')

    if not theory_lib_path.exists():
        print(f"Error: {theory_lib_path} not found")
        return

    total_functions = 0
    total_typed = 0
    file_results = []

    print("=== Type Hint Coverage Analysis ===")
    print()

    # Check all Python files except tests and bimodal
    for py_file in theory_lib_path.rglob('*.py'):
        if ('test' in str(py_file) or
            '__pycache__' in str(py_file) or
            'bimodal' in str(py_file)):  # Skip bimodal per plan
            continue

        func_count, typed_count, error = analyze_file_type_coverage(py_file)

        if error:
            print(f"Error analyzing {py_file}: {error}")
            continue

        if func_count == 0:
            continue  # Skip files with no functions

        total_functions += func_count
        total_typed += typed_count

        coverage = (typed_count / func_count * 100) if func_count > 0 else 0

        relative_path = py_file.relative_to(theory_lib_path)
        file_results.append((relative_path, func_count, typed_count, coverage))

    # Sort by coverage (lowest first to highlight issues)
    file_results.sort(key=lambda x: x[3])

    print("Files needing type hints (sorted by coverage):")
    print("-" * 60)

    for relative_path, func_count, typed_count, coverage in file_results:
        if coverage < 95:  # Highlight files with < 95% coverage
            status = "❌" if coverage < 50 else "⚠️ "
            print(f"{status} {relative_path}: {typed_count}/{func_count} ({coverage:.1f}%)")
        elif coverage < 100:
            print(f"✓  {relative_path}: {typed_count}/{func_count} ({coverage:.1f}%)")

    print()
    print("High coverage files (95%+ type hints):")
    print("-" * 40)

    high_coverage_files = [x for x in file_results if x[3] >= 95]
    for relative_path, func_count, typed_count, coverage in high_coverage_files:
        print(f"✅ {relative_path}: {typed_count}/{func_count} ({coverage:.1f}%)")

    print()
    print("=== Summary ===")
    overall_coverage = (total_typed / total_functions * 100) if total_functions > 0 else 0
    print(f"Total functions: {total_functions}")
    print(f"Functions with type hints: {total_typed}")
    print(f"Overall coverage: {overall_coverage:.1f}%")

    if overall_coverage >= 90:
        print("🎉 Excellent type coverage!")
    elif overall_coverage >= 75:
        print("✅ Good type coverage")
    else:
        print("⚠️  Type coverage needs improvement")

if __name__ == '__main__':
    main()