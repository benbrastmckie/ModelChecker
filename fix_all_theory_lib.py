#!/usr/bin/env python3
"""Fix circular imports in all theory_lib subtheories."""

import os
from pathlib import Path

base_path = Path("/Users/nicky/Documents/ModelChecker/Code/src/model_checker/theory_lib/logos/subtheories")
subtheories = ['extensional', 'modal', 'constitutive', 'relevance']  # counterfactual already fixed

for subtheory in subtheories:
    init_file = base_path / subtheory / "__init__.py"

    if not init_file.exists():
        print(f"Skipping {subtheory}: __init__.py not found")
        continue

    print(f"Fixing {subtheory}...")

    with open(init_file, 'r') as f:
        content = f.read()

    # Check if it needs fixing
    if "from .examples import" not in content or "lazy" in content.lower():
        print(f"  Already fixed or doesn't need fixing")
        continue

    # Different patterns for different subtheories
    if subtheory == 'extensional':
        old_import = "from .examples import countermodel_examples, theorem_examples, unit_tests"
        example_vars = "countermodel_examples, theorem_examples, unit_tests"
        return_dict = """    return {
        'countermodels': countermodel_examples,
        'theorems': theorem_examples,
        'all': unit_tests
    }"""
    elif subtheory == 'modal':
        old_import = "from .examples import modal_cm_examples, modal_th_examples, modal_def_examples, unit_tests"
        example_vars = "modal_cm_examples, modal_th_examples, modal_def_examples, unit_tests"
        return_dict = """    return {
        'countermodels': modal_cm_examples,
        'theorems': modal_th_examples,
        'definitions': modal_def_examples,
        'all': unit_tests
    }"""
    elif subtheory == 'constitutive':
        old_import = "from .examples import constitutive_cm_examples, constitutive_th_examples, unit_tests"
        example_vars = "constitutive_cm_examples, constitutive_th_examples, unit_tests"
        return_dict = """    return {
        'countermodels': constitutive_cm_examples,
        'theorems': constitutive_th_examples,
        'all': unit_tests
    }"""
    elif subtheory == 'relevance':
        old_import = "from .examples import relevance_cm_examples, relevance_th_examples, unit_tests"
        example_vars = "relevance_cm_examples, relevance_th_examples, unit_tests"
        return_dict = """    return {
        'countermodels': relevance_cm_examples,
        'theorems': relevance_th_examples,
        'all': unit_tests
    }"""

    # Remove the import line
    content = content.replace(old_import + "\n", "")

    # Update the get_examples function
    old_func_start = 'def get_examples():\n    """\n    Get all '

    # Find and replace the function
    if old_func_start in content:
        # Find the end of the docstring
        func_start = content.index(old_func_start)
        docstring_end = content.index('"""', func_start + len(old_func_start)) + 3

        # Find the return statement
        return_start = content.index("return {", docstring_end)
        func_end = content.index("}", return_start) + 1

        # Build new function
        new_func = f'''def get_examples():
    """
    Get all {subtheory} examples (lazy loaded to avoid circular imports).

    Returns:
        dict: Dictionary containing all {subtheory} examples
    """
    # Lazy import to avoid circular dependency
    from .examples import {example_vars}
{return_dict}'''

        # Replace the function
        content = content[:func_start] + new_func + content[func_end:]

    # Write back
    with open(init_file, 'w') as f:
        f.write(content)

    print(f"  ✓ Fixed")

print("\nAll theory_lib subtheories fixed!")