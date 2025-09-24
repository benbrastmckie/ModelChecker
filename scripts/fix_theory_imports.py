#!/usr/bin/env python3
"""
Import cleanup script following CODE_STANDARDS.md organization.

Converts star imports to explicit imports with proper organization:
1. Standard library
2. Third-party
3. Local framework
4. Relative imports
"""
import re
import ast
from pathlib import Path
from typing import Set, List, Tuple, Dict


def analyze_imports(content: str) -> Dict[str, List[str]]:
    """Analyze imports in content and categorize them."""
    lines = content.split('\n')

    stdlib_imports = []
    third_party_imports = []
    local_imports = []
    relative_imports = []

    # Standard library modules (common ones)
    stdlib_modules = {
        'os', 'sys', 'typing', 'abc', 'enum', 'collections', 'itertools',
        'functools', 'operator', 'math', 'random', 'json', 'pickle',
        'datetime', 'time', 'pathlib', 're', 'string', 'io'
    }

    # Third-party modules we know about
    third_party_modules = {'z3', 'pytest', 'numpy', 'sympy'}

    for line in lines:
        line = line.strip()
        if not line or line.startswith('#'):
            continue

        if line.startswith('from .') or line.startswith('from ..'):
            relative_imports.append(line)
        elif 'model_checker' in line:
            local_imports.append(line)
        elif any(f'import {module}' in line or f'from {module}' in line
                for module in third_party_modules):
            third_party_imports.append(line)
        elif any(f'import {module}' in line or f'from {module}' in line
                for module in stdlib_modules):
            stdlib_imports.append(line)
        elif line.startswith(('import ', 'from ')):
            # Default to stdlib for unknown imports
            stdlib_imports.append(line)

    return {
        'stdlib': stdlib_imports,
        'third_party': third_party_imports,
        'local': local_imports,
        'relative': relative_imports
    }


def reorganize_imports(content: str) -> str:
    """Reorganize imports per CODE_STANDARDS.md order."""
    lines = content.split('\n')

    # Find module docstring end
    in_docstring = False
    docstring_end = 0
    quote_count = 0

    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith('"""') or stripped.startswith("'''"):
            quote_count += stripped.count('"""') + stripped.count("'''")
            in_docstring = quote_count % 2 == 1
            if not in_docstring and quote_count > 0:
                docstring_end = i + 1
                break
        elif not stripped and not in_docstring:
            continue
        elif not in_docstring and not stripped.startswith('#'):
            docstring_end = i
            break

    # Split content into docstring, imports, and rest
    docstring_lines = lines[:docstring_end]
    remaining_lines = lines[docstring_end:]

    # Extract import lines and other lines
    import_lines = []
    other_lines = []
    in_import_block = False

    for line in remaining_lines:
        stripped = line.strip()
        if stripped.startswith(('import ', 'from ')) and not stripped.startswith('#'):
            import_lines.append(line)
            in_import_block = True
        elif in_import_block and stripped == '':
            # Skip blank lines in import block
            continue
        elif in_import_block and not stripped.startswith(('import ', 'from ')):
            # End of import block
            in_import_block = False
            other_lines.append(line)
        else:
            other_lines.append(line)

    # Remove duplicates while preserving order
    seen_imports = set()
    unique_imports = []
    for imp in import_lines:
        if imp not in seen_imports:
            seen_imports.add(imp)
            unique_imports.append(imp)

    # Categorize imports
    import_text = '\n'.join(unique_imports)
    categorized = analyze_imports(import_text)

    # Remove duplicates from each category
    for category in categorized:
        categorized[category] = list(dict.fromkeys(categorized[category]))

    # Rebuild with proper organization and blank lines
    organized = docstring_lines[:]

    # Add blank line after docstring if needed
    if docstring_lines and not docstring_lines[-1].strip() == '':
        organized.append('')

    # Add imports in order with blank lines between categories
    if categorized['stdlib']:
        organized.extend(sorted(categorized['stdlib']))
        organized.append('')

    if categorized['third_party']:
        organized.extend(sorted(categorized['third_party']))
        organized.append('')

    if categorized['local']:
        organized.extend(sorted(categorized['local']))
        organized.append('')

    if categorized['relative']:
        organized.extend(sorted(categorized['relative']))
        organized.append('')

    # Add rest of content
    organized.extend(other_lines)

    return '\n'.join(organized)


def fix_star_imports(filepath: Path) -> int:
    """
    Fix star imports following import organization standards.

    Returns number of fixes made.
    """
    try:
        content = filepath.read_text(encoding='utf-8')
    except UnicodeDecodeError:
        print(f"Warning: Could not decode {filepath}, skipping")
        return 0

    original = content

    # Pattern for star imports (violates standards)
    star_pattern = r'^from ([\w\.]+) import \*$'

    # ALWAYS use relative imports for local modules (per standards)
    replacements = {
        'model_checker.syntactic': [
            'parse_formula', 'validate_syntax', 'SyntaxError'
        ],
        'model_checker.utils': [
            'create_variable', 'format_output', 'clean_formula'
        ],
        '..defaults': [  # Relative import (correct per standards)
            'DEFAULT_SETTINGS', 'DEFAULT_TIMEOUT', 'MAX_STATES'
        ]
    }

    fixes = 0
    for match in re.finditer(star_pattern, content, re.MULTILINE):
        module = match.group(1)
        if module in replacements:
            imports = ', '.join(replacements[module])
            new_line = f'from {module} import {imports}'
            content = content.replace(match.group(0), new_line)
            fixes += 1

    # Always reorganize imports to fix organization issues
    reorganized = reorganize_imports(content)
    if content != original or reorganized != content:
        filepath.write_text(reorganized, encoding='utf-8')
        return max(fixes, 1)  # At least 1 if we reorganized

    return 0


def validate_import_organization(filepath: Path) -> List[str]:
    """Validate that imports follow CODE_STANDARDS.md organization."""
    try:
        content = filepath.read_text(encoding='utf-8')
    except UnicodeDecodeError:
        return [f"Could not decode {filepath}"]

    issues = []
    lines = content.split('\n')

    # Find import section
    import_started = False
    last_category = None
    categories = ['stdlib', 'third_party', 'local', 'relative']

    for i, line in enumerate(lines, 1):
        stripped = line.strip()

        if stripped.startswith(('import ', 'from ')) and not stripped.startswith('#'):
            import_started = True

            # Determine category
            if stripped.startswith('from .') or stripped.startswith('from ..'):
                current_category = 'relative'
            elif 'model_checker' in stripped:
                current_category = 'local'
            elif any(lib in stripped for lib in ['z3', 'pytest', 'numpy']):
                current_category = 'third_party'
            else:
                current_category = 'stdlib'

            # Check order
            if last_category:
                last_idx = categories.index(last_category)
                current_idx = categories.index(current_category)
                if current_idx < last_idx:
                    issues.append(f"Line {i}: {current_category} import after {last_category}")

            last_category = current_category

        elif import_started and stripped.startswith(('class ', 'def ', 'if __name__')):
            break

    return issues


def main():
    """Run import cleanup on theory_lib files."""
    theory_path = Path('Code/src/model_checker/theory_lib')

    if not theory_path.exists():
        print(f"Error: {theory_path} not found")
        return

    total_fixes = 0
    total_issues = 0

    print("=== Import Cleanup and Validation ===")

    for py_file in theory_path.rglob('*.py'):
        if 'test' in str(py_file) or '__pycache__' in str(py_file):
            continue

        # Skip bimodal directory per plan
        if 'bimodal' in str(py_file):
            print(f"Skipping {py_file} (bimodal under development)")
            continue

        print(f"Processing {py_file}")

        # Check for issues first
        issues = validate_import_organization(py_file)
        if issues:
            print(f"  Issues found:")
            for issue in issues:
                print(f"    - {issue}")
            total_issues += len(issues)

        # Fix imports
        fixes = fix_star_imports(py_file)
        if fixes > 0:
            print(f"  Fixed/reorganized imports")
            total_fixes += fixes
        else:
            print(f"  No changes needed")

    print(f"\n=== Summary ===")
    print(f"Total files processed: {len(list(theory_path.rglob('*.py')))}")
    print(f"Import fixes/reorganizations: {total_fixes}")
    print(f"Import issues found: {total_issues}")
    print(f"Import cleanup complete per CODE_STANDARDS.md")


if __name__ == '__main__':
    main()