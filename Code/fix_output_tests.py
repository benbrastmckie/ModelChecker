#!/usr/bin/env python3
"""Fix OutputManager instantiations in test files to use OutputConfig."""

import os
import re
from pathlib import Path

def fix_file(filepath):
    """Fix OutputManager instantiations in a single file."""
    with open(filepath, 'r') as f:
        content = f.read()
    
    original = content
    
    # Check if OutputConfig is imported
    if 'OutputManager' in content and 'OutputConfig' not in content:
        # Add OutputConfig to imports
        if 'from model_checker.output import OutputManager' in content:
            content = content.replace(
                'from model_checker.output import OutputManager',
                'from model_checker.output import OutputManager, OutputConfig'
            )
        elif 'from model_checker.output.manager import OutputManager' in content:
            content = content.replace(
                'from model_checker.output.manager import OutputManager',
                'from model_checker.output.manager import OutputManager\nfrom model_checker.output.config import OutputConfig'
            )
    
    # Fix basic patterns
    patterns = [
        # Pattern 1: save_output=True/False only
        (r'OutputManager\(save_output=(True|False)\)',
         r'''OutputConfig(formats=['markdown', 'json'], save_output=\1)
        output_manager = OutputManager(config=config)'''),
        
        # Pattern 2: save_output and mode
        (r'OutputManager\(save_output=(True|False), mode=[\'"](\w+)[\'"]\)',
         r'''OutputConfig(formats=['markdown', 'json'], mode='\2', save_output=\1)
        output_manager = OutputManager(config=config)'''),
        
        # Pattern 3: with sequential_files
        (r'OutputManager\(\s*save_output=(True|False),\s*mode=[\'"](\w+)[\'"],\s*sequential_files=[\'"](\w+)[\'"]\s*\)',
         r'''OutputConfig(
            formats=['markdown', 'json'],
            mode='\2',
            sequential_files='\3',
            save_output=\1
        )
        output_manager = OutputManager(config=config)'''),
    ]
    
    # Apply patterns
    for pattern, replacement in patterns:
        # First find all matches
        matches = list(re.finditer(pattern, content))
        
        # Process from end to beginning to preserve indices
        for match in reversed(matches):
            # Get the line containing the match
            start = content.rfind('\n', 0, match.start()) + 1
            end = match.end()
            
            # Get indentation
            line_start = content[start:match.start()]
            indent = ''
            for char in line_start:
                if char in ' \t':
                    indent += char
                else:
                    break
            
            # Build replacement with proper indentation
            config_lines = replacement.split('\n')
            indented_replacement = f"{indent}config = " + config_lines[0]
            for line in config_lines[1:]:
                if line.strip():
                    indented_replacement += f"\n{indent}{line}"
            
            # Replace just the OutputManager instantiation
            assignment_match = re.search(r'(\w+)\s*=\s*' + pattern, content[start:end])
            if assignment_match:
                var_name = assignment_match.group(1)
                # Use the original variable name
                indented_replacement = indented_replacement.replace('output_manager', var_name)
            
            content = content[:match.start()] + f"OutputConfig(save_output={match.group(1)})\n{indent}{content[start:match.start()]}OutputManager(config=config)" + content[match.end():]
    
    if content != original:
        with open(filepath, 'w') as f:
            f.write(content)
        print(f"Fixed: {filepath}")
        return True
    return False

def main():
    """Fix all test files."""
    test_dir = Path('src/model_checker/output/tests')
    
    fixed_count = 0
    for test_file in test_dir.rglob('*.py'):
        if test_file.name != '__init__.py' and test_file.name != 'conftest.py':
            if fix_file(test_file):
                fixed_count += 1
    
    print(f"\nFixed {fixed_count} files")

if __name__ == '__main__':
    main()