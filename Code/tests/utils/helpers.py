"""Test helper utilities for ModelChecker tests.

This module provides common utility functions used across test modules
to reduce duplication and improve test maintainability.
"""

import subprocess
import sys
import os
from pathlib import Path
from typing import Optional, List, Dict, Any


def run_cli_command(args: List[str], capture_output: bool = True, 
                   check: bool = False, timeout: Optional[int] = None):
    """Run ModelChecker CLI command and return result.
    
    Args:
        args: List of command-line arguments
        capture_output: Whether to capture stdout/stderr
        check: Whether to raise exception on non-zero exit
        timeout: Command timeout in seconds
        
    Returns:
        subprocess.CompletedProcess: Result of command execution
    """
    # Find the Code directory (project root)
    current_dir = Path(__file__).parent
    while current_dir.name != 'Code' and current_dir.parent != current_dir:
        current_dir = current_dir.parent
    
    # Add src to Python path
    src_dir = current_dir / 'src'
    env = os.environ.copy()
    env['PYTHONPATH'] = str(src_dir) + os.pathsep + env.get('PYTHONPATH', '')
    
    cmd = [sys.executable, '-m', 'model_checker'] + args
    
    result = subprocess.run(
        cmd,
        capture_output=capture_output,
        text=True,
        check=check,
        timeout=timeout,
        cwd=current_dir,
        env=env
    )
    
    return result


def assert_theory_valid(theory_name: str) -> None:
    """Assert a theory can be loaded and used.
    
    Args:
        theory_name: Name of the theory to validate
        
    Raises:
        AssertionError: If theory is invalid or missing components
    """
    from model_checker.utils.api import get_theory
    
    theory = get_theory(theory_name)
    assert theory is not None, f"Theory '{theory_name}' could not be loaded"
    
    # Check required components
    required_components = ['semantics', 'model', 'proposition', 'operators']
    for component in required_components:
        assert component in theory, \
            f"Theory '{theory_name}' missing required component: {component}"
    
    # Validate semantics has required attributes
    semantics = theory['semantics']
    assert hasattr(semantics, 'DEFAULT_EXAMPLE_SETTINGS'), \
        f"Theory '{theory_name}' semantics missing DEFAULT_EXAMPLE_SETTINGS"
    assert hasattr(semantics, 'DEFAULT_GENERAL_SETTINGS'), \
        f"Theory '{theory_name}' semantics missing DEFAULT_GENERAL_SETTINGS"


def create_test_module(content: str, tmp_path: Path, 
                      filename: str = 'test_module.py') -> str:
    """Create a test module file with given content.
    
    Args:
        content: Python code content for the module
        tmp_path: Temporary directory path
        filename: Name of the module file
        
    Returns:
        str: Path to the created module file
    """
    module_file = tmp_path / filename
    module_file.write_text(content)
    return str(module_file)


def capture_model_output(example_data: List, theory_name: str = 'logos',
                        settings: Optional[Dict[str, Any]] = None) -> str:
    """Capture model checking output for testing.
    
    Args:
        example_data: [assumptions, conclusions, settings] for the example
        theory_name: Name of the theory to use
        settings: Optional settings override
        
    Returns:
        str: Captured output from model checking
    """
    from io import StringIO
    from contextlib import redirect_stdout
    
    # Import required components
    from model_checker.builder import BuildModule
    from model_checker.utils.api import get_theory
    
    # Get theory
    theory = get_theory(theory_name)
    
    # Prepare example
    assumptions, conclusions, example_settings = example_data
    if settings:
        example_settings.update(settings)
    
    # Capture output
    output_buffer = StringIO()
    with redirect_stdout(output_buffer):
        # Create and run example
        # Note: This is simplified - actual implementation would use BuildExample
        print(f"Theory: {theory_name}")
        print(f"Assumptions: {assumptions}")
        print(f"Conclusions: {conclusions}")
        print(f"Settings: {example_settings}")
    
    return output_buffer.getvalue()


def assert_cli_success(args: List[str], expected_output: Optional[str] = None) -> subprocess.CompletedProcess:
    """Assert CLI command succeeds with optional output validation.
    
    Args:
        args: Command-line arguments
        expected_output: Optional expected output substring
        
    Returns:
        subprocess.CompletedProcess: Command result
        
    Raises:
        AssertionError: If command fails or output doesn't match
    """
    result = run_cli_command(args)
    
    assert result.returncode == 0, \
        f"CLI command failed with code {result.returncode}: {result.stderr}"
    
    if expected_output:
        assert expected_output in result.stdout, \
            f"Expected output '{expected_output}' not found in stdout"
    
    return result


def assert_cli_failure(args: List[str], expected_error: Optional[str] = None) -> subprocess.CompletedProcess:
    """Assert CLI command fails with optional error validation.
    
    Args:
        args: Command-line arguments
        expected_error: Optional expected error substring
        
    Returns:
        subprocess.CompletedProcess: Command result
        
    Raises:
        AssertionError: If command succeeds or error doesn't match
    """
    result = run_cli_command(args)
    
    assert result.returncode != 0, \
        f"CLI command succeeded when failure was expected"
    
    if expected_error:
        error_output = result.stderr or result.stdout
        assert expected_error.lower() in error_output.lower(), \
            f"Expected error '{expected_error}' not found in output"
    
    return result


def validate_module_structure(module_path: str) -> Dict[str, bool]:
    """Validate a module has required ModelChecker structure.
    
    Args:
        module_path: Path to the module file
        
    Returns:
        dict: Validation results for each required component
    """
    import ast
    
    with open(module_path, 'r') as f:
        content = f.read()
    
    try:
        tree = ast.parse(content)
    except SyntaxError:
        return {'valid_syntax': False}
    
    # Check for required attributes
    module_dict = {}
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    module_dict[target.id] = True
    
    return {
        'valid_syntax': True,
        'has_semantic_theories': 'semantic_theories' in module_dict,
        'has_example_range': 'example_range' in module_dict,
        'has_general_settings': 'general_settings' in module_dict,
    }


def compare_outputs(output1: str, output2: str, 
                   ignore_whitespace: bool = True) -> bool:
    """Compare two outputs for equality with optional normalization.
    
    Args:
        output1: First output string
        output2: Second output string
        ignore_whitespace: Whether to normalize whitespace
        
    Returns:
        bool: True if outputs are equivalent
    """
    if ignore_whitespace:
        # Normalize whitespace
        output1 = ' '.join(output1.split())
        output2 = ' '.join(output2.split())
    
    return output1 == output2


def create_temp_project(tmp_path: Path, project_name: str = 'test_project',
                       theory_name: str = 'logos') -> Path:
    """Create a temporary ModelChecker project for testing.
    
    Args:
        tmp_path: Temporary directory path
        project_name: Name of the project
        theory_name: Theory to use for the project
        
    Returns:
        Path: Path to the created project directory
    """
    project_dir = tmp_path / project_name
    project_dir.mkdir()
    
    # Create basic project structure
    (project_dir / '__init__.py').write_text('')
    (project_dir / 'examples.py').write_text(f'''
from model_checker.theory_lib import {theory_name}

theory = {theory_name}.get_theory()
semantic_theories = {{"{project_name}": theory}}
example_range = {{"TEST": [[], ["A"], {{"N": 2}}]}}
''')
    
    return project_dir