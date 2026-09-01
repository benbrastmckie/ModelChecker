"""Test helper utilities for ModelChecker tests.

This module provides common utility functions used across test modules
to reduce duplication and improve test maintainability.
"""

import shutil
import subprocess
import sys
import os
from pathlib import Path
from typing import Optional, List, Dict, Any

from tests.utils.cli_mode import get_cli_test_mode


def run_cli_command(args: List[str], capture_output: bool = True,
                   check: bool = False, timeout: Optional[int] = 30,
                   cwd: Optional[Path] = None, input: Optional[str] = None):
    """Run ModelChecker CLI command and return result.

    Invocation is dispatched over `MODELCHECKER_CLI_TEST_MODE`
    (`tests.utils.cli_mode.get_cli_test_mode`), which defaults to `'source'`:

    - ``source`` (default): `python -m model_checker`, with `code/src` prepended to
      `PYTHONPATH` exactly as before this mode existed. The developer loop is unaffected --
      this branch is byte-for-byte the prior unconditional behavior.
    - ``installed``: the pip-installed `model-checker` console script, resolved via
      `shutil.which('model-checker')`, with `PYTHONPATH` popped rather than injected. This is
      deliberate: any test that only passes because the source tree is importable must fail in
      this mode, since that is exactly the vacuous-pass condition the mode exists to rule out.
      Raises `RuntimeError` immediately if the console script is not on `PATH`.
    - ``installed-module``: `python -m model_checker`, also with `PYTHONPATH` popped, so it can
      only succeed against a package actually installed into the running interpreter. This
      yields console-script vs. `python -m` parity across the whole CLI suite (previously
      checked only for `--version`/`--help` in `tests/packaging/`).

    Args:
        args: List of command-line arguments
        capture_output: Whether to capture stdout/stderr
        check: Whether to raise exception on non-zero exit
        timeout: Command timeout in seconds. Defaults to 30 so a hung
            subprocess (e.g. a flag that unexpectedly blocks on stdin)
            fails the test instead of hanging the suite; pass timeout=None
            explicitly to disable.
        cwd: Working directory for the subprocess. Defaults to the project
            root (directory containing pyproject.toml) when not given --
            callers that need file-relative behavior (e.g. --save writing
            into the current directory) should pass an explicit tmp_path.
        input: Optional text piped to the subprocess's stdin.

    Returns:
        subprocess.CompletedProcess: Result of command execution

    Raises:
        RuntimeError: mode is 'installed' and 'model-checker' is not on PATH.
        ValueError: MODELCHECKER_CLI_TEST_MODE is set to an unrecognized value.
    """
    mode = get_cli_test_mode()

    # Find the project root (directory containing pyproject.toml)
    current_dir = Path(__file__).parent
    while not (current_dir / 'pyproject.toml').exists() and current_dir.parent != current_dir:
        current_dir = current_dir.parent

    env = os.environ.copy()

    if mode == 'source':
        src_dir = current_dir / 'src'
        env['PYTHONPATH'] = str(src_dir) + os.pathsep + env.get('PYTHONPATH', '')
        cmd = [sys.executable, '-m', 'model_checker'] + args
    elif mode == 'installed':
        # No PYTHONPATH injection: any reliance on the source tree must fail here, by design.
        env.pop('PYTHONPATH', None)
        script = shutil.which('model-checker')
        if script is None:
            raise RuntimeError(
                "MODELCHECKER_CLI_TEST_MODE=installed but 'model-checker' is not on PATH"
            )
        cmd = [script] + args
    else:  # mode == 'installed-module', the only remaining value get_cli_test_mode() permits
        env.pop('PYTHONPATH', None)
        cmd = [sys.executable, '-m', 'model_checker'] + args

    result = subprocess.run(
        cmd,
        capture_output=capture_output,
        text=True,
        check=check,
        timeout=timeout,
        cwd=cwd if cwd is not None else current_dir,
        env=env,
        input=input,
    )

    return result


def assert_theory_valid(theory_name: str) -> None:
    """Assert a theory can be loaded and used.
    
    Args:
        theory_name: Name of the theory to validate
        
    Raises:
        AssertionError: If theory is invalid or missing components
    """
    from model_checker.api import get_theory
    
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


def capture_model_output(example_data: List, theory_name: str = 'bimodal',
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
    from model_checker.api import get_theory
    
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


def assert_cli_success(args: List[str], expected_output: Optional[str] = None,
                      **run_kwargs: Any) -> subprocess.CompletedProcess:
    """Assert CLI command succeeds with optional output validation.

    Args:
        args: Command-line arguments
        expected_output: Optional expected output substring
        **run_kwargs: Additional keyword arguments forwarded to run_cli_command
            (e.g. cwd, timeout, input) -- required so BaseCLITest.assert_cli_success
            in tests/utils/base.py, which already forwards **kwargs here, does not
            raise TypeError the first time a caller passes one.

    Returns:
        subprocess.CompletedProcess: Command result

    Raises:
        AssertionError: If command fails or output doesn't match
    """
    result = run_cli_command(args, **run_kwargs)

    assert result.returncode == 0, \
        f"CLI command failed with code {result.returncode}: {result.stderr}"

    if expected_output:
        assert expected_output in result.stdout, \
            f"Expected output '{expected_output}' not found in stdout"

    return result


def assert_cli_failure(args: List[str], expected_error: Optional[str] = None,
                      **run_kwargs: Any) -> subprocess.CompletedProcess:
    """Assert CLI command fails with optional error validation.

    Args:
        args: Command-line arguments
        expected_error: Optional expected error substring
        **run_kwargs: Additional keyword arguments forwarded to run_cli_command
            (e.g. cwd, timeout, input) -- same rationale as assert_cli_success.

    Returns:
        subprocess.CompletedProcess: Command result

    Raises:
        AssertionError: If command succeeds or error doesn't match
    """
    result = run_cli_command(args, **run_kwargs)

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


def create_test_model(settings: Optional[Dict[str, Any]] = None,
                     premises: Optional[List[str]] = None,
                     conclusions: Optional[List[str]] = None,
                     theory_name: str = 'logos'):
    """Create a test model with proper API usage.

    This helper function creates a ModelDefaults instance using the correct
    API: ModelDefaults(model_constraints, settings) where model_constraints
    is properly constructed from Syntax, Semantics, and proposition classes.

    Args:
        settings: Optional settings dictionary (merged with defaults)
        premises: Optional list of premise formulas (defaults to [])
        conclusions: Optional list of conclusion formulas (defaults to ['A'])
        theory_name: Name of the theory to use (defaults to 'logos')

    Returns:
        ModelDefaults instance
    """
    from model_checker.syntactic import Syntax
    from model_checker.models import ModelDefaults
    from model_checker.models.constraints import ModelConstraints
    from model_checker.api import get_theory

    # Get theory components. Defaults to logos rather than bimodal: this
    # helper's ~20 gating call sites (tests/integration/test_performance.py,
    # test_error_handling.py, test_timeout_resources.py) assert only generic
    # ModelDefaults/error/timing behavior, never bimodal-specific semantics,
    # so pinning them to the one theory under active construction (see
    # TESTING_GUIDE.md section 8.14) coupled their wall clock to that
    # theory's frame-axiom solve cost for no coverage benefit. A caller that
    # genuinely needs bimodal's semantics should pass theory_name='bimodal'
    # explicitly.
    theory = get_theory(theory_name)
    semantics_class = theory['semantics']
    proposition_class = theory['proposition']
    operators = theory['operators']

    # Start with theory default settings
    full_settings = dict(semantics_class.DEFAULT_EXAMPLE_SETTINGS)
    full_settings.update(semantics_class.DEFAULT_GENERAL_SETTINGS)

    # Override with user-provided settings
    if settings is not None:
        full_settings.update(settings)

    # Default values for formulas
    if premises is None:
        premises = []
    if conclusions is None:
        conclusions = ['A']  # Simple valid atomic sentence letter

    # Create Syntax
    syntax = Syntax(premises, conclusions, operators)

    # Create Semantics instance (matches builder/example.py's
    # self.semantics(self.settings) call -- semantics classes take only
    # settings, not syntax)
    semantics = semantics_class(full_settings)

    # Create ModelConstraints
    model_constraints = ModelConstraints(full_settings, syntax, semantics, proposition_class)

    # Create and return ModelDefaults
    return ModelDefaults(model_constraints, full_settings)


def create_temp_project(tmp_path: Path, project_name: str = 'test_project',
                       theory_name: str = 'bimodal') -> Path:
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
    # __init__.py must have content and export examples for tests to pass
    (project_dir / '__init__.py').write_text(f'''"""Package for {project_name}."""
from . import examples
''')
    (project_dir / 'examples.py').write_text(f'''"""Example definitions for {project_name}."""
from model_checker.theory_lib import {theory_name}

theory = {theory_name}.get_theory()
semantic_theories = {{"{project_name}": theory}}
example_range = {{"TEST": [[], ["A"], {{"N": 2}}]}}
''')

    return project_dir