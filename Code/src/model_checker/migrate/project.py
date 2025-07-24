"""
Project-level migration utilities.

This module provides tools for migrating entire projects and codebases
from the old ModelChecker API to the new modernized API.
"""

import os
import subprocess
import shutil
from pathlib import Path
from typing import List, Dict, Any, Tuple, Optional, Set
from dataclasses import dataclass
from concurrent.futures import ThreadPoolExecutor, as_completed

from .transformer import transform_file, batch_transform_files
from .notebook import migrate_notebook, find_notebooks_in_directory
from .config import validate_settings_compatibility


@dataclass
class MigrationResult:
    """Results of a project migration."""
    success: bool
    files_processed: int
    files_migrated: int
    files_failed: int
    warnings: List[str]
    errors: List[str]
    backup_directory: Optional[Path] = None


def migrate_project(project_path: Path, 
                   backup: bool = True,
                   include_tests: bool = True,
                   parallel: bool = True,
                   max_workers: Optional[int] = None) -> MigrationResult:
    """
    Migrate an entire project to the new ModelChecker API.
    
    This function handles Python files, Jupyter notebooks, configuration files,
    and other relevant project assets.
    
    Args:
        project_path: Path to the project directory
        backup: Whether to create a backup of the entire project
        include_tests: Whether to migrate test files
        parallel: Whether to use parallel processing
        max_workers: Maximum number of worker threads (None for default)
        
    Returns:
        MigrationResult with detailed information about the migration
    """
    if not project_path.exists():
        return MigrationResult(
            success=False,
            files_processed=0,
            files_migrated=0,
            files_failed=0,
            warnings=[],
            errors=[f"Project path does not exist: {project_path}"]
        )
    
    if not project_path.is_dir():
        return MigrationResult(
            success=False,
            files_processed=0,
            files_migrated=0,
            files_failed=0,
            warnings=[],
            errors=[f"Project path is not a directory: {project_path}"]
        )
    
    result = MigrationResult(
        success=True,
        files_processed=0,
        files_migrated=0,
        files_failed=0,
        warnings=[],
        errors=[]
    )
    
    try:
        # Create backup if requested
        if backup:
            backup_dir = _create_project_backup(project_path)
            result.backup_directory = backup_dir
            result.warnings.append(f"Backup created: {backup_dir}")
        
        # Find files to migrate
        files_to_migrate = _find_migration_candidates(project_path, include_tests)
        result.files_processed = len(files_to_migrate)
        
        if not files_to_migrate:
            result.warnings.append("No files found that need migration")
            return result
        
        # Migrate files
        if parallel and len(files_to_migrate) > 1:
            migration_results = _migrate_files_parallel(files_to_migrate, max_workers)
        else:
            migration_results = _migrate_files_sequential(files_to_migrate)
        
        # Process results
        for file_path, (file_success, file_warnings) in migration_results.items():
            if file_success:
                result.files_migrated += 1
            else:
                result.files_failed += 1
                result.errors.append(f"Failed to migrate {file_path}")
            
            result.warnings.extend(file_warnings)
        
        # Migrate project configuration
        config_warnings = _migrate_project_config(project_path)
        result.warnings.extend(config_warnings)
        
        # Update project dependencies
        deps_warnings = _update_project_dependencies(project_path)
        result.warnings.extend(deps_warnings)
        
        # Generate migration report
        report_path = project_path / "MIGRATION_REPORT.md"
        _generate_migration_report(result, migration_results, report_path)
        result.warnings.append(f"Migration report saved: {report_path}")
        
        # Validate the migration
        validation_warnings = _validate_project_migration(project_path)
        result.warnings.extend(validation_warnings)
        
        # Determine overall success
        result.success = result.files_failed == 0
        
    except Exception as e:
        result.success = False
        result.errors.append(f"Unexpected error during migration: {e}")
    
    return result


def _create_project_backup(project_path: Path) -> Path:
    """Create a backup of the entire project."""
    backup_name = f"{project_path.name}_backup"
    backup_path = project_path.parent / backup_name
    
    # Handle existing backups
    counter = 1
    while backup_path.exists():
        backup_path = project_path.parent / f"{backup_name}_{counter}"
        counter += 1
    
    shutil.copytree(project_path, backup_path, ignore=shutil.ignore_patterns(
        '*.pyc', '__pycache__', '.git', '.pytest_cache', '.coverage'
    ))
    
    return backup_path


def _find_migration_candidates(project_path: Path, include_tests: bool) -> List[Path]:
    """Find all files that might need migration."""
    candidates = []
    
    # Python files
    python_files = list(project_path.rglob("*.py"))
    
    # Filter out certain directories/files if not including tests
    if not include_tests:
        python_files = [
            f for f in python_files 
            if not any(part.startswith('test') for part in f.parts)
            and not f.name.startswith('test_')
        ]
    
    # Filter out common non-relevant files
    python_files = [
        f for f in python_files
        if not any(exclude in str(f) for exclude in [
            '__pycache__', '.git', '.pytest_cache', 'build/', 'dist/',
            '.venv', 'venv/', '.env'
        ])
    ]
    
    candidates.extend(python_files)
    
    # Jupyter notebooks
    notebooks = find_notebooks_in_directory(project_path, recursive=True)
    candidates.extend(notebooks)
    
    return candidates


def _migrate_files_sequential(files: List[Path]) -> Dict[Path, Tuple[bool, List[str]]]:
    """Migrate files sequentially."""
    results = {}
    
    for file_path in files:
        if file_path.suffix == '.py':
            success, warnings = transform_file(file_path, backup=False)  # Project-level backup already created
        elif file_path.suffix == '.ipynb':
            success, warnings = migrate_notebook(file_path, backup=False)
        else:
            success, warnings = False, [f"Unknown file type: {file_path.suffix}"]
        
        results[file_path] = (success, warnings)
    
    return results


def _migrate_files_parallel(files: List[Path], max_workers: Optional[int]) -> Dict[Path, Tuple[bool, List[str]]]:
    """Migrate files in parallel."""
    results = {}
    
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        # Submit all files for migration
        future_to_file = {}
        
        for file_path in files:
            if file_path.suffix == '.py':
                future = executor.submit(transform_file, file_path, False)
            elif file_path.suffix == '.ipynb':
                future = executor.submit(migrate_notebook, file_path, False)
            else:
                future = executor.submit(lambda p: (False, [f"Unknown file type: {p.suffix}"]), file_path)
            
            future_to_file[future] = file_path
        
        # Collect results
        for future in as_completed(future_to_file):
            file_path = future_to_file[future]
            try:
                success, warnings = future.result()
                results[file_path] = (success, warnings)
            except Exception as e:
                results[file_path] = (False, [f"Exception during migration: {e}"])
    
    return results


def _migrate_project_config(project_path: Path) -> List[str]:
    """Migrate project configuration files."""
    warnings = []
    
    # Check for setup.py
    setup_py = project_path / "setup.py"
    if setup_py.exists():
        warnings.extend(_migrate_setup_py(setup_py))
    
    # Check for pyproject.toml
    pyproject_toml = project_path / "pyproject.toml"
    if pyproject_toml.exists():
        warnings.extend(_migrate_pyproject_toml(pyproject_toml))
    
    # Check for requirements.txt
    requirements_txt = project_path / "requirements.txt"
    if requirements_txt.exists():
        warnings.extend(_migrate_requirements_txt(requirements_txt))
    
    # Check for environment.yml (conda)
    environment_yml = project_path / "environment.yml"
    if environment_yml.exists():
        warnings.extend(_migrate_environment_yml(environment_yml))
    
    return warnings


def _migrate_setup_py(setup_py_path: Path) -> List[str]:
    """Migrate setup.py dependency requirements."""
    warnings = []
    
    try:
        with open(setup_py_path, 'r') as f:
            content = f.read()
        
        # Check if it already has the new model-checker version
        if 'model-checker>=1.0' in content:
            warnings.append("setup.py already appears to be updated")
            return warnings
        
        # Update model-checker dependency
        if 'model-checker' in content:
            # Replace old version constraints
            content = content.replace(
                'model-checker>=0.14', 'model-checker>=1.0'
            ).replace(
                'model-checker>=0.15', 'model-checker>=1.0'  
            ).replace(
                'model-checker<1.0', 'model-checker>=1.0'
            )
            
            with open(setup_py_path, 'w') as f:
                f.write(content)
            
            warnings.append("Updated model-checker version requirement in setup.py")
        
    except Exception as e:
        warnings.append(f"Could not migrate setup.py: {e}")
    
    return warnings


def _migrate_pyproject_toml(pyproject_path: Path) -> List[str]:
    """Migrate pyproject.toml dependency requirements.""" 
    warnings = []
    
    try:
        with open(pyproject_path, 'r') as f:
            content = f.read()
        
        # Update model-checker dependency
        if 'model-checker' in content:
            # Simple regex replacement for common patterns
            import re
            
            # Replace version specifications
            content = re.sub(
                r'model-checker\s*[><=]+\s*[0-9.]+',
                'model-checker>=1.0',
                content
            )
            
            with open(pyproject_path, 'w') as f:
                f.write(content)
            
            warnings.append("Updated model-checker version requirement in pyproject.toml")
        
    except Exception as e:
        warnings.append(f"Could not migrate pyproject.toml: {e}")
    
    return warnings


def _migrate_requirements_txt(requirements_path: Path) -> List[str]:
    """Migrate requirements.txt file."""
    warnings = []
    
    try:
        with open(requirements_path, 'r') as f:
            lines = f.readlines()
        
        updated_lines = []
        modified = False
        
        for line in lines:
            stripped = line.strip()
            if stripped.startswith('model-checker'):
                # Update the version requirement
                updated_lines.append('model-checker>=1.0\n')
                modified = True
            else:
                updated_lines.append(line)
        
        if modified:
            with open(requirements_path, 'w') as f:
                f.writelines(updated_lines)
            warnings.append("Updated model-checker version requirement in requirements.txt")
        
    except Exception as e:
        warnings.append(f"Could not migrate requirements.txt: {e}")
    
    return warnings


def _migrate_environment_yml(environment_path: Path) -> List[str]:
    """Migrate conda environment.yml file."""
    warnings = []
    
    try:
        with open(environment_path, 'r') as f:
            content = f.read()
        
        # Update pip dependencies section
        if 'model-checker' in content:
            import re
            content = re.sub(
                r'- model-checker[><=\d.]*',
                '- model-checker>=1.0',
                content
            )
            
            with open(environment_path, 'w') as f:
                f.write(content)
            
            warnings.append("Updated model-checker version requirement in environment.yml")
        
    except Exception as e:
        warnings.append(f"Could not migrate environment.yml: {e}")
    
    return warnings


def _update_project_dependencies(project_path: Path) -> List[str]:
    """Update project dependencies for the new API."""
    warnings = []
    
    # Check if this is a pip-installable project
    if (project_path / "setup.py").exists() or (project_path / "pyproject.toml").exists():
        try:
            # Try to update the installed package
            result = subprocess.run(
                ["pip", "install", "-e", ".", "--upgrade"],
                cwd=project_path,
                capture_output=True,
                text=True,
                timeout=60
            )
            
            if result.returncode == 0:
                warnings.append("Successfully updated local package installation")
            else:
                warnings.append(f"Could not update local package: {result.stderr}")
                
        except subprocess.TimeoutExpired:
            warnings.append("Package update timed out")
        except Exception as e:
            warnings.append(f"Could not update package: {e}")
    
    return warnings


def _generate_migration_report(result: MigrationResult, 
                             file_results: Dict[Path, Tuple[bool, List[str]]],
                             report_path: Path) -> None:
    """Generate a detailed migration report."""
    
    with open(report_path, 'w') as f:
        f.write("# ModelChecker API Migration Report\n\n")
        
        # Summary
        f.write("## Summary\n\n")
        f.write(f"- **Overall Success**: {'✅' if result.success else '❌'}\n")
        f.write(f"- **Files Processed**: {result.files_processed}\n")
        f.write(f"- **Files Successfully Migrated**: {result.files_migrated}\n")
        f.write(f"- **Files Failed**: {result.files_failed}\n")
        
        if result.backup_directory:
            f.write(f"- **Backup Location**: {result.backup_directory}\n")
        
        f.write("\n")
        
        # File-by-file results
        f.write("## File Migration Results\n\n")
        
        for file_path, (success, warnings) in file_results.items():
            status = "✅" if success else "❌"
            f.write(f"### {status} {file_path.name}\n")
            f.write(f"**Path**: `{file_path}`\n\n")
            
            if warnings:
                f.write("**Messages**:\n")
                for warning in warnings:
                    f.write(f"- {warning}\n")
                f.write("\n")
        
        # Overall warnings and errors
        if result.warnings:
            f.write("## Warnings\n\n")
            for warning in result.warnings:
                f.write(f"- {warning}\n")
            f.write("\n")
        
        if result.errors:
            f.write("## Errors\n\n")
            for error in result.errors:
                f.write(f"- {error}\n")
            f.write("\n")
        
        # Next steps
        f.write("## Next Steps\n\n")
        f.write("1. Review the migration results above\n")
        f.write("2. Test your code to ensure it works with the new API\n")
        f.write("3. Update your documentation if needed\n")
        f.write("4. Consider running your test suite to verify functionality\n")
        
        if result.files_failed > 0:
            f.write("5. **Important**: Some files failed to migrate. Please review and migrate them manually.\n")


def _validate_project_migration(project_path: Path) -> List[str]:
    """Validate that the project migration was successful."""
    warnings = []
    
    # Check for common issues
    python_files = list(project_path.rglob("*.py"))
    
    for file_path in python_files:
        try:
            with open(file_path, 'r') as f:
                content = f.read()
            
            # Check for old import patterns that weren't caught
            old_patterns = [
                'from model_checker import BuildExample',
                'from model_checker import BuildModule',
                'from model_checker import ModelExplorer',
            ]
            
            for pattern in old_patterns:
                if pattern in content:
                    warnings.append(f"Possible unmigrated import in {file_path}: {pattern}")
            
            # Check for old API usage patterns
            old_api_patterns = [
                '.check_result()',
                'BuildExample(',
                'ModelExplorer(',
            ]
            
            for pattern in old_api_patterns:
                if pattern in content:
                    warnings.append(f"Possible old API usage in {file_path}: {pattern}")
        
        except Exception:
            # Skip files we can't read
            continue
    
    return warnings


def validate_migration(project_path: Path, 
                      test_command: Optional[str] = None) -> Dict[str, Any]:
    """
    Validate that a migrated project works correctly.
    
    Args:
        project_path: Path to the migrated project
        test_command: Optional command to run tests (e.g., "pytest", "python -m unittest")
        
    Returns:
        Dictionary with validation results
    """
    results = {
        'valid': True,
        'warnings': [],
        'errors': [],
        'test_results': None
    }
    
    try:
        # Basic syntax validation
        python_files = list(project_path.rglob("*.py"))
        
        for file_path in python_files:
            try:
                with open(file_path, 'r') as f:
                    content = f.read()
                
                # Try to parse the file
                import ast
                ast.parse(content)
                
            except SyntaxError as e:
                results['valid'] = False
                results['errors'].append(f"Syntax error in {file_path}: {e}")
            except Exception as e:
                results['warnings'].append(f"Could not validate {file_path}: {e}")
        
        # Try to import the project if it's a package
        if (project_path / "__init__.py").exists():
            try:
                import sys
                sys.path.insert(0, str(project_path.parent))
                
                import importlib
                module_name = project_path.name
                importlib.import_module(module_name)
                
                results['warnings'].append(f"Successfully imported {module_name}")
                
            except ImportError as e:
                results['warnings'].append(f"Could not import project: {e}")
            except Exception as e:
                results['warnings'].append(f"Error during import test: {e}")
            finally:
                if str(project_path.parent) in sys.path:
                    sys.path.remove(str(project_path.parent))
        
        # Run tests if command provided
        if test_command:
            try:
                result = subprocess.run(
                    test_command.split(),
                    cwd=project_path,
                    capture_output=True,
                    text=True,
                    timeout=300  # 5 minute timeout
                )
                
                results['test_results'] = {
                    'command': test_command,
                    'returncode': result.returncode,
                    'stdout': result.stdout,
                    'stderr': result.stderr,
                    'success': result.returncode == 0
                }
                
                if result.returncode != 0:
                    results['valid'] = False
                    results['errors'].append(f"Tests failed: {result.stderr}")
                
            except subprocess.TimeoutExpired:
                results['warnings'].append("Test execution timed out")
            except Exception as e:
                results['warnings'].append(f"Could not run tests: {e}")
    
    except Exception as e:
        results['valid'] = False
        results['errors'].append(f"Validation error: {e}")
    
    return results


# Example usage and testing
def _example_project_migration():
    """Example of project migration for testing."""
    
    # This would be run on a real project directory
    project_path = Path("example_project")
    
    print(f"Migrating project: {project_path}")
    
    if not project_path.exists():
        print("Example project directory not found - skipping example")
        return
    
    # Migrate the project
    result = migrate_project(project_path, backup=True, parallel=False)
    
    print(f"\nMigration Results:")
    print(f"Success: {result.success}")
    print(f"Files processed: {result.files_processed}")
    print(f"Files migrated: {result.files_migrated}")
    print(f"Files failed: {result.files_failed}")
    
    if result.warnings:
        print("\nWarnings:")
        for warning in result.warnings:
            print(f"  - {warning}")
    
    if result.errors:
        print("\nErrors:")
        for error in result.errors:
            print(f"  - {error}")
    
    # Validate the migration
    validation = validate_migration(project_path)
    print(f"\nValidation: {'Valid' if validation['valid'] else 'Invalid'}")


if __name__ == "__main__":
    _example_project_migration()