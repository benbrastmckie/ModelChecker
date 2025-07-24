"""
Command-line interface for ModelChecker API migration tools.

This module provides a command-line interface for migrating code from the old
ModelChecker API to the new modernized API.

Usage:
    python -m model_checker.migrate [options] <path>
    python -m model_checker.migrate --help
"""

import sys
import argparse
from pathlib import Path
from typing import List, Optional

from .project import migrate_project, validate_migration
from .transformer import transform_file, batch_transform_files
from .notebook import migrate_notebook, find_notebooks_in_directory, batch_migrate_notebooks
from .config import validate_settings_compatibility


def main():
    """Main entry point for the migration CLI."""
    parser = create_argument_parser()
    args = parser.parse_args()
    
    try:
        if args.command == 'project':
            handle_project_migration(args)
        elif args.command == 'file':
            handle_file_migration(args)
        elif args.command == 'notebook':
            handle_notebook_migration(args)
        elif args.command == 'validate':
            handle_validation(args)
        elif args.command == 'check':
            handle_check(args)
        else:
            # Default behavior for backward compatibility
            if args.path.is_dir():
                handle_project_migration(args)
            elif args.path.suffix == '.py':
                handle_file_migration(args)
            elif args.path.suffix == '.ipynb':
                handle_notebook_migration(args)
            else:
                print(f"Error: Unknown file type for {args.path}")
                sys.exit(1)
    
    except KeyboardInterrupt:
        print("\nMigration interrupted by user")
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


def create_argument_parser() -> argparse.ArgumentParser:
    """Create the command-line argument parser."""
    
    parser = argparse.ArgumentParser(
        description="Migrate ModelChecker code from old API to new API",
        epilog="Examples:\n"
               "  %(prog)s project /path/to/project\n"
               "  %(prog)s file script.py\n"
               "  %(prog)s notebook analysis.ipynb\n"
               "  %(prog)s validate /path/to/project\n",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    
    # Global options
    parser.add_argument(
        '--version',
        action='version',
        version='ModelChecker Migration Tools 0.1.0'
    )
    
    parser.add_argument(
        '--no-backup',
        action='store_true',
        help='Do not create backup files (dangerous!)'
    )
    
    parser.add_argument(
        '--dry-run',
        action='store_true',
        help='Show what would be changed without making changes'
    )
    
    parser.add_argument(
        '--parallel',
        action='store_true',
        default=True,
        help='Use parallel processing (default: True)'
    )
    
    parser.add_argument(
        '--no-parallel',
        dest='parallel',
        action='store_false',
        help='Disable parallel processing'
    )
    
    parser.add_argument(
        '--max-workers',
        type=int,
        default=None,
        help='Maximum number of parallel workers'
    )
    
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Verbose output'
    )
    
    # Subcommands
    subparsers = parser.add_subparsers(dest='command', help='Migration commands')
    
    # Project migration
    project_parser = subparsers.add_parser(
        'project',
        help='Migrate an entire project'
    )
    project_parser.add_argument(
        'path',
        type=Path,
        help='Path to the project directory'
    )
    project_parser.add_argument(
        '--include-tests',
        action='store_true',
        default=True,
        help='Include test files in migration (default: True)'
    )
    project_parser.add_argument(
        '--exclude-tests',
        dest='include_tests',
        action='store_false',
        help='Exclude test files from migration'
    )
    
    # File migration
    file_parser = subparsers.add_parser(
        'file',
        help='Migrate a single Python file or multiple files'
    )
    file_parser.add_argument(
        'path',
        type=Path,
        nargs='+',
        help='Path(s) to Python file(s)'
    )
    
    # Notebook migration
    notebook_parser = subparsers.add_parser(
        'notebook',
        help='Migrate Jupyter notebook(s)'
    )
    notebook_parser.add_argument(
        'path',
        type=Path,
        nargs='+',
        help='Path(s) to .ipynb file(s) or directory'
    )
    
    # Validation
    validate_parser = subparsers.add_parser(
        'validate',
        help='Validate a migrated project'
    )
    validate_parser.add_argument(
        'path',
        type=Path,
        help='Path to the project directory'
    )
    validate_parser.add_argument(
        '--test-command',
        type=str,
        help='Command to run tests (e.g., "pytest", "python -m unittest")'
    )
    
    # Check what needs migration
    check_parser = subparsers.add_parser(
        'check',
        help='Check what needs to be migrated without making changes'
    )
    check_parser.add_argument(
        'path',
        type=Path,
        help='Path to check'
    )
    
    # Backward compatibility: allow path as positional argument without subcommand
    parser.add_argument(
        'path',
        type=Path,
        nargs='?',
        help='Path to migrate (auto-detects type)'
    )
    
    return parser


def handle_project_migration(args):
    """Handle project migration command."""
    project_path = args.path
    
    if not project_path.exists():
        print(f"Error: Project path does not exist: {project_path}")
        sys.exit(1)
    
    if not project_path.is_dir():
        print(f"Error: Project path is not a directory: {project_path}")
        sys.exit(1)
    
    print(f"Migrating project: {project_path}")
    
    if args.dry_run:
        print("DRY RUN: No changes will be made")
        # TODO: Implement dry run functionality
        return
    
    # Perform migration
    result = migrate_project(
        project_path=project_path,
        backup=not args.no_backup,
        include_tests=getattr(args, 'include_tests', True),
        parallel=args.parallel,
        max_workers=args.max_workers
    )
    
    # Report results
    print(f"\nMigration Results:")
    print(f"  Success: {'✅' if result.success else '❌'}")
    print(f"  Files processed: {result.files_processed}")
    print(f"  Files migrated: {result.files_migrated}")
    print(f"  Files failed: {result.files_failed}")
    
    if result.backup_directory:
        print(f"  Backup created: {result.backup_directory}")
    
    if args.verbose and result.warnings:
        print(f"\nWarnings:")
        for warning in result.warnings:
            print(f"  - {warning}")
    
    if result.errors:
        print(f"\nErrors:")
        for error in result.errors:
            print(f"  - {error}")
    
    if not result.success:
        print(f"\n❌ Migration completed with errors. Check the migration report for details.")
        sys.exit(1)
    else:
        print(f"\n✅ Migration completed successfully!")


def handle_file_migration(args):
    """Handle single file or multiple file migration."""
    file_paths = args.path if isinstance(args.path, list) else [args.path]
    
    # Validate paths
    for file_path in file_paths:
        if not file_path.exists():
            print(f"Error: File does not exist: {file_path}")
            sys.exit(1)
        
        if not file_path.is_file():
            print(f"Error: Path is not a file: {file_path}")
            sys.exit(1)
        
        if file_path.suffix != '.py':
            print(f"Warning: File is not a Python file: {file_path}")
    
    print(f"Migrating {len(file_paths)} file(s)...")
    
    if args.dry_run:
        print("DRY RUN: No changes will be made")
        # TODO: Implement dry run for files
        return
    
    # Migrate files
    if len(file_paths) == 1:
        # Single file
        success, warnings = transform_file(file_paths[0], backup=not args.no_backup)
        
        status = "✅" if success else "❌"
        print(f"{status} {file_paths[0].name}")
        
        if args.verbose and warnings:
            for warning in warnings:
                print(f"  - {warning}")
    else:
        # Multiple files
        results = batch_transform_files(file_paths, backup=not args.no_backup)
        
        successful = 0
        failed = 0
        
        for file_path, (success, warnings) in results.items():
            status = "✅" if success else "❌"
            print(f"{status} {file_path.name}")
            
            if success:
                successful += 1
            else:
                failed += 1
            
            if args.verbose and warnings:
                for warning in warnings:
                    print(f"    - {warning}")
        
        print(f"\nSummary: {successful} successful, {failed} failed")
        
        if failed > 0:
            sys.exit(1)


def handle_notebook_migration(args):
    """Handle notebook migration command."""
    paths = args.path if isinstance(args.path, list) else [args.path]
    
    # Collect all notebook files
    notebook_files = []
    
    for path in paths:
        if not path.exists():
            print(f"Error: Path does not exist: {path}")
            sys.exit(1)
        
        if path.is_file():
            if path.suffix.lower() == '.ipynb':
                notebook_files.append(path)
            else:
                print(f"Warning: File is not a Jupyter notebook: {path}")
        elif path.is_dir():
            # Find notebooks in directory
            found_notebooks = find_notebooks_in_directory(path, recursive=True)
            notebook_files.extend(found_notebooks)
        else:
            print(f"Error: Invalid path: {path}")
            sys.exit(1)
    
    if not notebook_files:
        print("No Jupyter notebooks found to migrate")
        return
    
    print(f"Migrating {len(notebook_files)} notebook(s)...")
    
    if args.dry_run:
        print("DRY RUN: No changes will be made")
        for notebook_file in notebook_files:
            print(f"  Would migrate: {notebook_file}")
        return
    
    # Migrate notebooks
    results = batch_migrate_notebooks(notebook_files, backup=not args.no_backup)
    
    successful = 0
    failed = 0
    
    for notebook_path, (success, warnings) in results.items():
        status = "✅" if success else "❌"
        print(f"{status} {notebook_path.name}")
        
        if success:
            successful += 1
        else:
            failed += 1
        
        if args.verbose and warnings:
            for warning in warnings:
                print(f"    - {warning}")
    
    print(f"\nSummary: {successful} successful, {failed} failed")
    
    if failed > 0:
        sys.exit(1)


def handle_validation(args):
    """Handle validation command."""
    project_path = args.path
    
    if not project_path.exists():
        print(f"Error: Project path does not exist: {project_path}")
        sys.exit(1)
    
    if not project_path.is_dir():
        print(f"Error: Project path is not a directory: {project_path}")
        sys.exit(1)
    
    print(f"Validating migrated project: {project_path}")
    
    # Validate the migration
    validation = validate_migration(
        project_path,
        test_command=getattr(args, 'test_command', None)
    )
    
    print(f"\nValidation Results:")
    print(f"  Valid: {'✅' if validation['valid'] else '❌'}")
    
    if validation['warnings']:
        print(f"  Warnings:")
        for warning in validation['warnings']:
            print(f"    - {warning}")
    
    if validation['errors']:
        print(f"  Errors:")
        for error in validation['errors']:
            print(f"    - {error}")
    
    if validation['test_results']:
        test_results = validation['test_results']
        test_status = "✅" if test_results['success'] else "❌"
        print(f"  Tests: {test_status}")
        
        if args.verbose:
            print(f"    Command: {test_results['command']}")
            print(f"    Return code: {test_results['returncode']}")
            
            if test_results['stdout']:
                print(f"    Stdout: {test_results['stdout'][:200]}...")
            
            if test_results['stderr']:
                print(f"    Stderr: {test_results['stderr'][:200]}...")
    
    if not validation['valid']:
        sys.exit(1)


def handle_check(args):
    """Handle check command - analyze what needs migration without changing anything."""
    path = args.path
    
    if not path.exists():
        print(f"Error: Path does not exist: {path}")
        sys.exit(1)
    
    print(f"Checking migration needs for: {path}")
    
    if path.is_file():
        if path.suffix == '.py':
            needs_migration = check_python_file_needs_migration(path)
            if needs_migration:
                print(f"✅ {path.name} needs migration")
            else:
                print(f"❌ {path.name} does not need migration")
        elif path.suffix == '.ipynb':
            needs_migration = check_notebook_needs_migration(path)
            if needs_migration:
                print(f"✅ {path.name} needs migration")
            else:
                print(f"❌ {path.name} does not need migration")
        else:
            print(f"Unknown file type: {path}")
    
    elif path.is_dir():
        # Check all files in directory
        python_files = list(path.rglob("*.py"))
        notebook_files = find_notebooks_in_directory(path, recursive=True)
        
        needs_migration = []
        already_migrated = []
        
        for file_path in python_files:
            if check_python_file_needs_migration(file_path):
                needs_migration.append(file_path)
            else:
                already_migrated.append(file_path)
        
        for file_path in notebook_files:
            if check_notebook_needs_migration(file_path):
                needs_migration.append(file_path)
            else:
                already_migrated.append(file_path)
        
        print(f"\nSummary:")
        print(f"  Files needing migration: {len(needs_migration)}")
        print(f"  Files already migrated: {len(already_migrated)}")
        
        if args.verbose:
            if needs_migration:
                print(f"\nFiles needing migration:")
                for file_path in needs_migration:
                    print(f"  - {file_path}")
            
            if already_migrated:
                print(f"\nFiles already migrated:")
                for file_path in already_migrated:
                    print(f"  - {file_path}")


def check_python_file_needs_migration(file_path: Path) -> bool:
    """Check if a Python file needs migration."""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Look for old API patterns
        old_patterns = [
            'from model_checker import BuildExample',
            'from model_checker import BuildModule',
            'from model_checker import BuildProject',
            'from model_checker import ModelExplorer',
            'from model_checker import check_formula',
            'from model_checker import get_theory',
            'BuildExample(',
            'BuildModule(',
            'BuildProject(',
            'ModelExplorer(',
            '.check_result()',
        ]
        
        for pattern in old_patterns:
            if pattern in content:
                return True
        
        return False
        
    except Exception:
        return False


def check_notebook_needs_migration(file_path: Path) -> bool:
    """Check if a Jupyter notebook needs migration."""
    try:
        import json
        
        with open(file_path, 'r', encoding='utf-8') as f:
            notebook = json.load(f)
        
        # Check if already migrated
        if notebook.get('metadata', {}).get('migrated_to_api_v1'):
            return False
        
        # Look for old API patterns in code cells
        for cell in notebook.get('cells', []):
            if cell.get('cell_type') == 'code' and 'source' in cell:
                source = ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']
                
                if check_python_file_needs_migration_content(source):
                    return True
        
        return False
        
    except Exception:
        return False


def check_python_file_needs_migration_content(content: str) -> bool:
    """Check if Python content needs migration."""
    old_patterns = [
        'from model_checker import BuildExample',
        'from model_checker import BuildModule',
        'from model_checker import BuildProject', 
        'from model_checker import ModelExplorer',
        'from model_checker import check_formula',
        'BuildExample(',
        'ModelExplorer(',
        '.check_result()',
    ]
    
    for pattern in old_patterns:
        if pattern in content:
            return True
    
    return False


if __name__ == '__main__':
    main()