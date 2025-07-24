"""
Jupyter notebook migration utilities.

This module provides tools for migrating Jupyter notebooks from the old
ModelChecker API to the new modernized API.
"""

import json
import re
from pathlib import Path
from typing import List, Dict, Any, Tuple, Optional

from .transformer import transform_code


def migrate_notebook(notebook_path: Path, backup: bool = True) -> Tuple[bool, List[str]]:
    """
    Migrate a Jupyter notebook to use the new ModelChecker API.
    
    Args:
        notebook_path: Path to the .ipynb file
        backup: Whether to create a backup file
        
    Returns:
        Tuple of (success, warnings)
    """
    try:
        # Read the notebook
        with open(notebook_path, 'r', encoding='utf-8') as f:
            notebook = json.load(f)
        
        # Validate notebook format
        if not isinstance(notebook, dict) or 'cells' not in notebook:
            return False, ["Invalid notebook format"]
        
        # Create backup if requested
        if backup:
            backup_path = notebook_path.with_suffix('.backup.ipynb')
            with open(backup_path, 'w', encoding='utf-8') as f:
                json.dump(notebook, f, indent=1)
        
        # Track changes and warnings
        changes_made = False
        all_warnings = []
        
        # Process each cell
        for cell_index, cell in enumerate(notebook['cells']):
            if cell.get('cell_type') == 'code' and 'source' in cell:
                # Get the cell source code
                if isinstance(cell['source'], list):
                    source_lines = cell['source']
                    source_code = ''.join(source_lines)
                else:
                    source_code = cell['source']
                
                # Skip empty cells
                if not source_code.strip():
                    continue
                
                # Transform the code
                transformed_code, warnings = transform_code(source_code)
                
                # Check if changes were made
                if transformed_code != source_code:
                    changes_made = True
                    
                    # Update the cell
                    if isinstance(cell['source'], list):
                        # Preserve line-by-line format
                        cell['source'] = transformed_code.splitlines(keepends=True)
                    else:
                        cell['source'] = transformed_code
                    
                    # Add cell identification to warnings
                    cell_warnings = [f"Cell {cell_index + 1}: {w}" for w in warnings]
                    all_warnings.extend(cell_warnings)
        
        # Add notebook-specific migrations
        notebook_warnings = _migrate_notebook_metadata(notebook)
        all_warnings.extend(notebook_warnings)
        
        # Write back the notebook if changes were made
        if changes_made or notebook_warnings:
            with open(notebook_path, 'w', encoding='utf-8') as f:
                json.dump(notebook, f, indent=1, ensure_ascii=False)
            
            if not changes_made:
                all_warnings.append("Only metadata changes were made")
        
        success_message = f"Successfully migrated {notebook_path}"
        if backup:
            success_message += f" (backup: {backup_path})"
        
        return True, [success_message] + all_warnings
        
    except json.JSONDecodeError as e:
        return False, [f"Invalid JSON in notebook: {e}"]
    except Exception as e:
        return False, [f"Error migrating notebook: {e}"]


def _migrate_notebook_metadata(notebook: Dict[str, Any]) -> List[str]:
    """
    Migrate notebook metadata and add migration information.
    
    Args:
        notebook: The notebook dictionary
        
    Returns:
        List of warning messages about metadata changes
    """
    warnings = []
    
    # Ensure metadata exists
    if 'metadata' not in notebook:
        notebook['metadata'] = {}
    
    # Add migration information
    migration_info = {
        'migrated_to_api_v1': True,
        'migration_tool_version': '0.1.0',
        'original_api_version': '0.14.x'
    }
    
    # Check if already migrated
    if notebook['metadata'].get('migrated_to_api_v1'):
        warnings.append("Notebook appears to already be migrated")
        return warnings
    
    # Add migration metadata
    notebook['metadata'].update(migration_info)
    
    # Update kernel requirements if present
    if 'kernelspec' in notebook['metadata']:
        kernel_info = notebook['metadata']['kernelspec']
        if kernel_info.get('name') == 'python3':
            # Add note about new dependencies
            if 'display_name' not in kernel_info:
                kernel_info['display_name'] = 'Python 3'
            
            warnings.append("Updated kernel metadata for new API")
    
    # Check for widgets and update requirements
    uses_widgets = _check_notebook_uses_widgets(notebook)
    if uses_widgets:
        if 'requirements' not in notebook['metadata']:
            notebook['metadata']['requirements'] = []
        
        requirements = notebook['metadata']['requirements']
        if 'ipywidgets' not in requirements:
            requirements.append('ipywidgets')
            warnings.append("Added ipywidgets to notebook requirements")
    
    return warnings


def _check_notebook_uses_widgets(notebook: Dict[str, Any]) -> bool:
    """
    Check if the notebook uses ModelChecker widgets.
    
    Args:
        notebook: The notebook dictionary
        
    Returns:
        True if widgets are used
    """
    widget_indicators = [
        'ModelExplorer',
        'InteractiveExplorer',
        'FormulaChecker',
        '.display()',
        'ipywidgets'
    ]
    
    for cell in notebook.get('cells', []):
        if cell.get('cell_type') == 'code' and 'source' in cell:
            source = ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']
            
            for indicator in widget_indicators:
                if indicator in source:
                    return True
    
    return False


def batch_migrate_notebooks(notebook_paths: List[Path], backup: bool = True) -> Dict[Path, Tuple[bool, List[str]]]:
    """
    Migrate multiple Jupyter notebooks to the new API.
    
    Args:
        notebook_paths: List of paths to .ipynb files
        backup: Whether to create backup files
        
    Returns:
        Dictionary mapping paths to (success, warnings) tuples
    """
    results = {}
    
    for notebook_path in notebook_paths:
        if notebook_path.suffix.lower() != '.ipynb':
            results[notebook_path] = (False, ["Not a Jupyter notebook file"])
            continue
        
        if not notebook_path.exists():
            results[notebook_path] = (False, ["File does not exist"])
            continue
        
        success, warnings = migrate_notebook(notebook_path, backup)
        results[notebook_path] = (success, warnings)
    
    return results


def find_notebooks_in_directory(directory: Path, recursive: bool = True) -> List[Path]:
    """
    Find all Jupyter notebook files in a directory.
    
    Args:
        directory: Directory to search
        recursive: Whether to search subdirectories
        
    Returns:
        List of paths to .ipynb files
    """
    if recursive:
        pattern = "**/*.ipynb"
    else:
        pattern = "*.ipynb"
    
    return list(directory.glob(pattern))


def create_migration_summary_notebook(results: Dict[Path, Tuple[bool, List[str]]], 
                                    output_path: Path) -> None:
    """
    Create a summary notebook documenting the migration results.
    
    Args:
        results: Migration results from batch_migrate_notebooks
        output_path: Where to save the summary notebook
    """
    # Create summary notebook content
    cells = []
    
    # Title cell
    title_cell = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "# ModelChecker API Migration Summary\n",
            "\n",
            "This notebook summarizes the results of migrating notebooks from the old ModelChecker API to the new API.\n"
        ]
    }
    cells.append(title_cell)
    
    # Statistics cell
    successful = sum(1 for success, _ in results.values() if success)
    failed = len(results) - successful
    
    stats_cell = {
        "cell_type": "markdown", 
        "metadata": {},
        "source": [
            f"## Migration Statistics\n",
            f"\n",
            f"- **Total notebooks**: {len(results)}\n",
            f"- **Successfully migrated**: {successful}\n",
            f"- **Failed migrations**: {failed}\n",
            f"- **Success rate**: {successful/len(results)*100:.1f}%\n"
        ]
    }
    cells.append(stats_cell)
    
    # Detailed results
    results_cell = {
        "cell_type": "markdown",
        "metadata": {},
        "source": ["## Detailed Results\n\n"]
    }
    
    for notebook_path, (success, warnings) in results.items():
        status = "✅ Success" if success else "❌ Failed"
        results_cell["source"].append(f"### {notebook_path.name}\n")
        results_cell["source"].append(f"**Status**: {status}\n\n")
        
        if warnings:
            results_cell["source"].append("**Messages**:\n")
            for warning in warnings:
                results_cell["source"].append(f"- {warning}\n")
            results_cell["source"].append("\n")
    
    cells.append(results_cell)
    
    # Code cell for re-running migrations
    code_cell = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Re-run migration for failed notebooks\n",
            "from pathlib import Path\n",
            "from model_checker.migrate import migrate_notebook\n",
            "\n",
            "failed_notebooks = [\n"
        ]
    }
    
    # Add failed notebooks to the code
    for notebook_path, (success, _) in results.items():
        if not success:
            code_cell["source"].append(f'    Path("{notebook_path}"),\n')
    
    code_cell["source"].extend([
        "]\n",
        "\n",
        "for notebook_path in failed_notebooks:\n",
        "    success, warnings = migrate_notebook(notebook_path)\n",
        "    print(f'{notebook_path}: {\"Success\" if success else \"Failed\"}')\n",
        "    for warning in warnings:\n",
        "        print(f'  - {warning}')\n"
    ])
    
    cells.append(code_cell)
    
    # Create the notebook structure
    notebook = {
        "cells": cells,
        "metadata": {
            "kernelspec": {
                "display_name": "Python 3",
                "language": "python",
                "name": "python3"
            },
            "language_info": {
                "name": "python",
                "version": "3.8.0"
            }
        },
        "nbformat": 4,
        "nbformat_minor": 4
    }
    
    # Save the summary notebook
    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(notebook, f, indent=1, ensure_ascii=False)


# Example usage and testing
def _example_notebook_migration():
    """Example of notebook migration for testing."""
    
    # Create a sample notebook for testing
    sample_notebook = {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": None,
                "metadata": {},
                "outputs": [],
                "source": [
                    "from model_checker import BuildExample, get_theory, ModelExplorer\n",
                    "\n",
                    "theory = get_theory('logos')\n",
                    "example = [[], ['p → q'], {'N': 3, 'max_time': 5}]\n",
                    "model = BuildExample('test', theory, example)\n",
                    "result = model.check_result()\n",
                    "\n",
                    "explorer = ModelExplorer()\n",
                    "explorer.display()\n"
                ]
            }
        ],
        "metadata": {
            "kernelspec": {
                "display_name": "Python 3",
                "language": "python", 
                "name": "python3"
            }
        },
        "nbformat": 4,
        "nbformat_minor": 4
    }
    
    # Save sample notebook
    sample_path = Path("test_notebook.ipynb")
    with open(sample_path, 'w') as f:
        json.dump(sample_notebook, f, indent=1)
    
    print("Created sample notebook:")
    print(json.dumps(sample_notebook, indent=2))
    
    # Migrate it
    success, warnings = migrate_notebook(sample_path, backup=True)
    
    print(f"\nMigration result: {'Success' if success else 'Failed'}")
    for warning in warnings:
        print(f"  - {warning}")
    
    # Show migrated result
    if success:
        with open(sample_path, 'r') as f:
            migrated_notebook = json.load(f)
        
        print("\nMigrated notebook:")
        print(json.dumps(migrated_notebook, indent=2))
    
    # Clean up
    sample_path.unlink(missing_ok=True)
    Path("test_notebook.backup.ipynb").unlink(missing_ok=True)


if __name__ == "__main__":
    _example_notebook_migration()