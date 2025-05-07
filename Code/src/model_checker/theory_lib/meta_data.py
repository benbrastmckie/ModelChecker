"""
Metadata management for theory libraries.

This module provides utilities for managing version information and licensing
across all theory libraries in the ModelChecker framework.

It includes functions for:
- Updating version information
- Creating/updating license files
- Creating/updating citation files
- Verifying metadata consistency
"""

import os
import re
import datetime
from typing import Dict, List, Optional, Any, Tuple

from model_checker.utils import get_model_checker_version

from model_checker.theory_lib import (
    AVAILABLE_THEORIES,
    get_theory_version_registry,
    get_theory_license_info,
    create_license_file,
    create_citation_file
)

def update_all_theory_versions(new_version: Optional[str] = None) -> Dict[str, str]:
    """Update version information for all theories.
    
    Args:
        new_version: Optional new version to set for all theories.
                    If None, only updates the model_checker_version.
    
    Returns:
        dict: Dictionary mapping theory names to their updated versions
    """
    updated_versions = {}
    model_checker_version = get_model_checker_version()
    
    for theory_name in AVAILABLE_THEORIES:
        try:
            # Get theory directory
            theory_dir = os.path.dirname(os.path.abspath(__file__))
            init_path = os.path.join(theory_dir, theory_name, "__init__.py")
            
            if not os.path.exists(init_path):
                print(f"WARNING: __init__.py not found for theory '{theory_name}'")
                continue
                
            # Read current content
            with open(init_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # Update model_checker_version
            mc_version_pattern = re.compile(
                r'__model_checker_version__\s*=\s*["\'].*?["\']'
            )
            
            # Check if the file contains model_checker_version
            if '__model_checker_version__' in content:
                content = mc_version_pattern.sub(
                    f'__model_checker_version__ = "{model_checker_version}"', 
                    content
                )
            else:
                # Add the import for get_model_checker_version if needed
                if 'from model_checker.utils import get_model_checker_version' not in content:
                    import_pattern = re.compile(r'(from[\s\S]*?\n\n|import[\s\S]*?\n\n)')
                    # Try to add after imports
                    if import_pattern.search(content):
                        content = import_pattern.sub(
                            r'\1# Import version utilities\nfrom model_checker.utils import get_model_checker_version\n\n',
                            content
                        )
                    else:
                        # Add at the top after any docstring
                        if content.startswith('"""'):
                            # Find the end of the docstring
                            end_docstring = content.find('"""', 3)
                            if end_docstring > 0:
                                insertion_point = end_docstring + 3
                                content = content[:insertion_point] + '\n\n# Import version utilities\nfrom model_checker.utils import get_model_checker_version\n' + content[insertion_point:]
                        else:
                            # Just add at the top
                            content = '# Import version utilities\nfrom model_checker.utils import get_model_checker_version\n\n' + content
                
                # Find a good place to add version information
                version_block = f"\n# Version information\n__model_checker_version__ = \"{model_checker_version}\"  # ModelChecker version this was built with\n"
                
                # Add before __all__ if it exists
                all_pattern = re.compile(r'__all__\s*=\s*\[')
                if all_pattern.search(content):
                    all_match = all_pattern.search(content)
                    if all_match:
                        match_pos = all_match.start()
                        content = content[:match_pos] + version_block + content[match_pos:]
                else:
                    # Add at the end
                    content += version_block
            
            # Update theory version if specified
            if new_version:
                version_pattern = re.compile(r'__version__\s*=\s*["\'].*?["\']')
                
                if '__version__' in content:
                    content = version_pattern.sub(f'__version__ = "{new_version}"', content)
                else:
                    # Find where to insert the version
                    if '__model_checker_version__' in content:
                        content = content.replace(
                            f'__model_checker_version__ = "{model_checker_version}"',
                            f'__version__ = "{new_version}"  # Theory version\n__model_checker_version__ = "{model_checker_version}"'
                        )
                    else:
                        # Add at the end
                        content += f'\n__version__ = "{new_version}"  # Theory version\n'
                
                updated_versions[theory_name] = new_version
            else:
                # Extract current version
                version_pattern = re.compile(r'__version__\s*=\s*["\'](.+?)["\']')
                version_match = version_pattern.search(content)
                if version_match:
                    updated_versions[theory_name] = version_match.group(1)
                else:
                    updated_versions[theory_name] = "unknown"
            
            # Update __all__ list to include version attributes if needed
            if '__all__' in content:
                all_content_pattern = re.compile(r'__all__\s*=\s*\[([\s\S]*?)\]')
                all_content_match = all_content_pattern.search(content)
                if all_content_match:
                    all_items = all_content_match.group(1)
                    updates_needed = []
                    
                    if '"__version__"' not in all_items and "'__version__'" not in all_items:
                        updates_needed.append('"__version__",                # Theory version information')
                    
                    if '"__model_checker_version__"' not in all_items and "'__model_checker_version__'" not in all_items:
                        updates_needed.append('"__model_checker_version__",  # Compatible ModelChecker version')
                    
                    if updates_needed:
                        # Add the missing items to __all__
                        updated_all = all_items.rstrip()
                        if not updated_all.endswith(','):
                            updated_all += ','
                        
                        for item in updates_needed:
                            updated_all += f'\n    {item}'
                        
                        content = all_content_pattern.sub(f"__all__ = [{updated_all}\n]", content)
            
            # Write updated content
            with open(init_path, 'w', encoding='utf-8') as f:
                f.write(content)
            
        except Exception as e:
            print(f"Error updating version for theory '{theory_name}': {str(e)}")
            updated_versions[theory_name] = "error"
    
    return updated_versions

def create_all_license_files(license_type: str = "GPL-3.0", author_info: Optional[Dict[str, Any]] = None) -> Dict[str, bool]:
    """Create license files for all theories.
    
    Args:
        license_type: Type of license (GPL-3.0, MIT, etc.)
        author_info: Optional author information
    
    Returns:
        dict: Dictionary mapping theory names to success status
    """
    results = {}
    
    for theory_name in AVAILABLE_THEORIES:
        try:
            result = create_license_file(theory_name, license_type, author_info)
            results[theory_name] = result
        except Exception as e:
            print(f"Error creating license for theory '{theory_name}': {str(e)}")
            results[theory_name] = False
    
    return results

def create_all_citation_files(author_info: Optional[Dict[str, str]] = None) -> Dict[str, bool]:
    """Create citation files for all theories.
    
    Args:
        author_info: Optional author information with keys 'name', 'email', etc.
    
    Returns:
        dict: Dictionary mapping theory names to success status
    """
    results = {}
    year = datetime.datetime.now().year
    
    # Get author name from info or use placeholder
    author_name = author_info.get('name', '[Author Name]') if author_info else '[Author Name]'
    
    for theory_name in AVAILABLE_THEORIES:
        try:
            # Generate citation text
            citation_text = f"""# Citation Information

If you use this theory implementation in academic work, please cite:

{author_name}. ({year}). {theory_name.title()}: A semantic theory implementation for the
ModelChecker framework.

## Theory Implementation Notes

This theory implementation is part of the ModelChecker framework.
For more detailed information about the theory's mathematical foundations,
please include additional references here.
"""
            result = create_citation_file(theory_name, citation_text)
            results[theory_name] = result
        except Exception as e:
            print(f"Error creating citation for theory '{theory_name}': {str(e)}")
            results[theory_name] = False
    
    return results

def verify_metadata_consistency() -> Dict[str, Dict[str, Any]]:
    """Verify metadata consistency across all theories.
    
    Checks for consistent versioning, licensing, and citation information.
    
    Returns:
        dict: Dictionary with verification results for each theory
    """
    results = {}
    
    for theory_name in AVAILABLE_THEORIES:
        theory_results = {
            'version': {
                'found': False,
                'value': None,
                'model_checker_version_found': False,
                'model_checker_version': None,
            },
            'license': {
                'found': False,
                'type': None,
            },
            'citation': {
                'found': False,
            }
        }
        
        # Check for version info
        try:
            # Import the theory module
            try:
                import importlib
                theory_module = importlib.import_module(f"model_checker.theory_lib.{theory_name}")
                
                # Check version
                if hasattr(theory_module, "__version__"):
                    theory_results['version']['found'] = True
                    theory_results['version']['value'] = theory_module.__version__
                
                # Check model_checker_version
                if hasattr(theory_module, "__model_checker_version__"):
                    theory_results['version']['model_checker_version_found'] = True
                    theory_results['version']['model_checker_version'] = theory_module.__model_checker_version__
            except ImportError:
                pass
        except Exception as e:
            theory_results['version']['error'] = str(e)
        
        # Check for license file
        try:
            license_info = get_theory_license_info(theory_name)
            theory_results['license']['found'] = license_info['path'] is not None
            theory_results['license']['type'] = license_info['type']
        except Exception as e:
            theory_results['license']['error'] = str(e)
        
        # Check for citation file
        try:
            theory_dir = os.path.dirname(os.path.abspath(__file__))
            citation_path = os.path.join(theory_dir, theory_name, "CITATION.md")
            theory_results['citation']['found'] = os.path.exists(citation_path)
        except Exception as e:
            theory_results['citation']['error'] = str(e)
        
        results[theory_name] = theory_results
    
    return results

def print_metadata_report(verify_output: Optional[Dict[str, Dict[str, Any]]] = None) -> None:
    """Print a formatted report of metadata consistency.
    
    Args:
        verify_output: Optional verification output from verify_metadata_consistency()
                      If None, will call the function to get fresh results
    """
    if verify_output is None:
        verify_output = verify_metadata_consistency()
    
    print("\n=== ModelChecker Theory Metadata Report ===\n")
    print(f"ModelChecker Version: {get_model_checker_version()}")
    print(f"Theories: {', '.join(AVAILABLE_THEORIES)}")
    print("\n--- Metadata Status ---\n")
    
    # Calculate column widths
    theory_width = max(len(t) for t in AVAILABLE_THEORIES) + 2
    version_width = 12
    mc_version_width = 20
    license_width = 10
    citation_width = 10
    
    # Print header
    header = (
        f"{'Theory':{theory_width}} | "
        f"{'Version':{version_width}} | "
        f"{'MC Version':{mc_version_width}} | "
        f"{'License':{license_width}} | "
        f"{'Citation':{citation_width}}"
    )
    print(header)
    print("-" * len(header))
    
    # Print each theory's status
    for theory_name, status in verify_output.items():
        version_status = status['version']['value'] if status['version']['found'] else "Missing"
        mc_version_status = status['version']['model_checker_version'] if status['version']['model_checker_version_found'] else "Missing"
        license_status = status['license']['type'] if status['license']['found'] else "Missing"
        citation_status = "Present" if status['citation']['found'] else "Missing"
        
        row = (
            f"{theory_name:{theory_width}} | "
            f"{version_status:{version_width}} | "
            f"{mc_version_status:{mc_version_width}} | "
            f"{license_status:{license_width}} | "
            f"{citation_status:{citation_width}}"
        )
        print(row)
    
    print("\n--- Recommendations ---\n")
    
    # Generate recommendations
    recommendations = []
    
    # Check version consistency
    versions = get_theory_version_registry()
    unique_versions = set(v for v in versions.values() if v != "unknown")
    if len(unique_versions) > 1:
        recommendations.append("• Version inconsistency detected. Consider running update_all_theory_versions() to standardize versions.")
    
    # Check for missing data
    missing_versions = [t for t, s in verify_output.items() if not s['version']['found']]
    missing_mc_versions = [t for t, s in verify_output.items() if not s['version']['model_checker_version_found']]
    missing_licenses = [t for t, s in verify_output.items() if not s['license']['found']]
    missing_citations = [t for t, s in verify_output.items() if not s['citation']['found']]
    
    if missing_versions:
        recommendations.append(f"• Missing version information for: {', '.join(missing_versions)}")
    
    if missing_mc_versions:
        recommendations.append(f"• Missing model_checker_version information for: {', '.join(missing_mc_versions)}")
    
    if missing_licenses:
        recommendations.append(f"• Missing license files for: {', '.join(missing_licenses)}")
    
    if missing_citations:
        recommendations.append(f"• Missing citation files for: {', '.join(missing_citations)}")
    
    # Print recommendations
    if recommendations:
        for rec in recommendations:
            print(rec)
    else:
        print("✓ All metadata is consistent and complete.")
    
    print("\n--- How to Update ---\n")
    print("To update all theory versions:")
    print("  from model_checker.theory_lib.meta_data import update_all_theory_versions")
    print("  update_all_theory_versions('1.0.0')")
    print("\nTo create missing license files:")
    print("  from model_checker.theory_lib.meta_data import create_all_license_files")
    print("  create_all_license_files('GPL-3.0', {'name': 'Author Name'})")
    print("\nTo create missing citation files:")
    print("  from model_checker.theory_lib.meta_data import create_all_citation_files")
    print("  create_all_citation_files({'name': 'Author Name'})")
    print("")

if __name__ == "__main__":
    print_metadata_report()