"""
Version and compatibility functions for the model checker.

This module provides functions for version management, theory compatibility checking,
and license generation.
"""

import datetime
import importlib
from importlib.metadata import version


def get_model_checker_version():
    """Get the current version of the model_checker package.
    
    Returns:
        str: Version string (e.g., '1.0.0')
    """
    try:
        return version('model-checker')
    except:
        # If package is not installed, return development version
        return "0.0.0-dev"


def get_theory_version(theory_name):
    """Get the version of a specific theory implementation.
    
    Args:
        theory_name (str): Name of the theory (e.g., 'logos', 'exclusion')
        
    Returns:
        str: Version string if available, '0.0.0' if not versioned
    """
    try:
        theory_module = importlib.import_module(f"model_checker.theory_lib.{theory_name}")
        return getattr(theory_module, '__version__', '0.0.0')
    except ImportError:
        return '0.0.0'


def check_theory_compatibility(theory_name):
    """Check if a theory is compatible with the current model_checker version.
    
    Args:
        theory_name (str): Name of the theory
        
    Returns:
        bool: True if compatible, False otherwise
        
    Raises:
        ValueError: If theory_name is not a valid registered theory
    """
    try:
        # Import theory_lib
        from model_checker.theory_lib import AVAILABLE_THEORIES
        
        if theory_name not in AVAILABLE_THEORIES:
            raise ValueError(f"Theory '{theory_name}' not found. Available theories: {AVAILABLE_THEORIES}")
        
        # Import the theory module
        theory_module = importlib.import_module(f"model_checker.theory_lib.{theory_name}")
        
        # Check if the theory has model_checker version info
        if hasattr(theory_module, "__model_checker_version__"):
            theory_mc_version = theory_module.__model_checker_version__
            current_mc_version = get_model_checker_version()
            
            # Simple version comparison for now
            # Could be enhanced with more sophisticated version comparison logic
            return theory_mc_version == current_mc_version
        
        # If no version info is available, assume compatible
        return True
    except ImportError:
        # If we can't import the theory, it's not compatible
        return False


def get_license_template(license_type="GPL-3.0", author_info=None, source_theory_info=None):
    """Get license text for a specified license type with inheritance support.
    
    Args:
        license_type (str): Type of license (GPL-3.0, MIT, etc.)
        author_info (dict): New author information (name, email, year)
        source_theory_info (dict): Original theory information for inheritance
            - 'name': Name of the source theory
            - 'author': Original author name
            - 'year': Original copyright year
            - 'license_path': Path to source LICENSE.md file
        
    Returns:
        str: License text with proper attribution and inheritance
    """
    year = datetime.datetime.now().year
    author_name = author_info.get("name", "[Your Name]") if author_info else "[Your Name]"
    
    if source_theory_info:
        # Generate inherited license with proper attribution
        source_name = source_theory_info.get('name', '[Source Theory]')
        source_author = source_theory_info.get('author', '[Original Author]')
        source_year = source_theory_info.get('year', year)
        
        return f"""# License

This theory implementation is a derivative work based on the {source_name} theory.

## Original Theory Copyright

Copyright (c) {source_year} {source_author}

The original {source_name} theory implementation is licensed under GPL-3.0.
This derivative work must maintain the same license terms.

## Derivative Work Copyright

Copyright (c) {year} {author_name}

### Novel Contributions

[Describe your novel contributions here. Examples:
- Extended the theory to handle additional operators
- Implemented new semantic constraints for X
- Added support for Y feature
- Optimized performance for Z cases]

For detailed documentation of changes, see: [Link to your contribution docs]

## License Terms

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program. If not, see <https://www.gnu.org/licenses/>.

## Attribution Requirements

When using or distributing this theory:
1. Maintain attribution to the original {source_name} theory by {source_author}
2. Include this complete license file
3. Document any modifications in the "Novel Contributions" section
4. Provide links to detailed change documentation

## Academic Citation

If you use this theory implementation in academic work, please cite both:
1. The original {source_name} theory (see CITATION.md)
2. Your derivative work if substantial novel contributions were made
"""
    else:
        # Standard license for non-derivative work
        return f"""# License

Copyright (c) {year} {author_name}

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program. If not, see <https://www.gnu.org/licenses/>.
"""