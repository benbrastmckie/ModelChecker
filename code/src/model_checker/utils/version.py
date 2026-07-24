"""
Version and license functions for the model checker.

This module provides functions for core version management and license generation.
Theory-aware version/compatibility helpers (`get_theory_version`, `check_theory_compatibility`)
live in `theory_lib/meta_data.py` instead -- they import a specific theory module by name,
which makes them a `theory_lib` concern, not a core one (`utils/` must never import
`theory_lib`; see `docs/THEORY_ARCHITECTURE.md`'s Layering section).
"""

import datetime
from importlib.metadata import version
from typing import Dict, Optional, Any


def get_model_checker_version() -> str:
    """Get the current version of the model_checker package.

    Returns:
        str: Version string (e.g., '1.0.0')
    """
    try:
        return version('model-checker')
    except:
        # If package is not installed, return development version
        return "0.0.0-dev"


def get_license_template(
    license_type: str = "GPL-3.0",
    author_info: Optional[Dict[str, Any]] = None,
    source_theory_info: Optional[Dict[str, Any]] = None
) -> str:
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