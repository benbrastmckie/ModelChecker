# ModelChecker Licensing and Versioning System

This document provides comprehensive information about the licensing and versioning system used in the ModelChecker project, specifically for theories in the theory library.

## Licensing System

The ModelChecker project, including all theories in the theory library, uses the GNU General Public License v3.0 (GPL-3.0). This license was chosen to ensure:

1. **Open Source**: All code remains free and open
2. **Copyleft Protection**: Derivative works must also be open source
3. **Academic Freedom**: Research can be freely shared while ensuring attribution
4. **Collective Advancement**: The community can build upon and improve theories

### License Structure

The licensing system has a two-tiered structure:

1. **Core Package License**: The main ModelChecker framework is licensed under GPL-3.0
2. **Theory-Specific Licenses**: Each theory in the theory library has its own GPL-3.0 license file

### Theory License Files

Each theory directory contains two important files:

- **LICENSE.md**: Contains the GPL-3.0 license text, copyright notice, and specific terms
- **CITATION.md**: Contains academic attribution information and citation requirements

### License Compliance for Theory Authors

When contributing a new theory to the ModelChecker framework:

1. Your theory must be compatible with GPL-3.0 licensing
2. You retain copyright for your specific implementation
3. By contributing, you agree to license your theory under GPL-3.0
4. Your academic contribution will be properly attributed in CITATION.md

### License File Generation

The BuildProject system automatically creates license files for new theories:

```python
# Creating a new theory project
from model_checker import BuildProject
project = BuildProject("default")
project_dir = project.generate("my_theory")
```

This automatically creates:
- LICENSE.md with GPL-3.0 license text
- CITATION.md with attribution template

## Versioning System

The ModelChecker project uses a dual-versioning system:

1. **Core Package Version**: Tracks the main ModelChecker framework version
2. **Theory-Specific Version**: Each theory has its own version

### Version Attributes

In each theory's `__init__.py` file, you'll find:

```python
__version__ = "1.0.0"  # Theory version
__model_checker_version__ = "0.9.20"  # Compatible ModelChecker version
```

These attributes enable:
- Tracking theory development independently
- Checking compatibility between theories and the core package
- Facilitating updates and migrations

### Versioning Utilities

The ModelChecker provides utilities for managing versions:

```python
# Get the core package version
from model_checker.utils import get_model_checker_version
version = get_model_checker_version()

# Get a specific theory's version
from model_checker.utils import get_theory_version
theory_version = get_theory_version("default")

# Check compatibility
from model_checker.utils import check_theory_compatibility
is_compatible = check_theory_compatibility("default")
```

### Managing Theory Versions

The `meta_data.py` module provides tools for managing theory versions:

```python
# Update all theory versions
from model_checker.theory_lib.meta_data import update_all_theory_versions
update_all_theory_versions("1.0.0")

# Verify metadata consistency
from model_checker.theory_lib.meta_data import verify_metadata_consistency
metadata = verify_metadata_consistency()
```

## Academic Attribution

While the code is licensed under GPL-3.0, academic attribution is handled through:

1. **CITATION.md**: Contains proper citation information
2. **README.md**: Credits theory authors and references relevant papers
3. **Theory Documentation**: Includes links to papers and academic resources

## Management Tools

The ModelChecker provides tools for managing licensing and versioning:

```python
# Test script for metadata management
python test_meta_data.py --report
```

This displays comprehensive information about versioning and licensing across all theories.

## Additional Resources

- [GNU GPL-3.0 License](https://www.gnu.org/licenses/gpl-3.0.en.html)
- [Open Source Licensing Guide](https://opensource.org/licenses)
- [Software Package Data Exchange (SPDX)](https://spdx.org/licenses/GPL-3.0-only.html)