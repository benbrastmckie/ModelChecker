"""Model checker theory library.

This module provides access to various logical theories implementing programmatic 
semantics for modal, counterfactual, and hyperintensional operators. Theories are
loaded on-demand through lazy loading for better performance.

Each theory implements:
- Semantic model structures with state fusion, part-hood relations, etc.
- Logical operators with specific verification and falsification conditions
- Proposition evaluation within the semantic framework
- Example models demonstrating the theory's principles

Available Theories:
- logos: Standard bilateral truthmaker semantics with modular subtheories
- exclusion: Unilateral semantics with exclusion relations 
- imposition: Semantics with imposition relations
- bimodal: Bimodal semantics for counterfactuals and imposition (experimental)

The module supports theory extension through a central registry. To add a new theory:
1. Create a new directory under theory_lib/
2. Implement semantic.py, operators.py, and examples.py
3. Add test cases in a test/ subdirectory
4. Register the theory name in AVAILABLE_THEORIES

Usage Examples:
    # Import a specific theory
    from model_checker.theory_lib import logos
    
    # Get a theory configuration
    theory = logos.get_theory()
    
    # Access examples from a theory
    from model_checker.theory_lib import get_examples
    examples = get_examples('logos')
    cf_theorem = examples['CF_TH_1']  # Counterfactual theorem
    
    # Use with model checking via examples.py files
    # See the Examples Standard documentation for the recommended workflow
    
    # Get test examples for unit testing
    from model_checker.theory_lib import get_test_examples
    test_examples = get_test_examples('logos')
    
    # Discover all available theories
    from model_checker.theory_lib import discover_theories
    all_theories = discover_theories()
"""

import datetime
import importlib
import os
from typing import Dict, List, Optional, Any

from model_checker.theory_lib import logos

from ..utils import get_license_template







# Registry of available theories - add new theories here
AVAILABLE_THEORIES = [
    'logos',        # Standard bilateral truthmaker semantics with modular subtheories
    'exclusion',    # Unilateral semantics with exclusion relations
    'imposition',   # Semantics with imposition relations
    'bimodal',      # Bimodal semantics
]

# Dictionary to cache loaded theory modules
_theory_modules = {}

# Dictionary to cache theory versions
_theory_versions = {}

# Dictionary to cache theory license information
_theory_licenses = {}

def get_examples(theory_name: str) -> Dict[str, Any]:
    """Access example model configurations from a specific theory.

    Each theory provides a set of examples that demonstrate its logical principles.
    These examples are used for demonstration and model checking.

    Args:
        theory_name: Name of the registered theory ('default', 'exclusion', etc.)

    Returns:
        Dictionary mapping example names to (premises, conclusions, settings) tuples

    Raises:
        ValueError: If the theory is not registered or examples cannot be loaded

    Example:
        >>> from model_checker.theory_lib import get_examples
        >>> logos_examples = get_examples('logos')
        >>> print(list(logos_examples.keys())[:5])
        ['EXT_TH_1', 'EXT_TH_2', 'EXT_TH_3', 'EXT_TH_4', 'EXT_TH_5']
    """
    if theory_name not in AVAILABLE_THEORIES:
        raise ValueError(f"Unknown theory: {theory_name}")
    
    try:
        module = importlib.import_module(f".{theory_name}.examples", package=__name__)
        return module.example_range
    except (ImportError, AttributeError) as e:
        raise ValueError(f"Could not load examples for theory '{theory_name}': {str(e)}")

def get_test_examples(theory_name: str) -> Dict[str, Any]:
    """Access test examples from a specific theory for unit testing.

    These examples include test cases with expected results for automated testing.
    Each example typically includes premises, conclusions, settings, and expected outcome.

    Args:
        theory_name: Name of the registered theory ('default', 'exclusion', etc.)

    Returns:
        Dictionary mapping test names to (premises, conclusions, settings) tuples

    Raises:
        ValueError: If the theory is not registered or test examples cannot be loaded

    Example:
        >>> from model_checker.theory_lib import get_test_examples
        >>> tests = get_test_examples('logos')
        >>> # Use with pytest parametrization
        >>> @pytest.mark.parametrize("example_name, example_case", tests.items())
        >>> def test_examples(example_name, example_case):
        >>>     # Test implementation
    """
    if theory_name not in AVAILABLE_THEORIES:
        raise ValueError(f"Unknown theory: {theory_name}")
    
    try:
        module = importlib.import_module(f".{theory_name}.examples", package=__name__)
        return module.test_example_range
    except (ImportError, AttributeError) as e:
        raise ValueError(f"Could not load test examples for theory '{theory_name}': {str(e)}")

def get_semantic_theories(theory_name: str) -> Dict[str, Any]:
    """Access semantic theory implementations from a specific theory.

    This function returns the semantic theory implementations that define
    the logical behavior of each theory variant.

    Args:
        theory_name: Name of the registered theory ('default', 'exclusion', etc.)

    Returns:
        Dictionary mapping semantic theory names to their implementation classes

    Raises:
        ValueError: If the theory is not registered or semantic theories cannot be loaded

    Example:
        >>> from model_checker.theory_lib import get_semantic_theories
        >>> semantics = get_semantic_theories('logos')
        >>> # The logos theory uses a modular architecture
        >>> # with semantic theories loaded from subtheories
    """
    if theory_name not in AVAILABLE_THEORIES:
        raise ValueError(f"Unknown theory: {theory_name}")
    
    try:
        module = importlib.import_module(f".{theory_name}.examples", package=__name__)
        return module.semantic_theories
    except (ImportError, AttributeError) as e:
        raise ValueError(f"Could not load semantic theories for theory '{theory_name}': {str(e)}")

def discover_theories() -> List[str]:
    """Discover available theories by scanning the directory structure.

    Identifies directories that have the required files to be considered a theory
    implementation (examples.py and operators.py). Used primarily for development
    to find unregistered theories.

    Returns:
        Alphabetically sorted list of discovered theory names

    Example:
        >>> from model_checker.theory_lib import discover_theories, AVAILABLE_THEORIES
        >>> discovered = discover_theories()
        >>> unregistered = [t for t in discovered if t not in AVAILABLE_THEORIES]
        >>> print(f"Unregistered theories found: {unregistered}")
    """
    current_dir = os.path.dirname(os.path.abspath(__file__))
    theories = []
    
    # Find directories containing both examples.py and operators.py
    for item in os.listdir(current_dir):
        if os.path.isdir(os.path.join(current_dir, item)) and not item.startswith('__'):
            examples_path = os.path.join(current_dir, item, 'examples.py')
            operators_path = os.path.join(current_dir, item, 'operators.py')
            if os.path.exists(examples_path) and os.path.exists(operators_path):
                theories.append(item)
    
    return sorted(theories)

# Version and License utility functions
def get_theory_version_registry() -> Dict[str, str]:
    """Get a dictionary of all theory versions.

    Returns:
        Dictionary mapping theory names to their versions
    """
    versions = {}
    for theory_name in AVAILABLE_THEORIES:
        try:
            if theory_name in _theory_versions:
                versions[theory_name] = _theory_versions[theory_name]
            else:
                # Try to import the theory if not already in registry
                theory_module = importlib.import_module(f".{theory_name}", package=__name__)
                version = getattr(theory_module, "__version__", "unknown")
                _theory_versions[theory_name] = version
                versions[theory_name] = version
        except ImportError:
            versions[theory_name] = "unknown"
    
    return versions

def get_theory_license_info(theory_name: str) -> Dict[str, Any]:
    """Get license information for a specific theory.

    Args:
        theory_name: Name of the registered theory

    Returns:
        Dictionary containing license information

    Raises:
        ValueError: If the theory is not registered
    """
    if theory_name not in AVAILABLE_THEORIES:
        raise ValueError(f"Unknown theory: {theory_name}")
    
    # Return from cache if available
    if theory_name in _theory_licenses:
        return _theory_licenses[theory_name]
    
    # Try to load license information
    try:
        # Check if the theory has a LICENSE.md file
        theory_dir = os.path.dirname(os.path.abspath(__file__))
        license_path = os.path.join(theory_dir, theory_name, "LICENSE.md")
        
        license_info = {
            "type": "Unknown",
            "text": "No license information available",
            "path": None
        }
        
        if os.path.exists(license_path):
            with open(license_path, 'r', encoding='utf-8') as f:
                license_text = f.read()
                
            # Try to determine license type from content
            license_type = "Unknown"
            if "GNU GENERAL PUBLIC LICENSE" in license_text:
                license_type = "GPL-3.0"
            elif "MIT License" in license_text:
                license_type = "MIT"
                
            license_info = {
                "type": license_type,
                "text": license_text,
                "path": license_path
            }
        
        # Cache the result
        _theory_licenses[theory_name] = license_info
        return license_info
    except Exception as e:
        # In case of any error, return a default
        return {
            "type": "Unknown",
            "text": f"Failed to load license information: {str(e)}",
            "path": None
        }

def create_license_file(theory_name: str, license_type: str = "GPL-3.0", author_info: Optional[Dict[str, Any]] = None) -> bool:
    """Create a license file for a theory.

    Args:
        theory_name: Name of the registered theory
        license_type: Type of license (GPL-3.0, MIT, etc.)
        author_info: Author information (name, email, year)

    Returns:
        True if license was created successfully, False otherwise

    Raises:
        ValueError: If the theory is not registered
    """
    if theory_name not in AVAILABLE_THEORIES:
        raise ValueError(f"Unknown theory: {theory_name}")
    
    try:
        # Get theory directory
        theory_dir = os.path.dirname(os.path.abspath(__file__))
        license_path = os.path.join(theory_dir, theory_name, "LICENSE.md")
        
        # Get license template
        license_text = get_license_template(license_type, author_info)
        
        # Write license file
        with open(license_path, 'w', encoding='utf-8') as f:
            f.write(license_text)
        
        # Update cache
        _theory_licenses[theory_name] = {
            "type": license_type,
            "text": license_text,
            "path": license_path
        }
        
        return True
    except Exception as e:
        print(f"Failed to create license file: {str(e)}")
        return False

def create_citation_file(theory_name: str, citation_text: str) -> bool:
    """Create a citation file for a theory.

    Args:
        theory_name: Name of the registered theory
        citation_text: Citation text in markdown format

    Returns:
        True if citation was created successfully, False otherwise

    Raises:
        ValueError: If the theory is not registered
    """
    if theory_name not in AVAILABLE_THEORIES:
        raise ValueError(f"Unknown theory: {theory_name}")
    
    try:
        # Get theory directory
        theory_dir = os.path.dirname(os.path.abspath(__file__))
        citation_path = os.path.join(theory_dir, theory_name, "CITATION.md")
        
        # Write citation file
        with open(citation_path, 'w', encoding='utf-8') as f:
            f.write(citation_text)
        
        return True
    except Exception as e:
        print(f"Failed to create citation file: {str(e)}")
        return False

# Public API
__all__ = [
    'AVAILABLE_THEORIES',
    'get_examples',
    'get_test_examples',
    'get_semantic_theories',
    'discover_theories',
    'get_theory_version_registry',
    'get_theory_license_info',
    'create_license_file',
    'create_citation_file',
]

# Lazy loading implementation via __getattr__

def __getattr__(name: str) -> Any:
    """Lazily load theory modules when accessed.

    This special method implements Python's attribute lookup protocol.
    When a module attribute is requested that doesn't exist in globals(),
    Python calls this method to resolve it.

    Args:
        name: Name of the requested attribute

    Returns:
        The imported theory module if the name matches a registered theory

    Raises:
        AttributeError: If the name is not a registered theory

    Example:
        # This triggers __getattr__('logos')
    """
    if name in AVAILABLE_THEORIES:
        # Load and cache the module if not already loaded
        if name not in _theory_modules:
            try:
                module = importlib.import_module(f".{name}", package=__name__)
                _theory_modules[name] = module
            except ImportError as e:
                raise AttributeError(f"Failed to import theory '{name}': {str(e)}")
        return _theory_modules[name]
    
    raise AttributeError(f"module '{__name__}' has no attribute '{name}'")
