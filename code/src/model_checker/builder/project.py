"""BuildProject implementation for creating new theory projects.

This module provides the BuildProject class for creating new theory implementation 
projects from templates. It handles directory structure creation, file copying, 
and initial setup of new modal logic theory implementations.

Each new theory created includes:
- Version information (theory-specific and model-checker version compatibility)
- License files (GPL-3.0 by default)
- Citation templates for academic attribution
- Standard theory implementation structure

The BuildProject ensures all new theories adhere to the project's licensing
and code structure requirements automatically.
"""

import os
import sys
import shutil
import subprocess
from typing import Union, Optional, List, Tuple, Dict, Any
from pathlib import Path
from datetime import datetime

# Explicit copy manifest for theory project scaffolding.
#
# Enumerates the canonical theory file set from
# theory_lib/docs/THEORY_ARCHITECTURE.md's Theory Contract, so scaffolded projects only ever
# receive intentional, contract-conforming items -- never accumulated cruft (history/, reports/,
# examples_refactored/, TODO.md, etc.) that happens to be sitting in a theory's source directory.
#
# REQUIRED items must exist in the source theory directory; a missing required item is a
# fail-fast error (the theory itself is non-conforming, not something scaffolding should paper
# over). OPTIONAL items are copied if present and silently skipped otherwise. Items not on
# either list are skipped with a warning log line rather than copied.
#
# `semantic.py` and `semantic/` are both accepted. All four in-tree theories (bimodal, exclusion,
# imposition, logos) are now normalized onto THEORY_ARCHITECTURE.md's contractual `semantic/`
# package form (core.py/model.py/proposition.py, or bimodal's core.py alone) -- the flat
# `semantic.py` alternative remains accepted here only so a hand-authored or third-party theory
# project may still use a single-file layout without failing scaffolding. At least one of the two
# forms must be present; having both is valid, not an error.
REQUIRED_COPY_ITEMS = [
    '__init__.py',
    'operators.py',
    'examples.py',
    'tests',
    'docs',
    'README.md',
    'CITATION.md',
    'LICENSE.md',
    'VERSION',
]

# At least one must be present (see comment above); both may be present together.
SEMANTIC_ALTERNATIVES = ['semantic', 'semantic.py']

# Present in some theories, valid, but not required by every theory.
OPTIONAL_COPY_ITEMS = [
    # `iterate.py` is REQUIRED by THEORY_ARCHITECTURE.md's Theory Contract -- every theory's
    # DEFAULT_EXAMPLE_SETTINGS declares an `iterate` setting, so a theory lacking it has a live,
    # reachable ImportError under `iterate: 2`. It is listed here rather than in
    # REQUIRED_COPY_ITEMS only because bimodal does not yet have one (a known, tracked contract
    # gap; the theory-conformance test flags it with a narrowly-scoped xfail rather than this
    # scaffolding step hard-failing bimodal project generation). Copied when present; its
    # absence for a given theory is a conformance defect to fix in that theory (tracked by
    # `test_theory_conformance.py`), not something this scaffolding step should hard-fail on.
    'iterate.py',
    'notebooks',       # Jupyter demonstrations (exclusion, imposition)
    'protocols.py',    # logos-specific protocol definitions
    'subtheories',     # logos-specific subtheory packages
]

# Directories skipped even when copying an allowed directory item (build/cache artifacts, never
# intentional content).
COPY_IGNORE_PATTERNS = ['__pycache__', '.ipynb_checkpoints']


class BuildProject:
    """Creates a new theory implementation project from templates.
    
    This class handles the creation of a new modal logic theory implementation
    by copying and configuring template files. It sets up the directory structure
    and initializes the basic implementation files.
    
    Attributes:
        theory (str): Name of the source theory to use as template
        source_dir (str): Directory path to the source theory
        project_name (str): Name of the new project (will be prefixed with 'project_')
        destination_dir (str): Directory path for the new project
        log_messages (list): Log of actions and messages during project generation
    """

    # No longer enforcing essential files to allow for flexible project structures

    def __init__(self, theory: Optional[str] = None, subtheories: Optional[List[str]] = None) -> None:
        """Initialize project builder with specified theory.

        Args:
            theory: Name of the source theory to use as template. Defaults to the first
                registered theory (see `model_checker.registry`) rather than a hardcoded
                name, so this core module names no theory as a string literal (see
                docs/THEORY_ARCHITECTURE.md's Layering section).
            subtheories: List of subtheories to load (unused, kept for API compatibility)

        Raises:
            FileNotFoundError: If the source theory directory doesn't exist
            ValueError: If `theory` is None and no theory is registered yet
        """
        if theory is None:
            from .. import registry
            registered = registry.get_registered()
            if not registered:
                raise ValueError(
                    "No theory specified and no theory is registered yet; pass an "
                    "explicit theory name"
                )
            theory = registered[0]
        self.theory: str = theory
        self.subtheories: Optional[List[str]] = subtheories
        self.source_dir: str = os.path.join(os.path.dirname(os.path.dirname(__file__)), 'theory_lib', theory)
        self.project_name: str = ""
        self.destination_dir: str = ""
        self.log_messages: List[Tuple[str, str]] = []

        # Validate source directory exists
        if not os.path.exists(self.source_dir):
            raise FileNotFoundError(
                f"The semantic theory '{self.theory}' was not found at '{self.source_dir}'."
            )
    
    def log(self, message: str, level: str = "INFO") -> None:
        """Log a message with a specified level.
        
        Args:
            message (str): The message to log
            level (str): The log level (INFO, WARNING, ERROR)
        """
        self.log_messages.append(f"[{level}] {message}")
        # Only print error and warning messages immediately
        if level == "ERROR":
            print(f"Error: {message}")
        elif level == "WARNING":
            print(f"Warning: {message}")
    
    def ask_generate(self) -> bool:
        """Prompt user to create a new theory implementation project.

        Asks the user if they want to generate a new project for the current theory.
        If yes, prompts for a project name and calls generate(). If no, displays
        information about running existing example files.
        """
        result = input(f"Would you like to generate a new {self.theory}-project? (y/n): ")
        if result.lower() not in {'yes', 'ye', 'y'}:
            print("\nYou can run an example.py file that already exists with the command:\n")
            print("  $ model-checker example.py\n")
            return
        
        test_name = input("Enter the name of your project using snake_case: ")
        if not test_name:
            print("Project name cannot be empty.")
            return
            
        try:
            project_dir = self.generate(test_name)
            self._print_success_message(project_dir)
            self._handle_example_script(project_dir)
        except Exception as e:
            print(f"Error creating project: {e}")
        
    def generate(self, name: str, destination_dir: Optional[str] = None) -> None:
        """Generate a new theory implementation project from templates.
        
        Args:
            name: Name for the new project
            destination_dir: Target directory (defaults to current directory)
            
        Returns:
            str: Path to the created project
            
        Raises:
            ValueError: If project name is invalid
            FileExistsError: If project directory already exists
            FileNotFoundError: If source theory not found
        """
        if not name:
            raise ValueError("Project name cannot be empty")
            
        # Create project path
        self.project_name = f"project_{name}"
        
        # Use current directory if no destination specified
        if destination_dir is None:
            destination_dir = os.getcwd()
            
        self.destination_dir = os.path.join(destination_dir, self.project_name)
        
        # Verify destination doesn't exist
        if os.path.exists(self.destination_dir):
            raise FileExistsError(f"Directory '{self.destination_dir}' already exists.")
            
        # Create the project directory and collect files that were copied
        os.makedirs(self.destination_dir)
        
        try:
            # Copy files from source to destination, without printing progress
            self._copy_files(self.destination_dir)
            
            # Customize project files
            self._update_file_contents(self.destination_dir)
            
            # No longer verifying essential files
            # Simply return the created directory
            return self.destination_dir
            
        except Exception as e:
            # Clean up on failure
            if os.path.exists(self.destination_dir):
                shutil.rmtree(self.destination_dir)
            raise
    
    def _copy_files(self, project_dir: str) -> None:
        """Copy all files and transform into a package.

        Uses the explicit copy manifest (REQUIRED_COPY_ITEMS / SEMANTIC_ALTERNATIVES /
        OPTIONAL_COPY_ITEMS module-level constants) rather than a verbatim directory copy, so
        only canonical theory-contract items are ever scaffolded into a new project -- stray
        cruft sitting alongside a theory's source (history/, reports/, TODO.md, and similar) is
        never copied, even if it is reintroduced into the source tree later.

        Args:
            project_dir: Path to the destination project directory

        Raises:
            FileNotFoundError: If source files don't exist
            PermissionError: If files can't be written
        """
        # 1. Copy files as before (fail-fast on errors)
        if not os.path.exists(self.source_dir):
            raise FileNotFoundError(
                f"Source theory directory not found: {self.source_dir}"
            )

        available = set(os.listdir(self.source_dir))

        # Resolve which semantic implementation form(s) are present. At least one is required;
        # both `semantic.py` and `semantic/` may legitimately coexist (see SEMANTIC_ALTERNATIVES
        # comment above -- this is bimodal's deliberate pickling-compatibility shim, not drift).
        semantic_present = [item for item in SEMANTIC_ALTERNATIVES if item in available]
        if len(semantic_present) == 0:
            raise FileNotFoundError(
                f"Theory '{self.theory}' is missing a semantic implementation: expected at "
                f"least one of {SEMANTIC_ALTERNATIVES} in {self.source_dir}"
            )

        # Fail-fast: every required item (other than the semantic alternative, already checked
        # above) must be present in the source theory directory.
        missing_required = [
            item for item in REQUIRED_COPY_ITEMS if item not in available
        ]
        if missing_required:
            raise FileNotFoundError(
                f"Theory '{self.theory}' is missing required item(s) {missing_required} in "
                f"{self.source_dir}; scaffolding requires a contract-conforming theory "
                f"(see theory_lib/docs/THEORY_ARCHITECTURE.md)"
            )

        allowed_items = set(REQUIRED_COPY_ITEMS) | set(semantic_present) | set(OPTIONAL_COPY_ITEMS)

        # Copy only manifest-allowed items from source to destination
        for item in sorted(available):
            if item not in allowed_items:
                self.log(f"Skipped non-manifest item: {item}", "WARNING")
                continue

            source_item = os.path.join(self.source_dir, item)
            dest_item = os.path.join(project_dir, item)

            try:
                if os.path.isdir(source_item):
                    # Copy directories recursively, ignoring build/cache artifacts
                    shutil.copytree(
                        source_item,
                        dest_item,
                        ignore=shutil.ignore_patterns(*COPY_IGNORE_PATTERNS)
                    )
                    self.log(f"Copied directory: {item}")
                else:
                    # Copy files
                    shutil.copy2(source_item, dest_item)
                    self.log(f"Copied file: {item}")
            except Exception as e:
                self.log(f"Error copying {item}: {str(e)}", "ERROR")

        # 2. Create package marker file (fail-fast philosophy)
        self._create_package_marker(project_dir)
        
        # 3. Ensure __init__.py exists with proper exports
        self._ensure_package_structure(project_dir)
        
        # 4. Ensure subtheories are also packages
        self._ensure_subpackages(project_dir)
    
    def _create_package_marker(self, project_dir: str) -> None:
        """Create .modelchecker marker file to identify generated packages.
        
        Args:
            project_dir: Path to the project directory
            
        Raises:
            PermissionError: If marker file can't be created
        """
        marker_path = os.path.join(project_dir, '.modelchecker')
        try:
            with open(marker_path, 'w') as f:
                f.write(f"# ModelChecker Generated Project Marker\n")
                f.write(f"theory={self.theory}\n")
                f.write(f"package=true\n")
                f.write(f"version=1.0\n")
                f.write(f"created={datetime.now().isoformat()}\n")
                f.write(f"model_checker_version={self._get_current_version()}\n")
            self.log(f"Created package marker: .modelchecker")
        except IOError as e:
            raise PermissionError(
                f"Cannot create marker file at {marker_path}: {str(e)}"
            )
    
    def _ensure_package_structure(self, project_dir: str) -> None:
        """Ensure __init__.py exists with proper package exports.
        
        Args:
            project_dir: Path to the project directory
        """
        init_path = os.path.join(project_dir, '__init__.py')
        if not os.path.exists(init_path):
            # Copy from theory if exists, otherwise create new
            theory_init = os.path.join(self.source_dir, '__init__.py')
            if os.path.exists(theory_init):
                shutil.copy2(theory_init, init_path)
                self.log(f"Copied __init__.py from theory")
            else:
                self._create_default_init(init_path)
        else:
            self.log(f"Package __init__.py already exists")
    
    def _create_default_init(self, init_path: str) -> None:
        """Create a default __init__.py for the package.
        
        Args:
            init_path: Path to the __init__.py file to create
        """
        with open(init_path, 'w') as f:
            f.write(f'"""Generated {self.theory} theory package."""\n\n')
            f.write(f'__version__ = "0.1.0"\n')
            f.write(f'__theory__ = "{self.theory}"\n\n')
            f.write(f'# Re-export main components\n')
            f.write(f'try:\n')
            f.write(f'    from .semantic import *\n')
            f.write(f'except ImportError:\n')
            f.write(f'    pass  # semantic.py not present\n')
            f.write(f'try:\n')
            f.write(f'    from .operators import *\n')
            f.write(f'except ImportError:\n')
            f.write(f'    pass  # operators.py not present\n')
        self.log(f"Created default __init__.py")
    
    def _ensure_subpackages(self, project_dir: str) -> None:
        """Ensure all subdirectories with .py files are packages.
        
        Args:
            project_dir: Path to the project directory
        """
        for root, dirs, files in os.walk(project_dir):
            # Skip hidden directories and __pycache__
            dirs[:] = [d for d in dirs if not d.startswith('.') and d != '__pycache__']
            
            # If directory contains .py files, ensure it has __init__.py
            if any(f.endswith('.py') for f in files) and root != project_dir:
                init_path = os.path.join(root, '__init__.py')
                if not os.path.exists(init_path):
                    # Create minimal __init__.py
                    with open(init_path, 'w') as f:
                        subpackage_name = os.path.basename(root)
                        f.write(f'"""Subpackage: {subpackage_name}"""\n')
                    self.log(f"Created subpackage __init__.py in {os.path.relpath(root, project_dir)}")
    
    def _update_file_contents(self, project_dir: str) -> None:
        """Update file contents with project-specific information.
        
        Args:
            project_dir: Path to the project directory
            
        Raises:
            FileNotFoundError: If files to update don't exist
            PermissionError: If files can't be modified
        """
        # Update __init__.py with current version
        init_path = os.path.join(project_dir, "__init__.py")
        if os.path.exists(init_path):
            with open(init_path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            # Get core package version and add theory version
            model_checker_version = self._get_current_version()
            theory_version = "0.1.0"  # Initial version for all new theories
            
            # Update the content with both versions
            new_content = self._update_version_info(content, model_checker_version, theory_version)
            
            with open(init_path, 'w', encoding='utf-8') as f:
                f.write(new_content)
        
        # Add LICENSE.md file if it doesn't exist
        self._add_license_file(project_dir)
        
        # Add CITATION.md file if it doesn't exist
        self._add_citation_file(project_dir)
    
    def _update_version_info(self, content: str, model_checker_version: str, theory_version: str) -> str:
        """Update version information in content.
        
        Args:
            content (str): The file content to update
            model_checker_version (str): Current model_checker version
            theory_version (str): Initial theory version
            
        Returns:
            str: Updated content with version information
        """
        import re
        
        # Update model_checker_version
        mc_version_pattern = re.compile(
            r'__model_checker_version__\s*=\s*["\'].*?["\']'
        )
        
        # Try to replace existing model_checker_version
        mc_replaced = False
        if '__model_checker_version__' in content:
            content = mc_version_pattern.sub(
                f'__model_checker_version__ = "{model_checker_version}"', 
                content
            )
            mc_replaced = True
        
        # Update theory version
        version_pattern = re.compile(r'__version__\s*=\s*["\'].*?["\']')
        
        # Try to replace existing version
        version_replaced = False
        if '__version__' in content:
            content = version_pattern.sub(f'__version__ = "{theory_version}"', content)
            version_replaced = True
        
        # If neither was found, we need to add them
        if not mc_replaced or not version_replaced:
            # Add import for get_model_checker_version
            if 'from model_checker.utils import get_model_checker_version' not in content:
                import_pattern = re.compile(r'(from[\s\S]*?\n\n|import[\s\S]*?\n\n)')
                content = import_pattern.sub(
                    r'\1# Import version utilities\nfrom model_checker.utils import get_model_checker_version\n\n',
                    content
                )
            
            # Look for a good place to add version information
            # Try before __all__ list
            all_pattern = re.compile(r'__all__\s*=\s*\[')
            if all_pattern.search(content):
                # Add version info before __all__
                version_block = f"\n# Version information\n__version__ = \"{theory_version}\"  # Theory version\n__model_checker_version__ = \"{model_checker_version}\"  # ModelChecker version this was built with\n\n"
                content = all_pattern.sub(version_block + "__all__ = [", content)
                
                # Also update the __all__ list to include version attributes
                all_content_pattern = re.compile(r'__all__\s*=\s*\[([\s\S]*?)\]')
                all_content_match = all_content_pattern.search(content)
                if all_content_match:
                    all_items = all_content_match.group(1)
                    if '"__version__"' not in all_items and "'__version__'" not in all_items:
                        # Add version attributes to __all__
                        updated_all = all_items.rstrip() + ',\n    "__version__",                # Theory version information\n    "__model_checker_version__",  # Compatible ModelChecker version\n'
                        content = all_content_pattern.sub(f"__all__ = [{updated_all}]", content)
            else:
                # Just append to the end
                content += f"\n# Version information\n__version__ = \"{theory_version}\"\n__model_checker_version__ = \"{model_checker_version}\"\n"
        
        return content
    
    def _add_license_file(self, project_dir: str) -> None:
        """Add a license file to the project if it doesn't exist.
        
        If the source theory has a LICENSE.md file, this will create an inherited
        license that maintains attribution to the original author while allowing
        the user to add their own copyright for novel contributions.
        
        Args:
            project_dir (str): Path to the project directory
        """
        license_path = os.path.join(project_dir, "LICENSE.md")
        if not os.path.exists(license_path):
            try:
                # Import the license template function
                from model_checker.utils import get_license_template
                
                # Check if source theory has a LICENSE.md file
                source_license_path = os.path.join(self.source_dir, "LICENSE.md")
                source_theory_info = None
                
                if os.path.exists(source_license_path):
                    # Extract source theory information
                    source_theory_info = self._extract_source_theory_info(source_license_path)
                    source_theory_info['name'] = self.source_theory
                    source_theory_info['license_path'] = source_license_path
                
                # Generate license text with inheritance if applicable
                license_text = get_license_template(
                    "GPL-3.0",
                    source_theory_info=source_theory_info
                )
                
                # Write license file
                with open(license_path, 'w', encoding='utf-8') as f:
                    f.write(license_text)
                
                if source_theory_info:
                    self.log(f"Created LICENSE.md with inheritance from {self.source_theory}")
                else:
                    self.log(f"Created LICENSE.md file")
            except Exception as e:
                self.log(f"Error creating license file: {str(e)}", "WARNING")
    
    def _extract_source_theory_info(self, license_path: str) -> Tuple[str, str, str]:
        """Extract copyright information from source theory's LICENSE.md file.
        
        Args:
            license_path (str): Path to the source LICENSE.md file
            
        Returns:
            dict: Extracted information including author and year
        """
        import re
        
        info = {
            'author': 'Unknown Author',
            'year': '2024'
        }
        
        try:
            with open(license_path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            # Extract copyright information
            # Look for patterns like "Copyright (c) YEAR Author Name"
            copyright_match = re.search(r'Copyright\s*\(c\)\s*(\d{4})\s+(.+?)(?:\n|$)', content)
            if copyright_match:
                info['year'] = copyright_match.group(1)
                info['author'] = copyright_match.group(2).strip()
            
            # Also check for "Software Implementation Copyright" section
            impl_match = re.search(r'Software Implementation Copyright\s*\n+Copyright\s*\(c\)\s*(\d{4})\s+(.+?)(?:\n|$)', content, re.MULTILINE)
            if impl_match:
                info['year'] = impl_match.group(1)
                info['author'] = impl_match.group(2).strip()
                
        except Exception as e:
            self.log(f"Warning: Could not extract source theory info: {e}", "WARNING")
            
        return info
    
    def _add_citation_file(self, project_dir: str) -> None:
        """Add a citation file to the project if it doesn't exist.
        
        Args:
            project_dir (str): Path to the project directory
        """
        citation_path = os.path.join(project_dir, "CITATION.md")
        if not os.path.exists(citation_path):
            try:
                # Get current year
                import datetime
                year = datetime.datetime.now().year
                
                # Generate citation text
                citation_text = f"""# Citation Information

If you use this theory implementation in academic work, please cite:

[Author]. ({year}). [Theory Name]: A semantic theory implementation for the
ModelChecker framework.

## Theory Implementation Notes

This theory implementation is part of the ModelChecker framework.
For more detailed information about the theory's mathematical foundations,
please include additional references here.
"""
                
                # Write citation file
                with open(citation_path, 'w', encoding='utf-8') as f:
                    f.write(citation_text)
                
                self.log(f"Created CITATION.md file")
            except Exception as e:
                self.log(f"Error creating citation file: {str(e)}", "WARNING")
    
    def _get_current_version(self) -> str:
        """Extract the current version from the installed model-checker package.
        
        Returns:
            str: Current version number, or fallback version if not found
        """
        try:
            # First try to use the utility function
            try:
                from model_checker.utils import get_model_checker_version
                return get_model_checker_version()
            except ImportError:
                # Fallback to importlib.metadata
                try:
                    from importlib.metadata import version
                    return version("model-checker")
                except (ImportError, ModuleNotFoundError):
                    # Fallback to package __version__
                    from model_checker import __version__
                    if __version__ != "unknown":
                        return __version__
                    
                    # Final fallback to pyproject.toml
                    current_dir = os.path.dirname(os.path.dirname(os.path.dirname(__file__)))
                    pyproject_path = os.path.join(current_dir, 'pyproject.toml')
                    
                    if os.path.exists(pyproject_path):
                        with open(pyproject_path, 'r', encoding='utf-8') as f:
                            content = f.read()
                            
                        # Find version line
                        for line in content.split('\n'):
                            if line.strip().startswith('version = '):
                                return line.split('=')[1].strip().strip('"\'')
            
            return "unknown"  # Fallback to unknown
            
        except Exception:
            return "unknown"  # Fallback on any error
    
    # The _verify_essential_files method has been removed to allow for more flexible project structures
    
    def _print_success_message(self, project_dir: str) -> None:
        """Print success message with created files as a tree structure.
        
        Args:
            project_dir: Path to the project directory
        """
        print(f"\nProject generated at: {project_dir}\n")
        print("Project structure:")
        
        # Print the project root
        print(f"└── {os.path.basename(project_dir)}/")
        
        # Get all items in the project directory
        all_items = sorted(os.listdir(project_dir))
        files = [item for item in all_items if os.path.isfile(os.path.join(project_dir, item))]
        dirs = [item for item in all_items if os.path.isdir(os.path.join(project_dir, item))]
        
        # Print files first
        for i, file in enumerate(files):
            prefix = "    ├── " if i < len(files) - 1 or dirs else "    └── "
            print(f"{prefix}{file}")
        
        # Then print directories and their contents
        for i, directory in enumerate(dirs):
            dir_prefix = "    ├── " if i < len(dirs) - 1 else "    └── "
            print(f"{dir_prefix}{directory}/")
            
            # Get files in the subdirectory
            subdir_path = os.path.join(project_dir, directory)
            subdir_items = sorted(os.listdir(subdir_path))
            
            # Filter out __pycache__ directories
            subdir_items = [item for item in subdir_items if not item.startswith('__pycache__')]
            
            for j, subitem in enumerate(subdir_items):
                sub_prefix = "    │   ├── " if i < len(dirs) - 1 else "        ├── "
                if j == len(subdir_items) - 1:
                    sub_prefix = "    │   └── " if i < len(dirs) - 1 else "        └── "
                print(f"{sub_prefix}{subitem}")
    
    def _handle_example_script(self, project_dir: str) -> None:
        """Handle running the example script if requested.
        
        Args:
            project_dir: Path to the project directory
        """
        result = input("Would you like to test an example in your project? (y/n): ")
        if result.lower() not in {'yes', 'ye', 'y'}:
            print(f"\nYou can test your project by running:\n\nmodel-checker <path-to-example-file>\n")
            return

        # Check for examples.py or examples/__init__.py
        example_script = os.path.join(project_dir, "examples.py")
        examples_init = os.path.join(project_dir, "examples", "__init__.py")
        
        if os.path.exists(example_script):
            selected_example = example_script
        elif os.path.exists(examples_init):
            selected_example = examples_init
        else:
            print("\nNo examples.py or examples/__init__.py found.")
            print(f"\nYou can test your project by running:\n\nmodel-checker <path-to-example-file>\n")
            return
            
        print(f"\nRunning example: {selected_example}")
        try:
            # Verify package is importable before attempting to run
            parent_dir = os.path.dirname(project_dir)
            package_name = os.path.basename(project_dir)
            
            # Add parent to sys.path if needed (permanent change)
            if parent_dir not in sys.path:
                sys.path.insert(0, parent_dir)
                self.log(f"Added {parent_dir} to sys.path")
            
            # Verify package can be imported
            try:
                __import__(package_name)
                self.log(f"Package '{package_name}' verified as importable")
            except ImportError as e:
                from .errors import PackageNotImportableError
                raise PackageNotImportableError(
                    f"Package '{package_name}' cannot be imported",
                    f"Package location: {project_dir}",
                    f"Parent directory: {parent_dir}",
                    "Ensure package has __init__.py and proper structure",
                    f"Import error: {str(e)}"
                )
            
            # Run with modified PYTHONPATH to ensure package is importable
            # Need to pass sys.path modifications to subprocess
            env = os.environ.copy()
            current_pythonpath = env.get('PYTHONPATH', '')
            if current_pythonpath:
                env['PYTHONPATH'] = f"{parent_dir}{os.pathsep}{current_pythonpath}"
            else:
                env['PYTHONPATH'] = parent_dir
            
            subprocess.run(
                ["model-checker", selected_example], 
                check=True,
                timeout=30,  # Add 30 second timeout
                env=env  # Pass modified environment with PYTHONPATH
            )
        except subprocess.TimeoutExpired:
            print("\nScript execution timed out. You can run it manually with:")
            print(f"model-checker {selected_example}")
        except subprocess.CalledProcessError as e:
            print(f"\nError running example: {e}")
            print(f"You can run it manually with: model-checker {selected_example}")
        except Exception as e:
            print(f"\nUnexpected error: {e}")
            print(f"You can run it manually with: model-checker {selected_example}")
