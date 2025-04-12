"""Model checker builder components for constructing and executing modal logic examples.

This package provides components for building and executing modal logic model checking 
examples. It replaces the monolithic builder.py with a more modular approach.

Main Components:
    BuildModule: Manages loading and executing model checking examples from Python modules.
    BuildProject: Creates new theory implementation projects from templates.
    BuildExample: Handles individual model checking examples.

The package follows the project's design philosophy:
- Fail Fast: Let errors occur naturally rather than adding conditional logic
- Required Parameters: Parameters are explicitly required with no implicit conversions
- Clear Data Flow: Maintain a consistent approach to passing data between components
- No Silent Failures: Don't catch exceptions or provide defaults just to avoid errors
"""

__all__ = ['BuildModule', 'BuildProject', 'BuildExample']

# Import for backward compatibility during transition
from model_checker.builder.module import BuildModule
from model_checker.builder.project import BuildProject
from model_checker.builder.example import BuildExample
