"""
ModelChecker API Migration Tools

This package provides automated tools for migrating code from the old ModelChecker API
to the new modernized API structure.

Usage:
    # Command line migration
    python -m model_checker.migrate path/to/your/code/
    
    # Programmatic migration
    from model_checker.migrate import migrate_project
    results = migrate_project("path/to/project", backup=True)
"""

from .transformer import APITransformer, transform_code, transform_file
from .config import migrate_settings_dict, SettingsTranslator
from .notebook import migrate_notebook
from .project import migrate_project, validate_migration
from .compatibility import LegacyBuildExample, LegacyResult, SettingsTranslator

__all__ = [
    'APITransformer',
    'transform_code', 
    'transform_file',
    'migrate_settings_dict',
    'SettingsTranslator',
    'migrate_notebook',
    'migrate_project',
    'validate_migration',
    'LegacyBuildExample',
    'LegacyResult'
]

__version__ = "0.1.0"