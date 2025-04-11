"""Settings management module for ModelChecker.

This module provides centralized settings management for the ModelChecker framework,
including validation, merging, and overriding of settings from different sources.
"""

from .settings import SettingsManager, DEFAULT_GENERAL_SETTINGS

__all__ = ['SettingsManager', 'DEFAULT_GENERAL_SETTINGS']