"""Project detection functionality separated from loading.

This module handles ONLY project type detection, following the
Single Responsibility Principle. It does NOT handle module loading.
"""

import os
from enum import Enum
from pathlib import Path
from typing import Optional

from .errors import PackageStructureError, PackageFormatError


class ProjectType(Enum):
    """Type of project detected."""
    PACKAGE = "package"  # Has .modelchecker marker
    STANDARD = "standard"  # Regular Python module


class ProjectDetector:
    """Handle ONLY project detection logic.
    
    This class has a single responsibility: detecting the type of project
    and finding project roots. It does NOT load modules or handle imports.
    
    NO BACKWARDS COMPATIBILITY: This class does not support legacy
    config.py or project.yaml detection. Only .modelchecker markers
    are supported for package detection.
    """
    
    def __init__(self, path: str):
        """Initialize detector with path.

        Args:
            path: Path to project or module

        Raises:
            PackageStructureError: If path does not exist
        """
        # Store the resolved absolute path to ensure consistent detection
        self.path = str(Path(path).resolve())

        # Fail-fast validation
        if not os.path.exists(self.path):
            raise PackageStructureError(
                f"Path does not exist: {self.path}",
                f"Current directory: {os.getcwd()}",
                "Provide valid path to project or module"
            )
    
    def detect_project_type(self) -> ProjectType:
        """Determine project type from markers.
        
        NO LEGACY SUPPORT: Only checks for .modelchecker marker.
        Does not check for config.py or project.yaml.
        
        Returns:
            ProjectType.PACKAGE if .modelchecker marker found
            ProjectType.STANDARD otherwise
        """
        marker_path = self._find_marker()
        if marker_path and self._validate_marker(marker_path):
            return ProjectType.PACKAGE
        return ProjectType.STANDARD
    
    def get_package_root(self) -> Optional[str]:
        """Find package root directory.
        
        BREAKING CHANGE: Only finds root via .modelchecker marker.
        No config.py or other legacy detection.
        
        Returns:
            Path to package root if found, None otherwise
        """
        marker_path = self._find_marker()
        if marker_path:
            return str(Path(marker_path).parent)
        return None
    
    def _find_marker(self) -> Optional[str]:
        """Find .modelchecker marker file.
        
        Searches from the given path up to the root directory.
        
        Returns:
            Path to .modelchecker file if found, None otherwise
        """
        current = Path(self.path)
        
        # If path is a file, start from its directory
        if current.is_file():
            current = current.parent
            
        # Search upward for .modelchecker marker
        while current != current.parent:
            marker_path = current / ".modelchecker"
            if marker_path.exists():
                return str(marker_path)
            current = current.parent
            
        return None
    
    def _validate_marker(self, marker_path: str) -> bool:
        """Validate .modelchecker marker contents.
        
        Args:
            marker_path: Path to .modelchecker file
            
        Returns:
            True if marker is valid, False otherwise
            
        Raises:
            PackageFormatError: If marker exists but is invalid
        """
        try:
            with open(marker_path, 'r') as f:
                content = f.read().strip()
                
            # Marker must contain 'package=true'
            if 'package=true' not in content:
                raise PackageFormatError(
                    f"Invalid .modelchecker marker at {marker_path}",
                    f"Content: {content[:100]}",  # First 100 chars
                    "Marker must contain 'package=true'"
                )
                
            return True
            
        except OSError as e:
            raise PackageFormatError(
                f"Cannot read .modelchecker marker at {marker_path}",
                f"Error: {str(e)}",
                "Ensure marker file is readable"
            )