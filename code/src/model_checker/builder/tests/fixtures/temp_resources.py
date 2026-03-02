"""
Resource management utilities for test cleanup.

Provides utilities for managing temporary files, directories, and other
resources that need cleanup after tests complete.
"""

import tempfile
import os
import shutil
from typing import List, Optional, Any
from pathlib import Path


class TempFileCleanup:
    """Context manager for automatic cleanup of temporary resources."""
    
    def __init__(self):
        self.temp_files: List[str] = []
        self.temp_dirs: List[str] = []
        self.cleanup_functions: List[callable] = []
    
    def __enter__(self):
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        """Clean up all temporary resources."""
        # Clean up files
        for file_path in self.temp_files:
            try:
                if os.path.exists(file_path):
                    os.unlink(file_path)
            except OSError:
                pass  # Ignore cleanup errors
        
        # Clean up directories
        for dir_path in self.temp_dirs:
            try:
                if os.path.exists(dir_path):
                    shutil.rmtree(dir_path)
            except OSError:
                pass  # Ignore cleanup errors
        
        # Run custom cleanup functions
        for cleanup_func in self.cleanup_functions:
            try:
                cleanup_func()
            except Exception:
                pass  # Ignore cleanup errors
        
        # Clear lists
        self.temp_files.clear()
        self.temp_dirs.clear() 
        self.cleanup_functions.clear()
    
    def add_file(self, file_path: str) -> str:
        """Add file to cleanup list and return path."""
        self.temp_files.append(file_path)
        return file_path
    
    def add_dir(self, dir_path: str) -> str:
        """Add directory to cleanup list and return path."""
        self.temp_dirs.append(dir_path)
        return dir_path
    
    def add_cleanup(self, cleanup_func: callable):
        """Add custom cleanup function."""
        self.cleanup_functions.append(cleanup_func)
    
    def create_temp_file(self, content: str = "", suffix: str = ".py", 
                        prefix: str = "test_") -> str:
        """Create temporary file with content and add to cleanup."""
        with tempfile.NamedTemporaryFile(
            mode='w', suffix=suffix, prefix=prefix, delete=False
        ) as f:
            f.write(content)
            temp_path = f.name
        
        return self.add_file(temp_path)
    
    def create_temp_dir(self, prefix: str = "test_") -> str:
        """Create temporary directory and add to cleanup."""
        temp_dir = tempfile.mkdtemp(prefix=prefix)
        return self.add_dir(temp_dir)
    
    @property
    def temp_dir(self) -> str:
        """Get or create the default temporary directory."""
        if not self.temp_dirs:
            return self.create_temp_dir()
        return self.temp_dirs[0]


def create_temp_module_file(content: Optional[str] = None, 
                           cleanup: Optional[TempFileCleanup] = None) -> str:
    """Create temporary Python module file.
    
    Args:
        content: Module content (uses default minimal content if None)
        cleanup: TempFileCleanup instance to register file (optional)
    
    Returns:
        Path to created temporary file
    """
    if content is None:
        content = '''
from model_checker.theory_lib.logos import get_theory

theory = get_theory(['extensional'])
semantic_theories = {"Test": theory}
example_range = {"TEST": [[], ["A"], {"N": 2}]}
general_settings = {}
'''
    
    with tempfile.NamedTemporaryFile(
        mode='w', suffix='.py', prefix='test_module_', delete=False
    ) as f:
        f.write(content)
        temp_path = f.name
    
    if cleanup:
        cleanup.add_file(temp_path)
    
    return temp_path


def create_temp_project_dir(project_name: str = "test_project",
                           cleanup: Optional[TempFileCleanup] = None) -> str:
    """Create temporary project directory structure.
    
    Args:
        project_name: Name for the project directory
        cleanup: TempFileCleanup instance to register directory
    
    Returns:
        Path to created project directory
    """
    temp_dir = tempfile.mkdtemp(prefix=f"{project_name}_")
    
    # Create basic project structure
    os.makedirs(os.path.join(temp_dir, "examples"), exist_ok=True)
    os.makedirs(os.path.join(temp_dir, "tests"), exist_ok=True)
    
    if cleanup:
        cleanup.add_dir(temp_dir)
    
    return temp_dir


class MockFileSystem:
    """Mock file system operations for testing."""
    
    def __init__(self):
        self.files = {}
        self.dirs = set()
    
    def create_file(self, path: str, content: str = ""):
        """Create mock file with content."""
        self.files[path] = content
        # Add parent directories
        parent = str(Path(path).parent)
        if parent != path:  # Not root
            self.dirs.add(parent)
    
    def exists(self, path: str) -> bool:
        """Check if mock file or directory exists."""
        return path in self.files or path in self.dirs
    
    def read_file(self, path: str) -> str:
        """Read content from mock file."""
        if path not in self.files:
            raise FileNotFoundError(f"Mock file not found: {path}")
        return self.files[path]
    
    def list_dir(self, path: str) -> List[str]:
        """List mock directory contents."""
        if path not in self.dirs:
            raise FileNotFoundError(f"Mock directory not found: {path}")
        
        contents = []
        for file_path in self.files:
            if str(Path(file_path).parent) == path:
                contents.append(Path(file_path).name)
        
        for dir_path in self.dirs:
            if str(Path(dir_path).parent) == path:
                contents.append(Path(dir_path).name)
        
        return contents