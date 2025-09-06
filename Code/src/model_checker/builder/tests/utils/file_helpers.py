"""
File and directory helper utilities for testing.

Provides utilities for creating test file structures, validating outputs,
and managing test-related file operations.
"""

import os
import tempfile
import shutil
from typing import Dict, List, Optional, Union
from pathlib import Path


def create_test_module_structure(base_dir: str, 
                               files: Dict[str, str]) -> Dict[str, str]:
    """Create test module directory structure with specified files.
    
    Args:
        base_dir: Base directory to create structure in
        files: Dictionary mapping relative paths to file contents
    
    Returns:
        Dictionary mapping relative paths to absolute paths
    """
    created_files = {}
    
    for rel_path, content in files.items():
        full_path = os.path.join(base_dir, rel_path)
        
        # Create parent directories if needed
        parent_dir = os.path.dirname(full_path)
        if parent_dir:
            os.makedirs(parent_dir, exist_ok=True)
        
        # Write file content
        with open(full_path, 'w') as f:
            f.write(content)
        
        created_files[rel_path] = full_path
    
    return created_files


def validate_test_output(output: str, 
                        expected_patterns: List[str],
                        unexpected_patterns: Optional[List[str]] = None) -> bool:
    """Validate that test output contains expected patterns.
    
    Args:
        output: Output string to validate
        expected_patterns: Patterns that should be present
        unexpected_patterns: Patterns that should not be present
    
    Returns:
        True if validation passes
    
    Raises:
        AssertionError: If validation fails
    """
    # Check expected patterns
    for pattern in expected_patterns:
        if pattern not in output:
            raise AssertionError(
                f"Expected pattern '{pattern}' not found in output: {output[:200]}..."
            )
    
    # Check unexpected patterns
    if unexpected_patterns:
        for pattern in unexpected_patterns:
            if pattern in output:
                raise AssertionError(
                    f"Unexpected pattern '{pattern}' found in output: {output[:200]}..."
                )
    
    return True


def read_file_safely(file_path: str, 
                    encoding: str = 'utf-8',
                    fallback_encoding: str = 'latin-1') -> str:
    """Read file content with encoding fallback.
    
    Args:
        file_path: Path to file to read
        encoding: Primary encoding to try
        fallback_encoding: Fallback encoding if primary fails
    
    Returns:
        File content as string
    
    Raises:
        FileNotFoundError: If file doesn't exist
        UnicodeError: If both encodings fail
    """
    try:
        with open(file_path, 'r', encoding=encoding) as f:
            return f.read()
    except UnicodeDecodeError:
        with open(file_path, 'r', encoding=fallback_encoding) as f:
            return f.read()


def ensure_directory_exists(dir_path: str) -> str:
    """Ensure directory exists, creating if necessary.
    
    Args:
        dir_path: Directory path to ensure exists
    
    Returns:
        Absolute path to directory
    """
    abs_path = os.path.abspath(dir_path)
    os.makedirs(abs_path, exist_ok=True)
    return abs_path


def copy_test_files(source_patterns: List[str], 
                   dest_dir: str,
                   preserve_structure: bool = True) -> List[str]:
    """Copy test files matching patterns to destination.
    
    Args:
        source_patterns: List of glob patterns for source files
        dest_dir: Destination directory
        preserve_structure: Whether to preserve directory structure
    
    Returns:
        List of copied file paths
    """
    import glob
    
    ensure_directory_exists(dest_dir)
    copied_files = []
    
    for pattern in source_patterns:
        for source_file in glob.glob(pattern):
            if preserve_structure:
                # Preserve relative path structure
                rel_path = os.path.relpath(source_file)
                dest_path = os.path.join(dest_dir, rel_path)
                dest_parent = os.path.dirname(dest_path)
                if dest_parent:
                    os.makedirs(dest_parent, exist_ok=True)
            else:
                # Flatten to dest_dir
                filename = os.path.basename(source_file)
                dest_path = os.path.join(dest_dir, filename)
            
            shutil.copy2(source_file, dest_path)
            copied_files.append(dest_path)
    
    return copied_files


def find_files_with_pattern(root_dir: str, 
                          filename_pattern: str = "*.py",
                          content_pattern: Optional[str] = None) -> List[str]:
    """Find files matching filename and optionally content patterns.
    
    Args:
        root_dir: Root directory to search
        filename_pattern: Glob pattern for filenames
        content_pattern: Optional text pattern to search in file contents
    
    Returns:
        List of matching file paths
    """
    import glob
    
    matching_files = []
    pattern_path = os.path.join(root_dir, "**", filename_pattern)
    
    for file_path in glob.glob(pattern_path, recursive=True):
        if content_pattern is None:
            matching_files.append(file_path)
        else:
            try:
                content = read_file_safely(file_path)
                if content_pattern in content:
                    matching_files.append(file_path)
            except (UnicodeError, IOError):
                # Skip files that can't be read
                continue
    
    return matching_files


def create_minimal_python_module(module_name: str, 
                                content: Optional[str] = None) -> str:
    """Create minimal Python module in temporary location.
    
    Args:
        module_name: Name for the module (without .py)
        content: Module content (uses default if None)
    
    Returns:
        Path to created module file
    """
    if content is None:
        content = f'''"""
Test module: {module_name}

This is a minimal test module for testing purposes.
"""

def test_function():
    return "Hello from {module_name}"

TEST_CONSTANT = "{module_name}_constant"
'''
    
    with tempfile.NamedTemporaryFile(
        mode='w', 
        suffix='.py', 
        prefix=f'{module_name}_',
        delete=False
    ) as f:
        f.write(content)
        return f.name


def cleanup_test_files(file_patterns: List[str]) -> None:
    """Clean up test files matching patterns.
    
    Args:
        file_patterns: List of glob patterns for files to clean up
    """
    import glob
    
    for pattern in file_patterns:
        for file_path in glob.glob(pattern):
            try:
                if os.path.isfile(file_path):
                    os.unlink(file_path)
                elif os.path.isdir(file_path):
                    shutil.rmtree(file_path)
            except OSError:
                # Ignore cleanup errors
                pass