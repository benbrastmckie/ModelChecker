"""Helper functions for output operations."""

import os
import json
from typing import Dict, Any, Optional
from datetime import datetime
from .constants import OUTPUT_DIR_PREFIX, OUTPUT_DIR_TIMESTAMP_FORMAT
from .errors import OutputIOError, OutputDirectoryError


def create_timestamped_directory(base_path: str = ".", 
                                prefix: str = OUTPUT_DIR_PREFIX) -> str:
    """Create a directory with timestamp suffix.
    
    Args:
        base_path: Base path where to create the directory
        prefix: Prefix for the directory name
        
    Returns:
        Path to the created directory
        
    Raises:
        OutputDirectoryError: If directory cannot be created
    """
    timestamp = datetime.now().strftime(OUTPUT_DIR_TIMESTAMP_FORMAT)
    dir_name = f"{prefix}{timestamp}"
    full_path = os.path.join(base_path, dir_name)
    
    try:
        os.makedirs(full_path, exist_ok=True)
        return full_path
    except OSError as e:
        raise OutputDirectoryError(full_path, str(e))


def save_file(filepath: str, content: str, mode: str = 'w', 
             encoding: str = 'utf-8'):
    """Save content to a file with error handling.
    
    Args:
        filepath: Path where to save the file
        content: Content to write
        mode: File open mode ('w' for write, 'a' for append)
        encoding: File encoding
        
    Raises:
        OutputIOError: If file cannot be written
    """
    try:
        # Ensure directory exists
        directory = os.path.dirname(filepath)
        if directory:
            os.makedirs(directory, exist_ok=True)
            
        with open(filepath, mode, encoding=encoding) as f:
            f.write(content)
    except OSError as e:
        raise OutputIOError(filepath, str(e))


def save_json(filepath: str, data: Any, indent: int = 4, 
             ensure_ascii: bool = False):
    """Save data as JSON file.
    
    Args:
        filepath: Path where to save the JSON
        data: Data to serialize
        indent: Indentation level
        ensure_ascii: Whether to escape non-ASCII characters
        
    Raises:
        OutputIOError: If file cannot be written
    """
    try:
        content = json.dumps(data, indent=indent, ensure_ascii=ensure_ascii)
        save_file(filepath, content)
    except (TypeError, ValueError) as e:
        raise OutputIOError(filepath, f"JSON serialization error: {e}")


def combine_markdown_sections(sections: list, separator: str = "\n\n---\n\n") -> str:
    """Combine multiple markdown sections with separators.
    
    Args:
        sections: List of markdown strings
        separator: Separator between sections
        
    Returns:
        Combined markdown string
    """
    # Filter out empty sections
    non_empty = [s for s in sections if s and s.strip()]
    return separator.join(non_empty)


def extract_model_data(model_structure, example_name: str, 
                       theory_name: str) -> Dict[str, Any]:
    """Extract relevant data from a model structure.
    
    Args:
        model_structure: The model structure object
        example_name: Name of the example
        theory_name: Name of the theory used
        
    Returns:
        Dictionary containing extracted model data
    """
    # Check if model was found
    has_model = getattr(model_structure, 'z3_model_status', False)
    
    if not has_model:
        return {
            "example": example_name,
            "theory": theory_name,
            "has_model": False,
            "evaluation_world": None,
            "states": {"possible": [], "impossible": [], "worlds": []},
            "relations": {},
            "propositions": {}
        }
    
    # Extract full model data using existing collectors
    data = {
        "example": example_name,
        "theory": theory_name,
        "has_model": True,
    }
    
    # Use extraction methods if available
    if hasattr(model_structure, 'extract_states'):
        data["states"] = model_structure.extract_states()
    else:
        data["states"] = {"possible": [], "impossible": [], "worlds": []}
        
    if hasattr(model_structure, 'extract_evaluation_world'):
        data["evaluation_world"] = model_structure.extract_evaluation_world()
    else:
        data["evaluation_world"] = None
        
    if hasattr(model_structure, 'extract_propositions'):
        data["propositions"] = model_structure.extract_propositions()
    else:
        data["propositions"] = {}
        
    if hasattr(model_structure, 'extract_relations'):
        data["relations"] = model_structure.extract_relations()
    else:
        data["relations"] = {}
    
    return data


def ensure_directory_exists(directory: str) -> None:
    """Ensure a directory exists, creating it if necessary.
    
    Args:
        directory: Path to the directory
        
    Raises:
        OutputDirectoryError: If directory cannot be created
    """
    try:
        os.makedirs(directory, exist_ok=True)
    except OSError as e:
        raise OutputDirectoryError(directory, str(e))


def get_file_extension(format_name: str) -> str:
    """Get file extension for a format name.
    
    Args:
        format_name: Format name (markdown, json, notebook)
        
    Returns:
        File extension without dot
    """
    from .constants import EXTENSIONS
    return EXTENSIONS.get(format_name, format_name)