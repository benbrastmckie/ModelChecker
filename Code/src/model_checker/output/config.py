"""Configuration management for output generation."""

from typing import List, Optional, Set
from .constants import (
    DEFAULT_FORMATS, FORMAT_MARKDOWN, FORMAT_JSON, FORMAT_NOTEBOOK,
    MODE_BATCH, MODE_SEQUENTIAL, MODE_INTERACTIVE,
    SEQUENTIAL_SINGLE, SEQUENTIAL_MULTIPLE
)


class OutputConfig:
    """Configuration for output formats and modes.
    
    This class manages the configuration for output generation including
    which formats to generate, output mode (batch/sequential/interactive),
    and other output-related settings.
    """
    
    def __init__(self, 
                 formats: Optional[List[str]] = None,
                 mode: str = MODE_BATCH,
                 sequential_files: str = SEQUENTIAL_MULTIPLE,
                 save_output: bool = True):
        """Initialize output configuration.
        
        Args:
            formats: List of output formats to generate (default: all)
            mode: Output mode (batch, sequential, interactive)
            sequential_files: For sequential mode - single or multiple files
            save_output: Whether output saving is enabled
        """
        self.enabled_formats = set(formats if formats is not None else DEFAULT_FORMATS)
        self.mode = mode
        self.sequential_files = sequential_files
        self.save_output = save_output
        
    def is_format_enabled(self, format_name: str) -> bool:
        """Check if a format is enabled for generation.
        
        Args:
            format_name: Format to check (markdown, json)
            
        Returns:
            True if format should be generated
        """
        return format_name in self.enabled_formats
    
    def get_enabled_formats(self) -> Set[str]:
        """Get set of enabled format names.
        
        Returns:
            Set of enabled format names
        """
        return self.enabled_formats.copy()
    
    def disable_format(self, format_name: str):
        """Disable a specific format.
        
        Args:
            format_name: Format to disable
        """
        self.enabled_formats.discard(format_name)
        
    def enable_format(self, format_name: str):
        """Enable a specific format.
        
        Args:
            format_name: Format to enable
        """
        self.enabled_formats.add(format_name)


def create_output_config_from_cli_args(args, general_settings=None) -> OutputConfig:
    """Create configuration from CLI arguments and optional settings.
    
    Priority order for sequential mode:
    1. CLI flag --sequential (highest priority)
    2. 'sequential' setting in general_settings
    3. Default to non-sequential (batch)
    
    Args:
        args: Parsed command line arguments
        general_settings: Optional dictionary with general settings
        
    Returns:
        OutputConfig instance configured from CLI and settings
    """
    # Determine if saving is enabled and which formats
    save_output = False
    formats = []
    
    # Check for new consolidated --save flag
    if hasattr(args, 'save') and args.save is not None:
        # --save flag was used, so saving is enabled
        save_output = True
        
        if len(args.save) == 0:
            # --save with no arguments means all formats
            formats = DEFAULT_FORMATS.copy()
        else:
            # --save with specific formats
            for fmt in args.save:
                if fmt == 'markdown':
                    formats.append(FORMAT_MARKDOWN)
                elif fmt == 'json':
                    formats.append(FORMAT_JSON)
                elif fmt in ('notebook', 'jupyter'):
                    formats.append(FORMAT_NOTEBOOK)
    else:
        # No --save flag, no output saved
        save_output = False
        formats = []  # Empty since we're not saving
    
    # Determine if sequential mode is enabled
    # Priority: CLI flag > setting > default (False)
    sequential = False
    
    # Check settings first (lower priority)
    if general_settings and general_settings.get('sequential', False):
        sequential = True
    
    # Check CLI flag (highest priority - overrides settings)
    if hasattr(args, 'sequential') and args.sequential:
        sequential = True
        
    # For backward compatibility, keep mode but set based on sequential
    # When sequential, use sequential mode (save immediately)
    # When not sequential, use batch mode (save at end)
    mode = MODE_SEQUENTIAL if sequential else MODE_BATCH
    
    # Handle explicit --output-mode flag (for non-sequential use)
    if not sequential and hasattr(args, 'output_mode') and args.output_mode:
        mode = args.output_mode
        
    # Sequential files option (only relevant for sequential mode)
    sequential_files = SEQUENTIAL_MULTIPLE
    if hasattr(args, 'sequential_files') and args.sequential_files:
        sequential_files = args.sequential_files
    
    return OutputConfig(
        formats=formats,
        mode=mode,
        sequential_files=sequential_files,
        save_output=save_output
    )
