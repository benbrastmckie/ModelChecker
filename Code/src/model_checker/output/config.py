"""Simple output configuration."""

from typing import List, Optional


class OutputConfig:
    """Output configuration with two behaviors: batch or sequential.
    
    The configuration manages:
    - Which formats to generate (markdown, json, notebook)
    - Whether to save sequentially (with prompts)
    - Whether output is enabled at all
    """
    
    def __init__(self,
                 formats: List[str] = None,
                 sequential: bool = False,
                 save_output: bool = True):
        """Initialize output configuration.
        
        Args:
            formats: List of output formats to generate
            sequential: Whether to save sequentially (prompting for each model)
            save_output: Whether output saving is enabled
        """
        self.formats = formats if formats is not None else ['markdown', 'json']
        self.sequential = sequential
        self.save_output = save_output
    
    def is_format_enabled(self, format_name: str) -> bool:
        """Check if a format is enabled.
        
        Args:
            format_name: Format to check ('markdown', 'json', 'notebook')
            
        Returns:
            True if format should be generated
        """
        return format_name in self.formats
    

def create_output_config(args, settings=None) -> OutputConfig:
    """Create config from CLI arguments and settings.
    
    Priority for sequential mode:
    1. CLI flag --sequential (highest)
    2. Setting 'sequential' 
    3. Default (False)
    
    Args:
        args: Parsed command line arguments
        settings: Optional settings dictionary
        
    Returns:
        OutputConfig instance
    """
    # Determine formats from --save flag
    formats = []
    save_output = False
    
    if hasattr(args, 'save') and args.save is not None:
        save_output = True
        if len(args.save) == 0:
            # --save with no args means all formats
            formats = ['markdown', 'json', 'notebook']
        else:
            # --save with specific formats
            for fmt in args.save:
                if fmt in ('markdown', 'md'):
                    formats.append('markdown')
                elif fmt == 'json':
                    formats.append('json')
                elif fmt in ('notebook', 'jupyter'):
                    formats.append('notebook')
    
    # Check sequential flag - settings first (lower priority)
    sequential = False
    if settings and settings.get('sequential', False):
        sequential = True
    
    # CLI flag overrides settings
    if hasattr(args, 'sequential') and args.sequential:
        sequential = True
        
    return OutputConfig(
        formats=formats if save_output else [],
        sequential=sequential,
        save_output=save_output
    )