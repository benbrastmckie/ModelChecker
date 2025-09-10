"""Output manager for saving model checking results."""

import os
import logging
from datetime import datetime
from typing import Dict, List, Any

# Set up logger for this module
logger = logging.getLogger(__name__)

# Import new components
from .config import OutputConfig
from .constants import (
    MODE_BATCH, MODE_SEQUENTIAL, MODE_INTERACTIVE,
    FORMAT_MARKDOWN, FORMAT_JSON,
    DEFAULT_FORMATS, EXTENSIONS
)
from .helpers import (
    create_timestamped_directory, save_file, save_json,
    combine_markdown_sections, ensure_directory_exists
)
from .errors import OutputError, OutputDirectoryError, OutputIOError


class OutputManager:
    """Manages output directory creation and file organization.
    
    This class handles the creation of output directories, manages different
    output modes (batch vs sequential), and coordinates the saving of model
    checking results in structured formats.
    
    Attributes:
        save_output: Whether output saving is enabled
        mode: Output mode ('batch' or 'sequential')
        sequential_files: For sequential mode, 'single' or 'multiple' files
        output_dir: Path to the created output directory
        models_data: List of model data dictionaries for JSON export
    """
    
    def __init__(self, config: OutputConfig, 
                 interactive_manager=None):
        """Initialize output manager.
        
        Args:
            config: REQUIRED output configuration
            interactive_manager: Optional InteractiveSaveManager instance
            
        Raises:
            ValueError: If config is not provided
        """
        if not config:
            raise ValueError(
                "OutputConfig is required. Create with: "
                "OutputConfig(formats=['markdown', 'json'], mode='batch')"
            )
        
        self.config = config
        self.save_output = config.save_output
        self.output_dir = None
        self.models_data = []
        self.interactive_manager = interactive_manager
        
        # If interactive manager provided, use its mode
        if self.interactive_manager and hasattr(self.interactive_manager, 'mode'):
            self.mode = self.interactive_manager.mode
        else:
            self.mode = config.mode if config.mode in ['batch', 'sequential'] else 'batch'
        
        # Sequential mode options
        if self.mode == 'sequential':
            self.sequential_files = config.sequential_files
        else:
            self.sequential_files = None
        
        # Initialize formatters and strategy
        self._initialize_components()
            
        # Track saved models in interactive mode
        self._interactive_saves = {}
    
    def _initialize_components(self):
        """Initialize formatters and strategy based on configuration."""
        # Import formatters lazily to avoid circular imports
        from .formatters import MarkdownFormatter, JSONFormatter
        from .strategies import BatchOutputStrategy, SequentialOutputStrategy, InteractiveOutputStrategy
        
        # Initialize formatters based on enabled formats
        self.formatters = {}
        if self.config.is_format_enabled(FORMAT_MARKDOWN):
            self.formatters[FORMAT_MARKDOWN] = MarkdownFormatter()
        if self.config.is_format_enabled(FORMAT_JSON):
            self.formatters[FORMAT_JSON] = JSONFormatter()
        # Note: Notebook generation is now handled by StreamingNotebookGenerator in BuildModule
        
        # Initialize strategy based on mode
        if self.mode == MODE_BATCH:
            self.strategy = BatchOutputStrategy()
        elif self.mode == MODE_SEQUENTIAL:
            self.strategy = SequentialOutputStrategy(self.sequential_files)
        elif self.mode == MODE_INTERACTIVE:
            self.strategy = InteractiveOutputStrategy(self.interactive_manager)
        else:
            self.strategy = BatchOutputStrategy()  # Default to batch
        
    def should_save(self) -> bool:
        """Check if output should be saved.
        
        Returns:
            True if save_output is enabled, False otherwise
        """
        return self.save_output
        
    def create_output_directory(self, custom_name: str = None):
        """Create timestamped output directory.
        
        Creates a directory with timestamp or custom name. For sequential
        mode with multiple files, also creates a 'sequential' subdirectory.
        
        Args:
            custom_name: Optional custom directory name instead of timestamp
        """
        if custom_name:
            self.output_dir = custom_name
        else:
            # Create timestamp-based directory name
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            self.output_dir = f'output_{timestamp}'
            
        # Create the directory
        os.makedirs(self.output_dir, exist_ok=True)
        
        # Create sequential subdirectory if needed
        if self.mode == 'sequential' and self.sequential_files == 'multiple':
            sequential_dir = os.path.join(self.output_dir, 'sequential')
            os.makedirs(sequential_dir, exist_ok=True)
            
    def save_example(self, example_name: str, example_data: Dict[str, Any],
                    formatted_output: str):
        """Save example based on current mode and enabled formats.
        
        Generates output in all enabled formats and saves according
        to the current strategy.
        
        Args:
            example_name: Name of the example
            example_data: Dictionary of model data for JSON export
            formatted_output: Formatted markdown output (legacy parameter)
        """
        # Generate outputs for all enabled formats
        formatted_outputs = {}
        
        for format_name, formatter in self.formatters.items():
            try:
                # Use the appropriate formatter
                if format_name == FORMAT_MARKDOWN and formatted_output:
                    # Use provided markdown directly when available
                    formatted_outputs[format_name] = formatted_output
                else:
                    # Generate format-specific output
                    formatted_outputs[format_name] = formatter.format_example(
                        example_data, formatted_output
                    )
            except Exception as e:
                # Log error but continue with other formats
                logger.warning(f"Failed to format {format_name}: {e}")
                continue
        
        # Delegate to strategy for saving
        if self.strategy.should_save_immediately():
            self._save_all_formats(example_name, formatted_outputs)
        else:
            self.strategy.accumulate(example_name, formatted_outputs)
        
        # Track model data for JSON export
        self.models_data.append(example_data)
            
                
    def _save_all_formats(self, example_name: str, formatted_outputs: Dict[str, str]):
        """Save outputs in all enabled formats.
        
        Args:
            example_name: Name of the example
            formatted_outputs: Dictionary mapping format names to content
        """
        for format_name, content in formatted_outputs.items():
            try:
                extension = EXTENSIONS.get(format_name, format_name)
                filepath = self.strategy.get_file_path(
                    self.output_dir, example_name, format_name, extension
                )
                
                # Handle appending for sequential single file mode
                if (self.mode == MODE_SEQUENTIAL and 
                    self.sequential_files == 'single' and
                    os.path.exists(filepath)):
                    # Append with separator
                    with open(filepath, 'a', encoding='utf-8') as f:
                        f.write('\n\n---\n\n')
                        f.write(content)
                else:
                    # Write new file
                    save_file(filepath, content)
                    
            except OutputIOError as e:
                logger.warning(f"Failed to save {format_name} for {example_name}: {e}")
    
    def finalize(self):
        """Finalize output and save JSON/Markdown files only."""
        # Let strategy handle finalization
        if hasattr(self.strategy, 'finalize'):
            self.strategy.finalize(lambda name, outputs: self._finalize_outputs(name, outputs))
        
        # Create summary for interactive mode
        if self.mode == 'interactive':
            self._create_interactive_summary()
                
        # Save models JSON if JSON format is enabled
        if self.config.is_format_enabled(FORMAT_JSON):
            self._save_models_json()
        
        # Note: Notebook generation is now handled independently in BuildModule
    
    def _finalize_outputs(self, name: str, outputs: Dict):
        """Helper to finalize outputs from strategy.
        
        Args:
            name: Output name (e.g., 'batch_combined')
            outputs: Dictionary of format outputs
        """
        if name == 'batch_combined':
            # Handle combined batch outputs
            for format_name in outputs:
                if format_name in self.formatters:
                    formatter = self.formatters[format_name]
                    combined = formatter.format_batch(outputs[format_name])
                    
                    # Determine filename
                    if format_name == FORMAT_MARKDOWN:
                        filename = 'EXAMPLES.md'
                    elif format_name == FORMAT_JSON:
                        filename = 'MODELS.json'
                    else:
                        extension = EXTENSIONS.get(format_name, format_name)
                        filename = f"output.{extension}"
                    
                    filepath = os.path.join(self.output_dir, filename)
                    save_file(filepath, combined)
        elif name == 'summary':
            # Save summary JSON
            if FORMAT_JSON in outputs:
                summary_path = os.path.join(self.output_dir, 'summary.json')
                save_json(summary_path, outputs[FORMAT_JSON])
        
    def _save_models_json(self):
        """Save models data to JSON file.
        
        Creates a MODELS.json file with metadata and all collected model data
        in a structured format suitable for programmatic access.
        """
        import json
        from datetime import datetime
        
        # Create data structure
        data = {
            "metadata": {
                "timestamp": datetime.now().isoformat(),
                "version": "1.0"
            },
            "models": self.models_data
        }
        
        # Save to JSON file
        json_path = os.path.join(self.output_dir, 'MODELS.json')
        with open(json_path, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=4, ensure_ascii=False)
            
    def create_example_directory(self, example_name: str) -> str:
        """Create directory for an example in interactive mode.
        
        Args:
            example_name: Name of the example
            
        Returns:
            str: Path to the created directory
        """
        if not self.output_dir:
            raise ValueError("Output directory not created yet")
            
        example_dir = os.path.join(self.output_dir, example_name)
        os.makedirs(example_dir, exist_ok=True)
        return example_dir
        
    def save_model_interactive(self, example_name: str, model_data: Dict[str, Any],
                              formatted_output: str, model_num: int):
        """Save individual model in interactive mode.
        
        Args:
            example_name: Name of the example
            model_data: Dictionary of model data
            formatted_output: Formatted markdown output
            model_num: Model number (1-based)
        """
        # Create example directory if needed
        example_dir = self.create_example_directory(example_name)
        
        # Save markdown file
        md_path = os.path.join(example_dir, f'MODEL_{model_num}.md')
        with open(md_path, 'w', encoding='utf-8') as f:
            f.write(formatted_output)
            
        # Save JSON file
        json_path = os.path.join(example_dir, f'MODEL_{model_num}.json')
        import json
        with open(json_path, 'w', encoding='utf-8') as f:
            json.dump(model_data, f, indent=4, ensure_ascii=False)
            
        # Track this save
        if example_name not in self._interactive_saves:
            self._interactive_saves[example_name] = []
        self._interactive_saves[example_name].append(model_num)
        
        # Add to models data for overall JSON
        self.models_data.append(model_data)
        
        # Display save location
        # Keep print for user interaction - showing save location
        print(f"Saved to: {md_path}")
        
    def get_output_path(self, example_name: str, filename: str) -> str:
        """Get full path for output file.
        
        Args:
            example_name: Name of the example (for interactive mode)
            filename: Name of the file
            
        Returns:
            str: Full path to the file
        """
        if self.mode == 'interactive':
            example_dir = os.path.join(self.output_dir, example_name)
            return os.path.join(example_dir, filename)
        else:
            return os.path.join(self.output_dir, filename)
            
    def _create_interactive_summary(self):
        """Create summary.json for interactive mode.
        
        Summarizes what was saved for each example.
        """
        import json
        from datetime import datetime
        
        summary = {
            "metadata": {
                "timestamp": datetime.now().isoformat(),
                "mode": "interactive",
                "total_examples": len(self._interactive_saves),
                "total_models": sum(len(models) for models in self._interactive_saves.values())
            },
            "examples": {}
        }
        
        # Add example summaries
        for example_name, model_nums in self._interactive_saves.items():
            summary["examples"][example_name] = {
                "model_count": len(model_nums),
                "model_numbers": model_nums,
                "directory": example_name
            }
            
        # Save summary
        summary_path = os.path.join(self.output_dir, 'summary.json')
        with open(summary_path, 'w', encoding='utf-8') as f:
            json.dump(summary, f, indent=4, ensure_ascii=False)
    
