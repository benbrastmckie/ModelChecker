"""Output manager for saving model checking results."""

import os
import json
import logging
from datetime import datetime
from typing import Dict, List, Any, Optional

# Set up logger for this module
logger = logging.getLogger(__name__)

from .config import OutputConfig
from .constants import (
    FORMAT_MARKDOWN, FORMAT_JSON, FORMAT_NOTEBOOK,
    DEFAULT_FORMATS, EXTENSIONS,
    DEFAULT_MARKDOWN_FILE, DEFAULT_JSON_FILE, DEFAULT_NOTEBOOK_FILE
)
from .helpers import save_file, save_json, ensure_directory_exists
from .errors import OutputError, OutputDirectoryError


class OutputManager:
    """Manages output directory creation and file saving.
    
    This class handles the creation of output directories and coordinates
    the saving of model checking results. It supports two behaviors:
    - Batch: Accumulate all results and save at the end
    - Sequential: Save immediately when user approves
    """
    
    def __init__(self, config: OutputConfig, prompt_manager=None):
        """Initialize output manager.
        
        Args:
            config: Output configuration
            prompt_manager: Optional SequentialSaveManager for user prompting
            
        Raises:
            ValueError: If config is not provided
        """
        if not config:
            raise ValueError("OutputConfig is required")
        
        self.config = config
        self.prompt_manager = prompt_manager
        self.save_output = config.save_output
        self.output_dir = None
        
        # Track outputs based on mode
        self.accumulated_outputs = []  # For batch mode
        self.saved_models = {}  # Track what was saved in sequential mode
        
        # Initialize formatters
        self._initialize_formatters()
        
        # Module context for notebook generation
        self._module_vars = None
        self._source_path = None
    
    def _initialize_formatters(self):
        """Initialize format handlers."""
        from .formatters import MarkdownFormatter, JSONFormatter, NotebookFormatter
        
        self.formatters = {}
        if self.config.is_format_enabled(FORMAT_MARKDOWN):
            self.formatters[FORMAT_MARKDOWN] = MarkdownFormatter()
        if self.config.is_format_enabled(FORMAT_JSON):
            self.formatters[FORMAT_JSON] = JSONFormatter()
        if self.config.is_format_enabled(FORMAT_NOTEBOOK):
            self.formatters[FORMAT_NOTEBOOK] = NotebookFormatter()
    
    def set_module_context(self, module_vars: Dict[str, Any], source_path: str):
        """Set module context for notebook generation.
        
        Args:
            module_vars: Module variables including semantic_theories
            source_path: Path to the source examples file
        """
        self._module_vars = module_vars
        self._source_path = source_path
        
        # Pass context to notebook formatter if it exists
        if FORMAT_NOTEBOOK in self.formatters:
            notebook_formatter = self.formatters[FORMAT_NOTEBOOK]
            if hasattr(notebook_formatter, 'set_context'):
                notebook_formatter.set_context(module_vars, source_path)
    
    def should_save(self) -> bool:
        """Check if output should be saved.
        
        Returns:
            True if save_output is enabled
        """
        return self.save_output
    
    def create_output_directory(self, custom_name: str = None):
        """Create timestamped output directory.
        
        Args:
            custom_name: Optional custom directory name
        """
        if custom_name:
            self.output_dir = custom_name
        else:
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            self.output_dir = f'output_{timestamp}'
        
        os.makedirs(self.output_dir, exist_ok=True)
    
    def save_example(self, example_name: str, example_data: Dict[str, Any],
                    formatted_output: str):
        """Save example based on configuration.
        
        In sequential mode, this is called only after user approval.
        In batch mode, this accumulates for later saving.
        
        Args:
            example_name: Name of the example
            example_data: Dictionary of model data for JSON export
            formatted_output: Formatted markdown output
        """
        if self.config.sequential:
            # Sequential mode - save immediately (already approved)
            self._save_immediately(example_name, example_data, formatted_output)
            self.saved_models[example_name] = True
        else:
            # Batch mode - accumulate for later
            self.accumulated_outputs.append((example_name, example_data, formatted_output))
    
    def save_prompted_model(self, example_name: str, model_data: Dict[str, Any],
                           formatted_output: str, model_num: int):
        """Save individual model in sequential mode.
        
        Creates per-example directories with numbered model files.
        
        Args:
            example_name: Name of the example
            model_data: Dictionary of model data
            formatted_output: Formatted markdown output
            model_num: Model number (1-based)
        """
        # Create example directory
        example_dir = os.path.join(self.output_dir, example_name)
        os.makedirs(example_dir, exist_ok=True)
        
        # Save markdown file
        md_path = os.path.join(example_dir, f'MODEL_{model_num}.md')
        save_file(md_path, formatted_output)
        
        # Save JSON file if enabled
        if self.config.is_format_enabled(FORMAT_JSON):
            json_path = os.path.join(example_dir, f'MODEL_{model_num}.json')
            save_json(json_path, model_data)
        
        # Track this save
        if example_name not in self.saved_models:
            self.saved_models[example_name] = []
        self.saved_models[example_name].append(model_num)
        
        # Display save location
        print(f"Saved to: {md_path}")
    
    def _save_immediately(self, example_name: str, example_data: Dict[str, Any],
                         formatted_output: str):
        """Save outputs immediately to disk.
        
        Args:
            example_name: Name of the example
            example_data: Model data dictionary
            formatted_output: Formatted output string
        """
        # Generate outputs for all enabled formats
        for format_name, formatter in self.formatters.items():
            try:
                if format_name == FORMAT_MARKDOWN:
                    content = formatted_output
                else:
                    content = formatter.format_example(example_data, formatted_output)
                
                # Determine filename
                extension = EXTENSIONS.get(format_name, format_name)
                
                if self.config.sequential:
                    # In sequential mode, save to example directories
                    example_dir = os.path.join(self.output_dir, example_name)
                    os.makedirs(example_dir, exist_ok=True)
                    filepath = os.path.join(example_dir, f"{example_name}.{extension}")
                else:
                    # In batch mode (shouldn't happen here but handle it)
                    filepath = os.path.join(self.output_dir, f"{example_name}.{extension}")
                
                save_file(filepath, content)
                
            except Exception as e:
                logger.warning(f"Failed to save {format_name} for {example_name}: {e}")
    
    def finalize(self):
        """Finalize output - save accumulated outputs and generate summary."""
        if self.config.sequential:
            # Sequential mode - create summary of what was saved
            self._create_summary()
        else:
            # Batch mode - save all accumulated outputs
            self._save_batch_outputs()
        
        # Generate notebook if enabled
        if self.config.is_format_enabled(FORMAT_NOTEBOOK):
            self._generate_notebook()
    
    def _save_batch_outputs(self):
        """Save all accumulated outputs in batch mode."""
        if not self.accumulated_outputs:
            return
        
        # Combine all markdown outputs
        all_markdown = []
        all_json_data = []
        
        for example_name, example_data, formatted_output in self.accumulated_outputs:
            all_markdown.append(formatted_output)
            all_json_data.append(example_data)
        
        # Save combined markdown
        if self.config.is_format_enabled(FORMAT_MARKDOWN):
            combined_md = "\n\n---\n\n".join(all_markdown)
            md_path = os.path.join(self.output_dir, DEFAULT_MARKDOWN_FILE)
            save_file(md_path, combined_md)
        
        # Save combined JSON
        if self.config.is_format_enabled(FORMAT_JSON):
            json_data = {
                "metadata": {
                    "timestamp": datetime.now().isoformat(),
                    "version": "1.0"
                },
                "models": all_json_data
            }
            json_path = os.path.join(self.output_dir, DEFAULT_JSON_FILE)
            save_json(json_path, json_data)
    
    def _create_summary(self):
        """Create summary.json for sequential mode."""
        if not self.saved_models:
            return
        
        summary = {
            "metadata": {
                "timestamp": datetime.now().isoformat(),
                "mode": "sequential",
                "total_examples": len(self.saved_models),
                "total_models": sum(
                    len(models) if isinstance(models, list) else 1 
                    for models in self.saved_models.values()
                )
            },
            "examples": {}
        }
        
        # Add example summaries
        for example_name, models in self.saved_models.items():
            if isinstance(models, list):
                summary["examples"][example_name] = {
                    "model_count": len(models),
                    "model_numbers": models,
                    "directory": example_name
                }
            else:
                summary["examples"][example_name] = {
                    "saved": True,
                    "directory": example_name
                }
        
        # Save summary
        summary_path = os.path.join(self.output_dir, 'summary.json')
        save_json(summary_path, summary)
    
    def _generate_notebook(self):
        """Generate Jupyter notebook if enabled."""
        if FORMAT_NOTEBOOK not in self.formatters:
            logger.warning("Notebook formatter not initialized")
            return
        
        notebook_formatter = self.formatters[FORMAT_NOTEBOOK]
        
        # Ensure context has been set
        if not self._module_vars or not self._source_path:
            logger.warning("Module context not set for notebook generation")
            return
        
        try:
            notebook_path = os.path.join(self.output_dir, DEFAULT_NOTEBOOK_FILE)
            
            if hasattr(notebook_formatter, 'format_for_streaming'):
                # Direct streaming for efficiency
                notebook_formatter.format_for_streaming(notebook_path)
                logger.info(f"Notebook generated: {notebook_path}")
            else:
                # Fallback to basic method
                notebook_content = notebook_formatter.format_batch([])
                save_file(notebook_path, notebook_content)
                logger.info(f"Notebook generated via batch: {notebook_path}")
                
        except Exception as e:
            logger.warning(f"Failed to generate notebook: {e}")