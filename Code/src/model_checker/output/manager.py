"""Output manager for saving model checking results."""

import os
from datetime import datetime
from typing import Optional, List, Dict, Any


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
    
    def __init__(self, save_output: bool, mode: str = 'batch', 
                 sequential_files: str = 'multiple',
                 interactive_manager=None):
        """Initialize output manager.
        
        Args:
            save_output: Whether to save output
            mode: Output mode ('batch' or 'sequential')
            sequential_files: For sequential mode, 'single' or 'multiple'
            interactive_manager: Optional InteractiveSaveManager instance
        """
        self.save_output = save_output
        self.output_dir = None
        self.models_data = []
        self.interactive_manager = interactive_manager
        
        # If interactive manager provided, use its mode
        if self.interactive_manager and hasattr(self.interactive_manager, 'mode'):
            self.mode = self.interactive_manager.mode
        else:
            self.mode = mode if mode in ['batch', 'sequential'] else 'batch'
        
        # Sequential mode options
        if self.mode == 'sequential':
            self.sequential_files = sequential_files
        else:
            self.sequential_files = None
            
        # Internal storage for batch mode
        self._batch_outputs = []
        
        # Track saved models in interactive mode
        self._interactive_saves = {}
        
    def should_save(self) -> bool:
        """Check if output should be saved.
        
        Returns:
            True if save_output is enabled, False otherwise
        """
        return self.save_output
        
    def create_output_directory(self, custom_name: Optional[str] = None):
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
        """Save example based on current mode.
        
        Delegates to appropriate method based on output mode.
        
        Args:
            example_name: Name of the example
            example_data: Dictionary of model data for JSON export
            formatted_output: Formatted markdown output
        """
        if self.mode == 'batch':
            self._append_to_batch(example_name, example_data, formatted_output)
        else:  # sequential
            self._save_sequential(example_name, example_data, formatted_output)
            
    def _append_to_batch(self, example_name: str, example_data: Dict[str, Any],
                        formatted_output: str):
        """Append example to batch storage.
        
        Args:
            example_name: Name of the example
            example_data: Dictionary of model data
            formatted_output: Formatted output
        """
        self._batch_outputs.append(formatted_output)
        self.models_data.append(example_data)
        
    def _save_sequential(self, example_name: str, example_data: Dict[str, Any],
                        formatted_output: str):
        """Save example in sequential mode.
        
        Args:
            example_name: Name of the example
            example_data: Dictionary of model data
            formatted_output: Formatted output
        """
        # Add to models data
        self.models_data.append(example_data)
        
        if self.sequential_files == 'multiple':
            # Save to individual file in sequential subdirectory
            file_path = os.path.join(self.output_dir, 'sequential', f'{example_name}.md')
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(formatted_output)
        else:  # single file
            # Append to single EXAMPLES.md file
            file_path = os.path.join(self.output_dir, 'EXAMPLES.md')
            mode = 'a' if os.path.exists(file_path) else 'w'
            
            with open(file_path, mode, encoding='utf-8') as f:
                if mode == 'a':
                    f.write('\n\n---\n\n')  # separator
                f.write(formatted_output)
                
    def finalize(self):
        """Finalize output and save all files.
        
        For batch mode, writes the accumulated outputs to EXAMPLES.md.
        For interactive mode, creates summary.json.
        Always saves MODELS.json with all collected model data.
        """
        if self.mode == 'batch' and self._batch_outputs:
            # Save batch outputs to EXAMPLES.md
            examples_path = os.path.join(self.output_dir, 'EXAMPLES.md')
            with open(examples_path, 'w', encoding='utf-8') as f:
                f.write('\n\n---\n\n'.join(self._batch_outputs))
        
        # Create summary for interactive mode
        if self.mode == 'interactive':
            self._create_interactive_summary()
                
        # Save models JSON
        self._save_models_json()
        
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