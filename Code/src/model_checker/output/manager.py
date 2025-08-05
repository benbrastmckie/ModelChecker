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
                 sequential_files: str = 'multiple'):
        """Initialize output manager.
        
        Args:
            save_output: Whether to save output
            mode: Output mode ('batch' or 'sequential')
            sequential_files: For sequential mode, 'single' or 'multiple'
        """
        self.save_output = save_output
        self.mode = mode if mode in ['batch', 'sequential'] else 'batch'
        self.output_dir = None
        self.models_data = []
        
        # Sequential mode options
        if self.mode == 'sequential':
            self.sequential_files = sequential_files
        else:
            self.sequential_files = None
            
        # Internal storage for batch mode
        self._batch_outputs = []
        
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
                    f.write('\\n---\\n\\n')  # separator
                f.write(formatted_output)
                
    def finalize(self):
        """Finalize output and save all files.
        
        For batch mode, writes the accumulated outputs to EXAMPLES.md.
        Always saves MODELS.json with all collected model data.
        """
        if self.mode == 'batch' and self._batch_outputs:
            # Save batch outputs to EXAMPLES.md
            examples_path = os.path.join(self.output_dir, 'EXAMPLES.md')
            with open(examples_path, 'w', encoding='utf-8') as f:
                f.write('\\n---\\n\\n'.join(self._batch_outputs))
                
        # Save models JSON (implementation in Phase 2)
        self._save_models_json()
        
    def _save_models_json(self):
        """Save models data to JSON file.
        
        This will be implemented in Phase 2.
        """
        pass  # TODO: Implement in Phase 2