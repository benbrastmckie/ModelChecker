"""BuildModule implementation for managing model checking examples.

This module provides the BuildModule class for loading and executing model checking 
examples from Python modules. It handles dynamic module loading, configuration 
settings, and coordinating the model checking process.
"""

# Standard library imports
import os
import sys
from typing import TYPE_CHECKING, Any, Dict, Optional, Tuple
from types import ModuleType

# Local imports
from .types import (
    TheoryDict, ExampleDict, SettingsDict, TheoryName
)

if TYPE_CHECKING:
    from .loader import ModuleLoader
    from .runner import ModelRunner
    from .translation import OperatorTranslation
    from .example import BuildExample
    from ..output import OutputManager, InteractiveManager


class BuildModule:
    """Manages loading and executing model checking examples from Python modules.
    
    This class is responsible for dynamically loading a Python module containing modal logic
    examples, extracting configuration settings, and coordinating the model checking process.
    
    Attributes:
        module_flags: Command-line flags that override module settings
        module_path (str): File path to the Python module being loaded
        module_name (str): Name of the module (without extension)
        module: The loaded Python module object
        semantic_theories (dict): Mapping of theory names to their implementations
        example_range (dict): Mapping of example names to their definitions
        general_settings (dict): General configuration settings for model checking
        print_impossible (bool): Whether to print models that are impossible
        print_constraints (bool): Whether to print Z3 constraints
        print_z3 (bool): Whether to print raw Z3 output
        save_output (bool): Whether to save results to files
        maximize (bool): Whether to maximize the model size
    """

    def __init__(self, module_flags: Any) -> None:
        """Initialize BuildModule with module flags containing configuration.
        
        Args:
            module_flags: Object containing configuration flags including file_path
                        and other optional settings that override module settings
        
        Raises:
            ImportError: If the module cannot be loaded
            AttributeError: If required attributes are missing from the module
        """
        self.module_flags: Any = module_flags
        self.module_path: str = self.module_flags.file_path
        self.module_name: str = os.path.splitext(os.path.basename(self.module_path))[0]
        
        # Load the module and its attributes
        self._load_module()
        
        # Store module variables for output generation
        self.module_variables = {
            'semantic_theories': self.semantic_theories,
            'example_range': self.example_range,
            'general_settings': getattr(self.module, 'general_settings', {})
        }
        
        # Initialize settings
        self._initialize_settings()
        
        # Initialize output management
        self._initialize_output_management()
        
        # Initialize component instances
        self._initialize_components()
    
    def _load_module(self) -> None:
        """Load the module and extract required attributes."""
        from model_checker.builder.loader import ModuleLoader
        
        # Create loader instance
        self.loader = ModuleLoader(self.module_name, self.module_path)
        
        # Load the module
        self.module = self.loader.load_module()
        
        # Load core attributes
        self.semantic_theories = self.loader.load_attribute(self.module, "semantic_theories")
        self.example_range = self.loader.load_attribute(self.module, "example_range")
        
        # Store raw settings for later processing
        self.raw_general_settings = getattr(self.module, "general_settings", None)
    
    def _initialize_settings(self) -> None:
        """Initialize and validate general settings."""
        from model_checker.settings import SettingsManager, DEFAULT_GENERAL_SETTINGS
        import contextlib
        import io
        
        # Initialize general settings
        if self.raw_general_settings is not None:
            # Use first theory's defaults as baseline
            first_theory = next(iter(self.semantic_theories.values()))
            # Create a temporary manager to get the merged defaults
            # Don't print warnings during this setup phase
            with contextlib.redirect_stdout(io.StringIO()):
                temp_manager = SettingsManager(first_theory, DEFAULT_GENERAL_SETTINGS)
                self.general_settings = temp_manager.validate_general_settings(self.raw_general_settings)
                self.general_settings = temp_manager.apply_flag_overrides(self.general_settings, self.module_flags)
        else:
            self.general_settings = DEFAULT_GENERAL_SETTINGS.copy()
        
        # Set attributes from settings
        for key, value in self.general_settings.items():
            setattr(self, key, value)
    
    def _initialize_output_management(self) -> None:
        """Initialize output and sequential managers."""
        from model_checker.output import OutputManager, SequentialSaveManager, ConsoleInputProvider, OutputConfig
        
        # Create output configuration from CLI arguments and settings
        from ..output.config import create_output_config_from_cli_args
        config = create_output_config_from_cli_args(self.module_flags, self.general_settings)
        
        # Check if saving is enabled via new --save flag
        save_enabled = hasattr(self.module_flags, 'save') and self.module_flags.save is not None
        
        # Check if we're only generating a notebook (no other formats)
        only_notebook = (save_enabled and 
                        isinstance(self.module_flags.save, list) and 
                        self.module_flags.save == ['jupyter'])
        
        # Set save_output flag
        self.save_output = config.save_output and not only_notebook
        
        # Create sequential manager if sequential flag or setting is enabled
        self.sequential_manager = None
        sequential_enabled = (
            (hasattr(self.module_flags, 'sequential') and self.module_flags.sequential) or
            (self.general_settings and self.general_settings.get('sequential', False))
        )
        
        if config.save_output and not only_notebook and sequential_enabled:
            # Sequential mode is enabled (via flag or setting)
            # Create console input provider for production use
            input_provider = ConsoleInputProvider()
            self.sequential_manager = SequentialSaveManager(input_provider)
            # Automatically set to sequential mode without prompting
            # since batch mode would be the same as not using --sequential
            self.sequential_manager.set_mode('sequential')
        
        # Create output manager with configuration only
        self.output_manager = OutputManager(config, self.sequential_manager)
        
        # Pass module context for notebook generation
        if self.output_manager.should_save():
            self.output_manager.set_module_context(
                self.module_variables,
                self.module_path
            )
        
        # Create output directory if needed (skip for notebook-only)
        if self.output_manager.should_save():
            self.output_manager.create_output_directory()
    
    def _initialize_components(self) -> None:
        """Initialize runner, comparison, and translation components."""
        from model_checker.builder.runner import ModelRunner
        from model_checker.builder.comparison import ModelComparison
        from model_checker.builder.translation import OperatorTranslation
        
        # Create runner instance
        self.runner = ModelRunner(self)
        
        # Create comparison instance - always initialize for tests
        self.comparison = ModelComparison(self)
        
        # Create translation instance
        self.translation = OperatorTranslation()



    



    

    def _capture_and_save_output(
        self,
        example: 'BuildExample',
        example_name: str,
        theory_name: TheoryName,
        model_num: Optional[int] = None
    ) -> None:
        """Capture and save model output if save_output is enabled.
        
        Args:
            example: The BuildExample instance
            example_name: Name of the example
            theory_name: Name of the theory
            model_num: Optional model number for iterations
        """
        if not self.output_manager.should_save():
            # Just print normally if not saving
            example.print_model(example_name, theory_name)
            return
        
        # Capture and format output
        raw_output, converted_output = self._capture_model_output(example, example_name, theory_name)
        
        # Collect and prepare model data
        model_data = self._prepare_model_data(example, example_name, theory_name)
        
        # Determine display name
        display_name = f"{example_name}_model{model_num}" if model_num is not None else example_name
        
        # Format and save the output
        self._format_and_save_output(
            example, example_name, display_name, model_data, 
            converted_output, model_num
        )
    
    def _capture_model_output(
        self,
        example: 'BuildExample',
        example_name: str,
        theory_name: TheoryName
    ) -> Tuple[str, str]:
        """Capture model output and convert ANSI colors.
        
        Args:
            example: The BuildExample instance
            example_name: Name of the example
            theory_name: Name of the theory
            
        Returns:
            Tuple of (raw_output, converted_output)
        """
        from model_checker.output import ANSIToMarkdown
        import io
        import sys
        
        # Capture the output
        captured_output = io.StringIO()
        old_stdout = sys.stdout
        sys.stdout = captured_output
        
        try:
            # Print the model to our capture buffer
            example.print_model(example_name, theory_name, output=captured_output)
            raw_output = captured_output.getvalue()
        finally:
            sys.stdout = old_stdout
        
        # Also print to console so user sees output
        print(raw_output, end='')
        
        # Convert ANSI colors if present
        converter = ANSIToMarkdown()
        converted_output = converter.convert(raw_output)
        
        return raw_output, converted_output
    
    def _prepare_model_data(
        self,
        example: 'BuildExample',
        example_name: str,
        theory_name: TheoryName
    ) -> Dict[str, Any]:
        """Collect and prepare model data for saving.
        
        Args:
            example: The BuildExample instance
            example_name: Name of the example
            theory_name: Name of the theory
            
        Returns:
            Dictionary containing model data
        """
        from model_checker.output import ModelDataCollector
        
        # Collect model data
        collector = ModelDataCollector()
        model_data = collector.collect_model_data(
            example.model_structure,
            example_name,
            theory_name
        )
        
        # Add the original example data (premises, conclusions, settings)
        model_data['premises'] = example.premises
        model_data['conclusions'] = example.conclusions
        model_data['settings'] = example.example_settings
        
        # Note: semantic_theory is not added to model_data because it contains
        # non-serializable class objects. It's passed separately to notebook generation.
        
        return model_data
    
    def _format_and_save_output(
        self,
        example: 'BuildExample',
        example_name: str,
        display_name: str,
        model_data: Dict[str, Any],
        converted_output: str,
        model_num: Optional[int]
    ) -> None:
        """Format and save the output based on interactive or batch mode.
        
        Args:
            example: The BuildExample instance
            example_name: Name of the example
            display_name: Display name for the output
            model_data: Collected model data
            converted_output: ANSI-converted output
            model_num: Optional model number for iterations
        """
        from model_checker.output import MarkdownFormatter
        
        # Format the output
        formatter = MarkdownFormatter(use_colors=True)
        formatted_output = formatter.format_example(model_data, converted_output)
        
        # Handle interactive vs batch save
        if self.interactive_manager and self.interactive_manager.is_interactive():
            # Check if model found
            if example.model_structure.z3_model_status:
                # Prompt to save this model
                if self.interactive_manager.prompt_save_model(example_name):
                    # Get model number
                    model_number = model_num or self.interactive_manager.get_next_model_number(example_name)
                    # Save interactively
                    self.output_manager.save_model_sequential(
                        example_name, model_data, formatted_output, model_number
                    )
        else:
            # Batch mode - save normally
            self.output_manager.save_example(display_name, model_data, formatted_output)
    
    

