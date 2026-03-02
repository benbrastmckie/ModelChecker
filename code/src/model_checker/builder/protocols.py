"""Protocol definitions for builder package components.

This module defines interfaces (protocols) for builder components to enable
better type checking, dependency injection, and testing.
"""

from typing import Protocol, Any, Dict, List, Tuple, Optional

class IModuleLoader(Protocol):
    """Interface for module loading functionality."""
    
    def load_module(self) -> Any:
        """Load a Python module from a file path.
        
        Returns:
            module: The loaded Python module
            
        Raises:
            ImportError: If the module cannot be loaded
        """
        ...
    
    def load_attribute(self, module: Any, attr_name: str) -> Any:
        """Load a required attribute from a module with validation.
        
        Args:
            module: The module to load from
            attr_name: Name of the attribute to load
            
        Returns:
            Any: The loaded attribute
            
        Raises:
            ImportError: If the attribute is missing or invalid
        """
        ...

class IModelRunner(Protocol):
    """Interface for model checking execution."""
    
    
    def run_examples(self, examples: Dict[str, List]) -> None:
        """Run model checking examples.
        
        Args:
            examples: Dictionary mapping example names to example cases
        """
        ...
    
    
    def process_example(
        self, 
        example_name: str, 
        example_case: List, 
        theory_name: str, 
        semantic_theory: Dict[str, Any]
    ) -> Any:
        """Process a single example with model checking.
        
        Args:
            example_name: Name of the example
            example_case: Example case data
            theory_name: Name of the theory
            semantic_theory: Theory configuration
            
        Returns:
            Any: The processed example result
        """
        ...

class IComparison(Protocol):
    """Interface for theory comparison functionality."""
    
    
    def run_comparison(self) -> None:
        """Run comparison across all theories and examples."""
        ...
    
    
    def compare_semantics(self, example_theory_tuples: List[Tuple]) -> List[Tuple]:
        """Compare semantic theories for a single example.
        
        Args:
            example_theory_tuples: List of (theory_name, semantic_theory, example_case)
            
        Returns:
            List of (theory_name, max_N) tuples sorted by performance
        """
        ...

class ITranslation(Protocol):
    """Interface for operator translation functionality."""
    
    
    def translate(self, example_case: List, dictionary: Dict[str, str]) -> List:
        """Translate operators in an example case using a dictionary.
        
        Args:
            example_case: The example case to translate
            dictionary: Mapping of old operators to new operators
            
        Returns:
            List: Translated example case
        """
        ...

class IOutputManager(Protocol):
    """Interface for output management functionality."""
    
    
    def should_save(self) -> bool:
        """Check if output should be saved.
        
        Returns:
            bool: True if output should be saved
        """
        ...
    
    
    def create_output_directory(self) -> None:
        """Create the output directory if needed."""
        ...
    
    
    def save_output(self, content: str, filename: str) -> None:
        """Save output content to a file.
        
        Args:
            content: The content to save
            filename: The filename to save to
        """
        ...

class IInteractiveManager(Protocol):
    """Interface for interactive session management."""
    
    
    def is_interactive(self) -> bool:
        """Check if currently in interactive mode.
        
        Returns:
            bool: True if in interactive mode
        """
        ...
    
    
    def set_mode(self, mode: str) -> None:
        """Set the interactive mode.
        
        Args:
            mode: The mode to set ('interactive' or 'batch')
        """
        ...
    
    
    def prompt_save_mode(self) -> None:
        """Prompt user to select save mode."""
        ...

class IValidator(Protocol):
    """Interface for validation functionality."""
    
    
    def validate_semantic_theory(self, semantic_theory: Any) -> Tuple:
        """Validate a semantic theory structure.
        
        Args:
            semantic_theory: The theory to validate
            
        Returns:
            Tuple: Extracted and validated components
            
        Raises:
            ValidationError: If validation fails
        """
        ...
    
    
    def validate_example_case(self, example_case: Any) -> Tuple:
        """Validate an example case structure.
        
        Args:
            example_case: The example case to validate
            
        Returns:
            Tuple: Extracted and validated components
            
        Raises:
            ValidationError: If validation fails
        """
        ...

class IProjectGenerator(Protocol):
    """Interface for project generation functionality."""
    
    
    def generate(self, project_name: str) -> str:
        """Generate a new project from a template.
        
        Args:
            project_name: Name for the new project
            
        Returns:
            str: Path to the generated project directory
        """
        ...
    
    
    def create_template_content(self, theory_name: str) -> str:
        """Create template content for a theory.
        
        Args:
            theory_name: Name of the theory to create template for
            
        Returns:
            str: Template content
        """
        ...

class IBuildModule(Protocol):
    """Interface for the main build module functionality."""
    
    def get_semantic_theories(self) -> Dict[str, Any]:
        """Get the loaded semantic theories.
        
        Returns:
            Dict: Mapping of theory names to theory implementations
        """
        ...
    
    def get_example_range(self) -> Dict[str, List]:
        """Get the loaded example range.
        
        Returns:
            Dict: Mapping of example names to example cases
        """
        ...
    
    
    def run_model_check(self) -> None:
        """Run the model checking process."""
        ...
    
    
    def run_comparison(self) -> None:
        """Run theory comparison."""
        ...

class ISerializable(Protocol):
    """Interface for objects that can be serialized for multiprocessing."""
    
    
    def serialize(self) -> Dict[str, Any]:
        """Serialize the object to a dictionary.
        
        Returns:
            Dict: Serialized object data
        """
        ...
    
    def deserialize(self, data: Dict[str, Any]) -> 'ISerializable':
        """Deserialize an object from a dictionary.
        
        Args:
            data: Serialized object data
            
        Returns:
            ISerializable: The deserialized object
        """
        ...

class IProgressTracker(Protocol):
    """Interface for progress tracking functionality."""
    
    
    def start_model_search(self, model_number: int, start_time: float = None) -> None:
        """Start tracking a model search.
        
        Args:
            model_number: The model number being searched
            start_time: Optional start time for the search
        """
        ...
    
    
    def model_checked(self) -> None:
        """Mark that a model check has completed."""
        ...
    
    
    def complete_model_search(self, found: bool) -> None:
        """Complete a model search.
        
        Args:
            found: Whether a model was found
        """
        ...
    
    
    def finish(self) -> None:
        """Finish progress tracking and cleanup."""
        ...

# Type aliases for common data structures
SemanticTheory = Dict[str, Any]
ExampleCase = List[Any]  # [premises, conclusions, settings]
Settings = Dict[str, Any]
TheoryTuple = Tuple[str, SemanticTheory, ExampleCase]  # (theory_name, semantic_theory, example_case)
ComparisonResult = Tuple[str, int]  # (theory_name, max_N)

# Factory Protocol for dependency injection
class IComponentFactory(Protocol):
    """Interface for creating builder components."""
    
    
    def create_loader(self, module_name: str, module_path: str) -> IModuleLoader:
        """Create a module loader.
        
        Args:
            module_name: Name of the module
            module_path: Path to the module file
            
        Returns:
            IModuleLoader: The created loader
        """
        ...
    
    
    def create_runner(self, build_module: IBuildModule) -> IModelRunner:
        """Create a model runner.
        
        Args:
            build_module: The build module to run with
            
        Returns:
            IModelRunner: The created runner
        """
        ...
    
    
    def create_comparison(self, build_module: IBuildModule) -> IComparison:
        """Create a comparison instance.
        
        Args:
            build_module: The build module to compare with
            
        Returns:
            IComparison: The created comparison
        """
        ...
    
    
    def create_translation(self) -> ITranslation:
        """Create a translation instance.
        
        Returns:
            ITranslation: The created translation
        """
        ...
    
    
    def create_output_manager(
        self,
        save_output: bool,
        mode: str,
        sequential_files: str,
        interactive_manager: Optional[IInteractiveManager] = None
    ) -> IOutputManager:
        """Create an output manager.
        
        Args:
            save_output: Whether to save output
            mode: Output mode
            sequential_files: Sequential files setting
            interactive_manager: Optional interactive manager
            
        Returns:
            IOutputManager: The created output manager
        """
        ...
