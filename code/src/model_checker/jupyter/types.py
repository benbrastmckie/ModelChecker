"""Type definitions for the jupyter package.

This module provides comprehensive type definitions for Jupyter notebook
integration, including visualization, debugging, and interactive features.
"""

from typing import (
    TYPE_CHECKING, Any, Callable, Dict, List, Optional, Protocol, Set, Tuple,
    TypeVar, Union, Literal
)
from enum import Enum

if TYPE_CHECKING:
    import networkx as nx
    from IPython.core.display import HTML, Markdown, JSON
    from ipywidgets import Widget
    from ..models import ModelStructure
    from ..builder import BuildExample

# Type variables
T = TypeVar('T')
V = TypeVar('V')

# Core type aliases
TheoryName = str
FormulaString = str
ModelId = str
NodeId = Union[int, str]
EdgeId = Tuple[NodeId, NodeId]

# Cell and notebook types
CellType = Literal['code', 'markdown', 'raw']
CellSource = Union[str, List[str]]
OutputType = Literal['stream', 'display_data', 'execute_result', 'error']

# Visualization types
VisualizationType = Literal['graph', 'table', 'tree', 'matrix', 'text']
LayoutType = Literal['spring', 'circular', 'hierarchical', 'random']
ColorScheme = Literal['default', 'dark', 'light', 'high_contrast']

# Unicode and formatting types
UnicodeSymbol = str
LatexString = str
HTMLString = str
MarkdownString = str

# Widget types
WidgetType = Literal['button', 'dropdown', 'text', 'checkbox', 'slider']
WidgetValue = Union[str, int, float, bool, List[Any]]

# Notebook data structures
NotebookMetadata = Dict[str, Any]
CellMetadata = Dict[str, Any]
OutputData = Dict[str, Any]

# Enumerations
class DisplayFormat(Enum):
    """Output display formats."""
    HTML = "html"
    MARKDOWN = "markdown"
    LATEX = "latex"
    PLAIN = "plain"
    JSON = "json"

class VisualizationStyle(Enum):
    """Visualization rendering styles."""
    COMPACT = "compact"
    DETAILED = "detailed"
    INTERACTIVE = "interactive"
    STATIC = "static"

class DebugLevel(Enum):
    """Debug output verbosity levels."""
    NONE = 0
    ERROR = 1
    WARNING = 2
    INFO = 3
    DEBUG = 4
    TRACE = 5

# Data structures
class NotebookCell:
    """Represents a notebook cell."""
    
    def __init__(
        self,
        cell_type: CellType,
        source: CellSource,
        metadata: Optional[CellMetadata] = None,
        outputs: Optional[List[OutputData]] = None,
        execution_count: Optional[int] = None
    ) -> None:
        """Initialize notebook cell.
        
        Args:
            cell_type: Type of cell (code, markdown, raw)
            source: Cell content
            metadata: Optional cell metadata
            outputs: Optional cell outputs
            execution_count: Optional execution counter
        """
        self.cell_type = cell_type
        self.source = source if isinstance(source, list) else [source]
        self.metadata = metadata or {}
        self.outputs = outputs or []
        self.execution_count = execution_count

class GraphVisualization:
    """Configuration for graph visualization."""
    
    def __init__(
        self,
        layout: LayoutType = 'spring',
        node_size: int = 500,
        node_color: str = 'lightblue',
        edge_color: str = 'gray',
        with_labels: bool = True,
        font_size: int = 10,
        figsize: Tuple[int, int] = (10, 8)
    ) -> None:
        """Initialize graph visualization config.
        
        Args:
            layout: Graph layout algorithm
            node_size: Size of nodes
            node_color: Color of nodes
            edge_color: Color of edges
            with_labels: Whether to show labels
            font_size: Font size for labels
            figsize: Figure size as (width, height)
        """
        self.layout = layout
        self.node_size = node_size
        self.node_color = node_color
        self.edge_color = edge_color
        self.with_labels = with_labels
        self.font_size = font_size
        self.figsize = figsize

# Protocol definitions
class TheoryAdapter(Protocol):
    """Protocol for theory-specific adapters."""
    
    theory_name: str
    
    def model_to_graph(self, model: 'ModelStructure') -> 'nx.DiGraph':
        """Convert model to graph representation.
        
        Args:
            model: Model structure to convert
            
        Returns:
            NetworkX directed graph
        """
        ...
    
    def format_formula(self, formula: FormulaString) -> str:
        """Format formula for display.
        
        Args:
            formula: Formula string to format
            
        Returns:
            Formatted formula string
        """
        ...
    
    def format_model(self, model: 'ModelStructure') -> HTMLString:
        """Format model for HTML display.
        
        Args:
            model: Model to format
            
        Returns:
            HTML representation
        """
        ...

class NotebookBuilder(Protocol):
    """Protocol for notebook builders."""
    
    def add_markdown_cell(self, content: str) -> None:
        """Add markdown cell to notebook.
        
        Args:
            content: Markdown content
        """
        ...
    
    def add_code_cell(self, code: str, outputs: Optional[List[OutputData]] = None) -> None:
        """Add code cell to notebook.
        
        Args:
            code: Python code
            outputs: Optional outputs
        """
        ...
    
    def build(self) -> Dict[str, Any]:
        """Build final notebook structure.
        
        Returns:
            Notebook as dictionary
        """
        ...

class DisplayFormatter(Protocol):
    """Protocol for display formatters."""
    
    def format(self, obj: Any, format_type: DisplayFormat) -> str:
        """Format object for display.
        
        Args:
            obj: Object to format
            format_type: Target format
            
        Returns:
            Formatted string
        """
        ...

class ModelVisualizer(Protocol):
    """Protocol for model visualizers."""
    
    def visualize(
        self,
        model: 'ModelStructure',
        style: VisualizationStyle = VisualizationStyle.DETAILED
    ) -> Union['HTML', 'Markdown']:
        """Create model visualization.
        
        Args:
            model: Model to visualize
            style: Visualization style
            
        Returns:
            IPython display object
        """
        ...

# Callback types
FormulaFormatter = Callable[[FormulaString], str]
ModelProcessor = Callable[['ModelStructure'], Any]
CellProcessor = Callable[[NotebookCell], NotebookCell]
OutputFormatter = Callable[[Any], OutputData]

# Result types
ConversionResult = Tuple[bool, Optional[Dict[str, Any]], Optional[str]]
ValidationResult = Tuple[bool, Optional[str]]
VisualizationResult = Union['HTML', 'Markdown', str]

# UI Builder types
class WidgetConfig:
    """Configuration for interactive widgets."""
    
    def __init__(
        self,
        widget_type: WidgetType,
        description: str = "",
        value: Optional[WidgetValue] = None,
        options: Optional[List[Any]] = None,
        min_value: Optional[Union[int, float]] = None,
        max_value: Optional[Union[int, float]] = None,
        step: Optional[Union[int, float]] = None,
        disabled: bool = False
    ) -> None:
        """Initialize widget configuration.
        
        Args:
            widget_type: Type of widget
            description: Widget label
            value: Initial value
            options: Options for dropdown
            min_value: Minimum for slider
            max_value: Maximum for slider
            step: Step for slider
            disabled: Whether widget is disabled
        """
        self.widget_type = widget_type
        self.description = description
        self.value = value
        self.options = options
        self.min_value = min_value
        self.max_value = max_value
        self.step = step
        self.disabled = disabled

# Exception types
ErrorContext = Dict[str, Any]
ErrorSuggestion = str

# Debug types
DebugInfo = Dict[str, Any]
DebugCallback = Callable[[str, DebugLevel], None]

# Interactive types
InteractionEvent = Dict[str, Any]
EventHandler = Callable[[InteractionEvent], None]

# Unicode conversion maps
UnicodeMap = Dict[str, UnicodeSymbol]
LatexMap = Dict[str, LatexString]