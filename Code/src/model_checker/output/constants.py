"""Constants for output package configuration."""

# Output format types
FORMAT_MARKDOWN = 'markdown'
FORMAT_JSON = 'json'
FORMAT_NOTEBOOK = 'notebook'

# Default formats to generate
DEFAULT_FORMATS = [FORMAT_MARKDOWN, FORMAT_JSON, FORMAT_NOTEBOOK]

# File extensions
EXTENSIONS = {
    FORMAT_MARKDOWN: 'md',
    FORMAT_JSON: 'json',
    FORMAT_NOTEBOOK: 'ipynb'
}

# Output modes
MODE_BATCH = 'batch'
MODE_SEQUENTIAL = 'sequential'
MODE_INTERACTIVE = 'interactive'

# Sequential file options
SEQUENTIAL_SINGLE = 'single'
SEQUENTIAL_MULTIPLE = 'multiple'

# Default output filenames
DEFAULT_MARKDOWN_FILE = 'EXAMPLES.md'
DEFAULT_JSON_FILE = 'MODELS.json'
DEFAULT_NOTEBOOK_FILE = 'NOTEBOOK.ipynb'
DEFAULT_SUMMARY_FILE = 'summary.json'

# Notebook metadata - DEPRECATED (moved to notebook package)
# NOTEBOOK_KERNEL = 'python3'
# NOTEBOOK_LANGUAGE = 'python'
# NOTEBOOK_FORMAT_VERSION = 4
# NOTEBOOK_FORMAT_MINOR = 5

# Output directory settings
OUTPUT_DIR_PREFIX = 'output_'
OUTPUT_DIR_TIMESTAMP_FORMAT = '%Y%m%d_%H%M%S'