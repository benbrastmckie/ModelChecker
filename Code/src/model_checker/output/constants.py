"""Output constants."""

# Output format types
FORMAT_MARKDOWN = 'markdown'
FORMAT_JSON = 'json'
FORMAT_NOTEBOOK = 'notebook'

# Default formats to generate
DEFAULT_FORMATS = [FORMAT_MARKDOWN, FORMAT_JSON]

# File extensions
EXTENSIONS = {
    FORMAT_MARKDOWN: 'md',
    FORMAT_JSON: 'json',
    FORMAT_NOTEBOOK: 'ipynb'
}

# Default output filenames
DEFAULT_MARKDOWN_FILE = 'EXAMPLES.md'
DEFAULT_JSON_FILE = 'MODELS.json'
DEFAULT_NOTEBOOK_FILE = 'NOTEBOOK.ipynb'
DEFAULT_SUMMARY_FILE = 'summary.json'

# Output directory settings
OUTPUT_DIR_PREFIX = 'output_'
OUTPUT_DIR_TIMESTAMP_FORMAT = '%Y%m%d_%H%M%S'