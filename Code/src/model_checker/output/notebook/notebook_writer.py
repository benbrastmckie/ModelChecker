"""Memory-efficient notebook writer for streaming JSON output.

This module provides a NotebookWriter class that streams notebook JSON
directly to a file, maintaining constant memory usage regardless of
the number of examples being generated.
"""

import json
from typing import Dict, Any


class NotebookWriter:
    """Memory-efficient notebook writer that streams JSON directly to file.
    
    This writer creates valid Jupyter notebook JSON by streaming cells
    one at a time to the output file, avoiding the need to hold the
    entire notebook structure in memory.
    """
    
    def __init__(self, output_path: str):
        """Initialize the notebook writer.
        
        Args:
            output_path: Path where the notebook JSON will be written
        """
        self.output_path = output_path
        self.cell_count = 0
        self.file = None
        
    def __enter__(self):
        """Enter context manager - open file and write notebook header."""
        self.file = open(self.output_path, 'w', encoding='utf-8')
        self._write_notebook_header()
        return self
        
    def write_cell(self, cell: Dict[str, Any]):
        """Write a single cell to the notebook JSON stream.
        
        Args:
            cell: Cell dictionary following Jupyter notebook cell format
        """
        if self.cell_count > 0:
            self.file.write(',\n')
        
        # Ensure cell has required structure
        if 'metadata' not in cell:
            cell['metadata'] = {}
        
        # Write cell JSON with proper indentation
        json.dump(cell, self.file, indent=1, ensure_ascii=False)
        self.cell_count += 1
        
    def __exit__(self, exc_type, exc_val, exc_tb):
        """Exit context manager - write notebook footer and close file."""
        self._write_notebook_footer()
        self.file.close()
        
    def _write_notebook_header(self):
        """Write the opening JSON structure for the notebook."""
        # Write the beginning of the notebook structure
        self.file.write('{\n')
        self.file.write(' "cells": [\n')
        
    def _write_notebook_footer(self):
        """Write the closing JSON structure for the notebook."""
        # Close cells array and add metadata
        self.file.write('\n ],\n')
        self.file.write(' "metadata": {\n')
        self.file.write('  "kernelspec": {\n')
        self.file.write('   "display_name": "Python 3 (ipykernel)",\n')
        self.file.write('   "language": "python",\n')
        self.file.write('   "name": "python3"\n')
        self.file.write('  },\n')
        self.file.write('  "language_info": {\n')
        self.file.write('   "name": "python",\n')
        self.file.write('   "version": "3.12.0"\n')
        self.file.write('  }\n')
        self.file.write(' },\n')
        self.file.write(' "nbformat": 4,\n')
        self.file.write(' "nbformat_minor": 4\n')
        self.file.write('}\n')