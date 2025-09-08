"""Helper functions for Jupyter notebooks."""

import sys
from io import StringIO


def print_model(model_structure, capture=False):
    """
    Print a model structure, showing the interpreted values.
    
    This actually calls print_input_sentences to show the model values,
    not the raw Z3 model (which is what print_model does internally).
    
    Args:
        model_structure: The model structure to print
        capture: If True, capture and return the output as a string
    
    Returns:
        If capture=True, returns the output as a string
        Otherwise prints directly
    """
    if capture:
        output = StringIO()
        model_structure.print_input_sentences(output)
        result = output.getvalue()
        output.close()
        return result
    else:
        model_structure.print_input_sentences(sys.stdout)


def print_all(model_structure, capture=False):
    """
    Print all model information (input, constraints, model).
    
    Args:
        model_structure: The model structure to print
        capture: If True, capture and return the output as a string
    """
    if capture:
        output = StringIO()
        model_structure.print_all(output)
        result = output.getvalue()
        output.close()
        return result
    else:
        model_structure.print_all(sys.stdout)
