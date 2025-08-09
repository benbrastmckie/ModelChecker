"""
Utils subpackage for the ModelChecker framework.

This package will replace the original utils.py module.
"""

# Phase 2.2 - Z3 Context Management
from .context import Z3ContextManager

# Phase 2.3 - Expression Parsing
from .parsing import parse_expression, op_left_right

# Phase 2.4 - Bitvector Operations
from .bitvector import (
    binary_bitvector, int_to_binary, index_to_substate,
    bitvec_to_substates, bitvec_to_worldstate
)

# Phase 2.5 - Z3 Helpers
from .z3_helpers import ForAll, Exists

# Phase 2.6 - Additional Utilities
from .formatting import pretty_set_print, not_implemented_string, flatten
from .version import (
    get_model_checker_version, get_theory_version,
    check_theory_compatibility, get_license_template
)
from .api import get_example, get_theory
from .testing import (
    run_test, run_enhanced_test, run_strategy_test, TestResultData
)

__all__ = [
    # Z3 Context Management
    'Z3ContextManager',
    # Expression Parsing
    'parse_expression',
    'op_left_right',
    # Bitvector Operations
    'binary_bitvector',
    'int_to_binary', 
    'index_to_substate',
    'bitvec_to_substates',
    'bitvec_to_worldstate',
    # Z3 Helpers
    'ForAll',
    'Exists',
    # Formatting
    'pretty_set_print',
    'not_implemented_string',
    'flatten',
    # Version Management
    'get_model_checker_version',
    'get_theory_version',
    'check_theory_compatibility',
    'get_license_template',
    # API Functions
    'get_example',
    'get_theory',
    # Testing Functions
    'run_test',
    'run_enhanced_test',
    'run_strategy_test',
    'TestResultData',
]