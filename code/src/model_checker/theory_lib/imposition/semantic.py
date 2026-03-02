"""
Imposition theory semantic module (compatibility wrapper).

This module maintains backward compatibility by re-exporting classes
from the new modular semantic package structure.
"""

# Import from the new modular structure
from .semantic import (
    ImpositionSemantics,
    ImpositionModelStructure,
    safe_bitvec_as_long,
    format_imposition_relation,
    group_impositions_by_world,
    extract_unique_states,
    validate_imposition_triple,
    sort_imposition_relations,
    filter_valid_impositions,
)

# Maintain backward compatibility
__all__ = [
    'ImpositionSemantics',
    'ImpositionModelStructure',
    'safe_bitvec_as_long',
    'format_imposition_relation',
    'group_impositions_by_world',
    'extract_unique_states',
    'validate_imposition_triple',
    'sort_imposition_relations',
    'filter_valid_impositions',
]