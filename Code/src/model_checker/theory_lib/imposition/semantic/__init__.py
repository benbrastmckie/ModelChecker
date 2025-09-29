"""
Imposition theory semantic module.

This package provides the core semantic classes for imposition theory,
split into focused modules while maintaining backward compatibility.

Classes:
    ImpositionSemantics: Core semantics implementation
    ImpositionModelStructure: Model structure with imposition relations
"""

from .core import ImpositionSemantics
from .model import ImpositionModelStructure
from .helpers import (
    safe_bitvec_as_long,
    format_imposition_relation,
    group_impositions_by_world,
    extract_unique_states,
    validate_imposition_triple,
    sort_imposition_relations,
    filter_valid_impositions,
)

# Export all public classes and functions
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