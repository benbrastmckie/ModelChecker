"""Output strategy implementations for different save modes."""

from .base import IOutputStrategy
from .batch import BatchOutputStrategy
from .sequential import SequentialOutputStrategy
from .prompted import PromptedOutputStrategy

__all__ = [
    'IOutputStrategy',
    'BatchOutputStrategy',
    'SequentialOutputStrategy',
    'PromptedOutputStrategy'
]