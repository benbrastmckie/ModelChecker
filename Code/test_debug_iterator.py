"""Debug script to trace iterator constraint generation."""

import logging
import sys

# Configure detailed logging
logging.basicConfig(level=logging.DEBUG, format='[%(name)s] %(message)s')

# Test case
from model_checker.theory_lib.logos import get_theory

premises = ['A']
conclusions = []
iterate = 2
settings = {
    'N': 2,
    'contingent': False,
    'non_null': True,
    'non_empty': True,
    'max_time': 10
}
semantic_theory = get_theory()

# Add debug logging to semantic
class DebugProxy:
    def __init__(self, target, name):
        self.target = target
        self.name = name
    
    def __call__(self, *args, **kwargs):
        result = self.target(*args, **kwargs)
        print(f"[DEBUG] {self.name}({args}) = {result}")
        return result

# Patch the theory
original_semantics = semantic_theory["semantics"]

class DebugSemantics(original_semantics):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        # Wrap verify/falsify
        if hasattr(self, 'verify'):
            self.verify = DebugProxy(self.verify, 'verify')
        if hasattr(self, 'falsify'):
            self.falsify = DebugProxy(self.falsify, 'falsify')

semantic_theory["semantics"] = DebugSemantics