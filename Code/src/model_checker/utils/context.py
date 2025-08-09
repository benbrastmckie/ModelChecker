"""
Z3 context management utilities.

This module provides centralized management of Z3 solver contexts to ensure
proper isolation between different solver instances.
"""


class Z3ContextManager:
    """Provides centralized management of Z3 solver contexts.
    
    This class ensures proper isolation between different solver instances by explicitly
    resetting the Z3 global context when needed. It implements a fail-fast approach
    and enforces deterministic behavior by preventing state leakage between examples.
    """
    
    @staticmethod
    def reset_context():
        """Explicitly reset the Z3 global context.
        
        This method forces Z3 to create a fresh context for the next solver instance,
        ensuring complete isolation between different examples.
        
        Note: Z3 stores its context in either '_main_ctx' or 'main_ctx' depending on
        the Z3 version. This method handles both cases for maximum compatibility.
        """
        import z3
        
        # Handle both possible attribute names for Z3 context
        if hasattr(z3, '_main_ctx'):
            # Reset the context completely
            z3._main_ctx = None
            
        elif hasattr(z3, 'main_ctx'):
            z3.main_ctx = None
            
        # Try to clear other Z3 caches that might persist
        if hasattr(z3, 'clear_parser_cache'):
            z3.clear_parser_cache()
            
        # Re-import z3 to use the new context
        import importlib
        importlib.reload(z3)