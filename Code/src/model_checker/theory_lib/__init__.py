"""Model checker theory library."""

# Initialize empty module attributes
default = None
exclusion = None
imposition = None

__all__ = [
    'default',
    'exclusion',
    'imposition'
]

def __getattr__(name):
    global default, exclusion, imposition
    
    if name == 'default':
        from . import default as mod
        default = mod
        return default
    elif name == 'exclusion':
        from . import exclusion as mod
        exclusion = mod
        return exclusion
    elif name == 'imposition':
        from . import imposition as mod
        imposition = mod
        return imposition
    raise AttributeError(f"module '{__name__}' has no attribute '{name}'")
