# --------------------------------------------------------------------
import os

__all__ = ['resource']

# --------------------------------------------------------------------
def resource(*components):
    return os.path.join(os.getcwd(), 'data', *components)
