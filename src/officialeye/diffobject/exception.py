class DiffObjectException(Exception):
    """
    Base class for all `diffobject` exceptions.
    """

    def __init__(self, problem: str, /):
        super().__init__()

        self.problem = problem

    def __str__(self):
        return self.problem
