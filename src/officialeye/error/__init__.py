class OEError(Exception):
    """
    Base class for all officialeye-related errors.
    """

    def __init__(self, module: str, code: int, code_text: str, while_text: str, problem_text: str, /, *,
                 is_regular: bool = False):
        super().__init__()

        assert code != 0

        self.code = code
        self.module = module
        self.code_text = code_text
        self.while_text = while_text
        self.problem_text = problem_text

        # regular errors are those that can happen if the tool is configured correctly, but has been provided invalid input
        # here, 'input' should be narrowly understood as end user input, not as the tool users' input
        # an example of such an input would be the image provided as a basis for the analysis
        # on the other hand, the template configuration file does not count as end user input
        self.is_regular = is_regular

        self._causes = []

    def add_cause(self, cause: Exception, /):
        self._causes.append(cause)

    def serialize(self) -> dict:

        causes = [
            cause.serialize()
            for cause in self._causes
        ]

        return {
            "code": self.code,
            "code_text": self.code_text,
            "module": self.module,
            "while_text": self.while_text,
            "problem_text": self.problem_text,
            "is_regular": self.is_regular,
            "causes": causes
        }


ERR_MODULE_IO = "io"
ERR_MODULE_MATCHING = "matching"
ERR_MODULE_SUPERVISION = "supervision"
ERR_MODULE_TEMPLATE = "template"
