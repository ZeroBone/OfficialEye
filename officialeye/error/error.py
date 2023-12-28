class OEError(Exception):

    def __init__(self, module: str, code: int, code_text: str, while_text: str, problem_text: str, /):
        super().__init__()

        assert code != 0

        self.code = code
        self.module = module
        self.code_text = code_text
        self.while_text = while_text
        self.problem_text = problem_text

    def serialize(self) -> dict:
        return {
            "code": self.code,
            "code_text": self.code_text,
            "module": self.module,
            "while_text": self.while_text,
            "problem_text": self.problem_text
        }


ERR_MODULE_IO = "io"
ERR_MODULE_MATCHING = "matching"
ERR_MODULE_SUPERVISION = "supervision"
ERR_MODULE_TEMPLATE = "template"
