class OEError(Exception):

    def __init__(self, module: str, code_num: int, code_text: str, error_text: str, problem_text: str, /):
        super().__init__()

        assert code_num != 0

        self.code_num = code_num
        self.module = module
        self.code_text = code_text
        self.error_text = error_text
        self.problem_text = problem_text


ERR_MODULE_IO = "io"
ERR_MODULE_MATCHING = "matching"
ERR_MODULE_SUPERVISION = "supervision"
ERR_MODULE_TEMPLATE = "template"
