from officialeye.error import OEError
from officialeye.util.logger import oe_error, oe_debug


def oe_error_print_error(error: OEError):
    oe_error(f"Error {error.code} in module {error.module}: {error.code_text}")
    oe_error(f"Error occurred {error.while_text}")
    oe_error(f"Problem: {error.problem_text}")


def oe_error_print_debug(error: OEError):
    oe_debug(f"Error {error.code} in module {error.module}: {error.code_text}")
    oe_debug(f"Error occurred {error.while_text}")
    oe_debug(f"Problem: {error.problem_text}")
