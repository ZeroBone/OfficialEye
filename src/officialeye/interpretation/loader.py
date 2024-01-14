from typing import Dict

from officialeye.error.errors.template import ErrTemplateInvalidInterpretation
from officialeye.interpretation import InterpretationMethod
from officialeye.interpretation.interpretations.tesseract import TesseractInterpretationMethod


def load_interpretation_method(method_id: str, config_dict: Dict[str, any], /) -> InterpretationMethod:

    if method_id == TesseractInterpretationMethod.METHOD_ID:
        return TesseractInterpretationMethod(config_dict)

    raise ErrTemplateInvalidInterpretation(
        f"while loading interpretation method '{method_id}'.",
        "Unknown interpretation method id."
    )
