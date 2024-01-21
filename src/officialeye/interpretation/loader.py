from typing import Dict

from officialeye.context.context import Context
from officialeye.error.errors.template import ErrTemplateInvalidInterpretation
from officialeye.interpretation.method import InterpretationMethod
from officialeye.interpretation.methods.file_temp import FileTempMethod
from officialeye.interpretation.methods.ocr_tesseract import TesseractMethod


def load_interpretation_method(context: Context, method_id: str, config_dict: Dict[str, any], /) -> InterpretationMethod:

    if method_id == TesseractMethod.METHOD_ID:
        return TesseractMethod(context, config_dict)

    if method_id == FileTempMethod.METHOD_ID:
        return FileTempMethod(context, config_dict)

    raise ErrTemplateInvalidInterpretation(
        f"while loading interpretation method '{method_id}'.",
        "Unknown interpretation method id."
    )
