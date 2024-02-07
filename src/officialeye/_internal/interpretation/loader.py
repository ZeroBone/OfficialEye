from typing import Dict

from officialeye.error.errors.template import ErrTemplateInvalidInterpretation
from officialeye._internal.interpretation.method import InterpretationMethod
from officialeye._internal.interpretation.methods.file import FileMethod
from officialeye._internal.interpretation.methods.file_temp import FileTempMethod
from officialeye._internal.interpretation.methods.ocr_tesseract import TesseractMethod


def load_interpretation_method(method_id: str, config_dict: Dict[str, any], /) -> InterpretationMethod:

    # TODO: get rid of this method by abstracting it out similar to how it was done with mutator loading

    if method_id == TesseractMethod.METHOD_ID:
        return TesseractMethod(config_dict)

    if method_id == FileTempMethod.METHOD_ID:
        return FileTempMethod(config_dict)

    if method_id == FileMethod.METHOD_ID:
        return FileMethod(config_dict)

    raise ErrTemplateInvalidInterpretation(
        f"while loading interpretation method '{method_id}'.",
        "Unknown interpretation method id."
    )
