from difflib import SequenceMatcher

from officialeye import Context, IImage, IInterpretationResult, Image, ISupervisionResult, Template
from officialeye.detection import detect


def sequence_similarity_measure(str_1: str, str_2: str, /) -> float:
    return SequenceMatcher(None, str_1, str_2).ratio()


def test_driver_license_ru():

    with Context() as context:
        template = Template(context, path="docs/assets/templates/driver_license_ru_01/driver_license_ru.yml")

        image: IImage = Image(context, path="docs/assets/templates/driver_license_ru_01/examples/01.jpg")
        assert isinstance(image, IImage)

        result = detect(context, template, target=image)

        assert isinstance(result, ISupervisionResult)
        assert result.template.identifier == "driver_license_ru"

        interpretation: IInterpretationResult = result.interpret(target=image)
        assert isinstance(interpretation, IInterpretationResult)

        feature_interpretation_dict = {}

        for feature in result.template.features:
            feature_interpretation_dict[feature.identifier] = interpretation.get_feature_interpretation(feature)

        assert sequence_similarity_measure(feature_interpretation_dict["last_name_ru"], "СУРГУТСКИЙ") >= 0.6
        assert sequence_similarity_measure(feature_interpretation_dict["name_ru"], "ИГОРЬ ВЛАДИСЛАВОВИЧ") >= 0.6
        assert sequence_similarity_measure(feature_interpretation_dict["birthday"], "16.10.1986") >= 0.8
