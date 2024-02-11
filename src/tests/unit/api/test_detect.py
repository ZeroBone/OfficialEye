from officialeye import Context, IImage, Image, ISupervisionResult, Template
from officialeye.detection import detect


def test_detect():

    with Context() as context:
        template = Template(context, path="docs/assets/templates/driver_license_ru_01/driver_license_ru.yml")

        image: IImage = Image(context, path="docs/assets/templates/driver_license_ru_01/examples/01.jpg")
        assert isinstance(image, IImage)

        result = detect(context, template, target=image)

        assert isinstance(result, ISupervisionResult)
