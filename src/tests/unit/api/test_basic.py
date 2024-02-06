import pytest

from officialeye import Context, Template
from officialeye.error.errors.internal import ErrInvalidState


def test_context_reenter():

    with Context() as context:
        with pytest.raises(ErrInvalidState):
            with context as _:
                pass

    with Context() as context:
        with pytest.raises(ErrInvalidState):
            with context as _:
                pass


def test_illegal_dispose():

    with pytest.raises(ErrInvalidState):
        with Context() as context:
            context.dispose()


def test_template_load():

    with Context() as context:
        template = Template(context, path="docs/assets/templates/driver_license_ru_01/driver_license_ru.yml")
        assert template.identifier == "driver_license_ru"
        assert template.name == "Driver License RU"
        assert len([k for k in template.keypoints]) == 6
        assert len([f for f in template.features]) == 15

    with Context() as context:
        template = Template(context, path="docs/assets/templates/driver_license_ru_01/driver_license_ru.yml")
        assert len([f for f in template.features]) == 15
        assert template.name == "Driver License RU"


def test_image_dimensions():

    with Context() as context:
        template = Template(context, path="docs/assets/templates/driver_license_ru_01/driver_license_ru.yml")
        img = template.get_image().load()
        h, w, _ = img.shape
        assert template.width == w
        assert template.height == h


def test_mutated_image_dimensions():
    with Context() as context:
        template = Template(context, path="docs/assets/templates/driver_license_ru_01/driver_license_ru.yml")
        img = template.get_mutated_image().load()
        h, w, _ = img.shape
        assert template.width == w
        assert template.height == h
