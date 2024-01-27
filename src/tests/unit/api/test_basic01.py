import pytest

from officialeye.api.context import Context
from officialeye.api.error.errors.internal import ErrInvalidState
from officialeye.api.template.template import Template


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


def test_template_create():

    with Context() as context:

        template = Template(context, path="docs/assets/templates/driver_license_ru_01/driver_license_ru.yml")
