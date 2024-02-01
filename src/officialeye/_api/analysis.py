from officialeye._api.context import Context
from officialeye._api.image import Image
from officialeye._api.template.template import Template


def analyze(*templates: Template, target: Image, interpretation_target: Image | None = None):

    for template in templates:
        template.load()
