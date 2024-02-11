from officialeye._internal.context.singleton import get_internal_context
from officialeye._internal.template.external_template import ExternalTemplate
from officialeye._internal.template.schema.loader import load_template


def template_load(template_path: str, /, **kwargs) -> ExternalTemplate:

    with get_internal_context().setup(**kwargs):
        template = load_template(template_path)
        return ExternalTemplate(template)
