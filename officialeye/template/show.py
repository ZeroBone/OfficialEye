from officialeye.context.singleton import oe_context
from officialeye.template.template import Template


def do_show(template: Template):
    img = template.show()
    oe_context().io_driver.output_show_result(template, img)
