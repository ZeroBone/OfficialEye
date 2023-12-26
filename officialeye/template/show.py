from officialeye.io.driver_singleton import oe_io_driver
from officialeye.template.template import Template


def do_show(template: Template):
    img = template.show()
    oe_io_driver().output_show_result(template, img)
