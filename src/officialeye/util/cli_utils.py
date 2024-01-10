import click
# noinspection PyPackageRequirements
import cv2

from officialeye.context.singleton import oe_context
from officialeye.util.logger import oe_info


def export_image(img: cv2.Mat, /, *, file_name: str = "") -> str:
    export_file_path = oe_context().allocate_file_for_export(file_name=file_name)
    cv2.imwrite(export_file_path, img)
    oe_info(f"Exported '{export_file_path}'.")
    return export_file_path


def export_and_show_image(img: cv2.Mat, /, *, file_name: str = ""):
    path = export_image(img, file_name=file_name)
    click.launch(path, locate=False)
    click.pause()
