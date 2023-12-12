import click
# noinspection PyPackageRequirements
import cv2

from officialeye.context import oe_context


def export_image(img: cv2.Mat, /, *, debug: bool = False, file_name: str = "") -> str:
    export_file_path = oe_context().allocate_file_for_export(debug=debug, file_name=file_name)
    cv2.imwrite(export_file_path, img)
    click.secho(f"Success. Exported '{export_file_path}'.", bg="yellow" if debug else "green", bold=True)
    return export_file_path


def export_and_show_image(img: cv2.Mat, /, *, debug: bool = False, file_name: str = ""):
    path = export_image(img, debug=debug, file_name=file_name)
    click.launch(path, locate=False)
    click.pause()
