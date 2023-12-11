import os
import shutil
from typing import List

import click
import cv2

from officialeye.meta import APPLICATION_NAME


class DebugImage:

    def __init__(self, img: cv2.Mat, name: str, /):
        self.img = img
        self.name = name

    def get_export_filename(self, image_id: int) -> str:

        if self.name == "":
            return "%03d.png" % image_id

        return "%03d_%s.png" % (image_id, self.name)


class DebugInformationContainer:

    def __init__(self):
        self._images: List[DebugImage] = []

    def add_image(self, img: cv2.Mat, /, *, name: str = ""):
        self._images.append(DebugImage(img, name))

    def export(self):

        debug_directory = os.path.join(click.get_app_dir(APPLICATION_NAME), "debug")

        if os.path.exists(debug_directory):
            shutil.rmtree(debug_directory)
            # os.rmdir(debug_directory)

        os.makedirs(debug_directory, exist_ok=True)

        click.secho(f"Export directory: '{debug_directory}'.", bg="yellow", bold=True)

        for image_id, image in enumerate(self._images):
            export_filename = image.get_export_filename(image_id)
            export_path = os.path.join(debug_directory, export_filename)
            cv2.imwrite(export_path, image.img)
            click.secho(f"Exported '{export_filename}'.", fg="yellow", bold=True)
