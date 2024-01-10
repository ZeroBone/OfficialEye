from typing import List

# noinspection PyPackageRequirements
import cv2

from officialeye.util.cli_utils import export_image


class DebugImage:

    def __init__(self, img: cv2.Mat, name: str, /):
        self.img = img
        self.name = name

    def get_export_filename(self, image_id: int) -> str:

        if self.name == "":
            return "%03d.png" % image_id

        return "%03d_%s.png" % (image_id, self.name)


class DebugContainer:

    def __init__(self):
        self._images: List[DebugImage] = []

    def add_image(self, img: cv2.Mat, /, *, name: str = ""):
        self._images.append(DebugImage(img, name))

    def export(self):

        for image_id, image in enumerate(self._images):
            export_filename = image.get_export_filename(image_id)
            export_image(image.img, file_name=export_filename)
