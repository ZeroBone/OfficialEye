# needed to not break type annotations if we are not in type checking mode
from __future__ import annotations

import os
import tempfile
from typing import List, Dict, Union
from typing import TYPE_CHECKING

import click
import cv2
import z3

from officialeye._internal.error.error import OEError
from officialeye._internal.error.errors.internal import ErrInternal
from officialeye._internal.error.errors.template import ErrTemplateIdNotUnique
from officialeye._internal.logger.singleton import get_logger

if TYPE_CHECKING:
    from officialeye._internal.template.template import Template
    from officialeye._internal.io.driver import IODriver


# TODO: move part of the Context class methods to IO driver

class Context:

    def __init__(self, manager, /, *, visualization_generation: bool = False):
        self._manager = manager

        self._io_driver: Union[IODriver, None] = None

        self._visualization_generation = visualization_generation

        self._export_counter = 1
        self._not_deleted_temporary_files: List[str] = []

        # keys: template ids
        # values: template
        self._loaded_templates: Dict[str, Template] = {}

        z3.set_param("parallel.enable", True)

    def visualization_generation_enabled(self) -> bool:
        return self._visualization_generation

    def get_io_driver(self) -> IODriver:

        if self._io_driver is None:
            raise ErrInternal(
                "while trying to access officialeye's IO driver.",
                "The present officialeye context does not have an IO Driver set."
            )

        return self._io_driver

    def set_io_driver(self, io_driver: IODriver, /):
        assert io_driver is not None
        self._io_driver = io_driver

    def add_template(self, template: Template, /):

        if template.template_id in self._loaded_templates:
            raise ErrTemplateIdNotUnique(
                f"while loading template '{template.template_id}'",
                "A template with the same id has already been loaded."
            )

        self._loaded_templates[template.template_id] = template

        try:
            template.validate()
        except OEError as err:
            # rollback the loaded template
            del self._loaded_templates[template.template_id]
            # reraise the cause
            raise err

    def get_template(self, template_id: str, /) -> Template:
        assert template_id in self._loaded_templates, "Unknown template id"
        return self._loaded_templates[template_id]

    def _allocate_file_name(self) -> str:
        file_name = "%03d.png" % self._export_counter
        self._export_counter += 1
        return file_name

    def allocate_file_for_export(self, /, *, file_name: str = "") -> str:

        if self._manager.export_directory is None:
            with tempfile.NamedTemporaryFile(prefix="officialeye_", suffix=".png", delete=False) as fp:
                fp.close()
            self._not_deleted_temporary_files.append(fp.name)
            return fp.name

        if file_name == "":
            file_name = self._allocate_file_name()

        return os.path.join(self._manager.export_directory, file_name)

    def export_image(self, img: cv2.Mat, /, *, file_name: str = "") -> str:
        export_file_path = self.allocate_file_for_export(file_name=file_name)
        cv2.imwrite(export_file_path, img)
        get_logger().info(f"Exported '{export_file_path}'.")
        return export_file_path

    def _export_and_show_image(self, img: cv2.Mat, /, *, file_name: str = ""):
        path = self.export_image(img, file_name=file_name)
        click.launch(path, locate=False)
        click.pause()

    def export_primary_image(self, img: cv2.Mat, /, *, file_name: str = ""):
        if get_logger().quiet_mode:
            # just save the image, do not export
            self.export_image(img, file_name=file_name)
        else:
            self._export_and_show_image(img, file_name=file_name)

    def _cleanup_temporary_files(self):
        while len(self._not_deleted_temporary_files) > 0:
            temp_file = self._not_deleted_temporary_files.pop()
            if os.path.exists(temp_file):
                os.unlink(temp_file)

    def dispose(self):
        self._cleanup_temporary_files()
