import os
import shutil
import tempfile
from typing import List, Dict

import click

from officialeye.meta import APPLICATION_NAME
from officialeye.template import Template


class OEContext:

    def __init__(self):
        self._export_counter = 1
        self._not_deleted_temporary_files: List[str] = []
        self.debug_mode = False
        self.debug_export_directory = None
        self.export_directory = None
        # keys: template ids
        # values: template
        self._loaded_templates: Dict[str, Template] = {}

    def on_template_loaded(self, template: Template, /):
        assert template.template_id not in self._loaded_templates, "Template already loaded"
        self._loaded_templates[template.template_id] = template

    def get_template(self, template_id: str, /) -> Template:
        assert template_id in self._loaded_templates, "Unknown template id"
        return self._loaded_templates[template_id]

    def get_debug_export_directory(self) -> str:
        if self.debug_export_directory is not None:
            return self.debug_export_directory

        debug_directory = os.path.join(click.get_app_dir(APPLICATION_NAME), "debug")

        if os.path.exists(debug_directory):
            shutil.rmtree(debug_directory)

        os.makedirs(debug_directory, exist_ok=True)

        # cache the debug export directory
        self.debug_export_directory = debug_directory

        return self.debug_export_directory

    def _allocate_file_name(self) -> str:
        file_name = "%03d.png" % self._export_counter
        self._export_counter += 1
        return file_name

    def _allocate_file_for_debug_export(self, file_name: str = "") -> str:
        assert self.debug_mode, "Tried to export debug file when debug mode is off"

        if file_name == "":
            file_name = self._allocate_file_name()

        return os.path.join(self.get_debug_export_directory(), file_name)

    def allocate_file_for_export(self, /, *, file_name: str = "", debug: bool = False) -> str:

        if debug:
            return self._allocate_file_for_debug_export(file_name=file_name)

        if self.export_directory is None:
            with tempfile.NamedTemporaryFile(prefix="officialeye_", suffix=".png", delete=False) as fp:
                fp.close()
            self._not_deleted_temporary_files.append(fp.name)
            return fp.name

        if file_name == "":
            file_name = self._allocate_file_name()

        return os.path.join(self.export_directory, file_name)

    def _cleanup_temporary_files(self):
        for temp_file in self._not_deleted_temporary_files:
            os.unlink(temp_file)
        self._not_deleted_temporary_files = []

    def dispose(self):
        self._cleanup_temporary_files()


_officialeye_context_ = OEContext()


def oe_context() -> OEContext:
    global _officialeye_context_
    return _officialeye_context_
