import os
import random
from tempfile import NamedTemporaryFile
from types import TracebackType
from typing import List

import click
import cv2
import numpy as np
from rich.prompt import Confirm

from officialeye import Context
from officialeye.__version__ import __ascii_logo__
from officialeye._cli.ui import TerminalUI, Verbosity


class CLIContext:

    def __init__(self, **kwargs):
        self._api: Context | None = None
        self._ui: TerminalUI | None = None

        self.handle_exceptions = True
        self.visualization_generation = False
        self.export_directory = None

        self.verbosity = Verbosity.QUIET
        self.disable_logo = False

        self._export_counter = 1
        self._not_deleted_temporary_files: List[str] = []

        self.set_params(**kwargs)

    def set_params(self, /, *, handle_exceptions: bool | None = None, visualization_generation: bool | None = None,
                   export_directory: str | None = None, verbosity: Verbosity | None = None, disable_logo: bool | None = None):
        if handle_exceptions is not None:
            self.handle_exceptions = handle_exceptions

        if visualization_generation is not None:
            self.visualization_generation = visualization_generation
        if export_directory is not None:
            self.export_directory = export_directory

        if verbosity is not None:
            self.verbosity = verbosity
        if disable_logo is not None:
            self.disable_logo = disable_logo

    def __enter__(self):
        assert self._api is None
        assert self._ui is None

        assert self._export_counter == 1
        assert len(self._not_deleted_temporary_files) == 0

        self._ui = TerminalUI(self.verbosity)
        self._api = Context(afi=self._ui)

        return self

    def dispose(self):

        self._assert_entered()

        if len(self._not_deleted_temporary_files) > 0 and (self.verbosity == Verbosity.QUIET or Confirm.ask(
                ":question: Should temporary files created above be cleaned up now?",
                default=True, console=self._ui.get_console()
            )
        ):
            files_removed = 0

            # cleanup temporary files
            for temp_file_path in self._not_deleted_temporary_files:
                if os.path.isfile(temp_file_path):
                    os.unlink(temp_file_path)
                    files_removed += 1

            self._ui.info(Verbosity.INFO, f"Successfully removed {files_removed} temporary file(s).")

        # reset fields related to file exporting
        self._export_counter = 1
        self._not_deleted_temporary_files = []

        # dispose the api together with all resources it manages, such as the AFI
        self._api.dispose()

        self._api = None
        self._ui = None

    def __exit__(self, exception_type: any, exception_value: BaseException, traceback: TracebackType):

        self._assert_entered()

        if not self.handle_exceptions:
            self.dispose()
            # tell python that we do not want to handle the exception
            return None

        # handle the possible exception
        if exception_value is None:
            self.dispose()
            return None

        self._ui.handle_uncaught_error(exception_type, exception_value, traceback)

        # free all allocated resources
        self.dispose()

        # tell python that we have handled the exception ourselves
        return True

    def print_logo(self):

        if self.disable_logo:
            return

        logo_color = random.choice([
            "purple",
            "yellow",
            "red",
            "green",
            "cyan"
        ])

        self._ui.echo(Verbosity.INFO, __ascii_logo__, style=f"bold {logo_color}")

    def print_intro(self):

        self.print_logo()

        # print preliminary warnings if necessary
        if not self.handle_exceptions:
            self._ui.warn(Verbosity.INFO, "Raw error mode enabled. Use this mode only if you know precisely what you are doing!", )

        if self.verbosity >= Verbosity.DEBUG:
            self._ui.warn(Verbosity.INFO, "Debug mode enabled. Disable for production use to improve performance.")

        if self.visualization_generation:
            self._ui.warn(Verbosity.INFO, "Visualization generation mode enabled. Disable for production use to improve performance.")

    def _assert_entered(self):
        assert self._api is not None, "The context must be entered for this method to work correctly."
        assert self._ui is not None, "The context must be entered for this method to work correctly."

    def get_api_context(self) -> Context:
        self._assert_entered()
        return self._api

    def get_terminal_ui(self) -> TerminalUI:
        self._assert_entered()
        return self._ui

    def _allocate_file_name(self) -> str:
        self._assert_entered()
        file_name = "%03d.png" % self._export_counter
        self._export_counter += 1
        return file_name

    def allocate_file_for_export(self, /, *, file_name: str = "") -> str:

        self._assert_entered()

        file_suffix = ".png" if file_name == "" else file_name

        if self.export_directory is None:
            with NamedTemporaryFile(prefix="officialeye_", suffix=f"_{file_suffix}", delete=False) as fp:
                fp.close()
            self._not_deleted_temporary_files.append(fp.name)
            return fp.name

        if file_name == "":
            file_name = self._allocate_file_name()

        return os.path.join(self.export_directory, file_name)

    def export_image(self, img: np.ndarray, /, *, file_name: str = "") -> str:

        export_file_path = self.allocate_file_for_export(file_name=file_name)

        cv2.imwrite(export_file_path, img)

        self._ui.info(Verbosity.INFO, f"Exported [b]{export_file_path}[/].")

        return export_file_path

    def export_and_show_image(self, img: np.ndarray, /, *, file_name: str = ""):
        path = self.export_image(img, file_name=file_name)

        if self.verbosity != Verbosity.QUIET and Confirm.ask(
            ":question: Would you like to open the image in an image viewer (as provided by the OS)?",
            default=True, console=self._ui.get_console()
        ):
            click.launch(path, locate=False)
