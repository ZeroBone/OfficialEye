from typing import Callable

import click

from officialeye._internal.error.error import OEError
from officialeye.meta import OFFICIALEYE_CLI_LOGO


def _do_print_oe_error(output_func: Callable[[str], None], error: OEError, /):
    output_func(f"Error {error.code} in module {error.module}: {error.code_text}")
    output_func(f"Error occurred {error.while_text}")
    output_func(f"Problem: {error.problem_text}")

    causes = error.get_causes()
    external_causes = error.get_external_causes()

    if len(causes) + len(external_causes) > 0:
        output_func("The above error has been caused by the following error(s).")

    for cause in causes:
        _do_print_oe_error(output_func, cause)

    for external_cause in external_causes:
        output_func(str(external_cause))


class Logger:

    def __init__(self, /, *, debug_mode: bool = False, quiet_mode: bool = False, verbose_mode: bool = False, disable_logo: bool = False):

        self.debug_mode = debug_mode
        self.quiet_mode = quiet_mode
        self.verbose_mode = verbose_mode
        self.disable_logo = disable_logo

    def debug(self, msg, *args, prefix: bool = True, **kwargs):

        if not self.debug_mode:
            return

        if self.quiet_mode:
            return

        if prefix:
            click.secho("DEBUG", bold=True, bg="yellow", nl=False)
            click.echo(" ", nl=False)

        click.secho(msg, *args, **kwargs)

    def info(self, msg: any, *args, prefix: bool = True, **kwargs):

        if self.quiet_mode:
            return

        if prefix:
            click.secho("INFO", bold=True, bg="blue", nl=False)
            click.echo("  ", nl=False)

        click.secho(msg, *args, **kwargs)

    def warn(self, msg: any, *args, prefix: bool = True, **kwargs):

        if self.quiet_mode:
            return

        if prefix:
            click.secho("WARN", bold=True, bg="yellow", nl=False)
            click.echo("  ", nl=False)

        click.secho(msg, *args, **kwargs)

    def debug_verbose(self, msg: any, *args, prefix: bool = True, **kwargs):

        if not self.debug_mode:
            return

        if self.quiet_mode:
            return

        if not self.verbose_mode:
            return

        if prefix:
            click.secho("DEBUG", bold=True, bg="yellow", nl=False)
            click.echo(" ", nl=False)

        click.secho(msg, *args, **kwargs)

    def error(self, msg: any, *args, prefix: bool = True, **kwargs):

        if self.quiet_mode:
            return

        for line in msg.splitlines():
            if prefix:
                click.secho("ERROR", bold=True, bg="red", nl=False, err=True)
                click.echo(" ", nl=False, err=True)
            click.secho(line, *args, **kwargs, err=True)

    def logo(self):

        if self.quiet_mode:
            return

        if self.disable_logo:
            return

        click.secho(OFFICIALEYE_CLI_LOGO, fg="red")

    def error_oe_error(self, error: OEError, /):
        _do_print_oe_error(self.error, error)

    def debug_oe_error(self, error: OEError, /):
        _do_print_oe_error(self.debug, error)
