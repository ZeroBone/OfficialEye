import click

from officialeye._internal.error.error import OEError
from officialeye.meta import OFFICIALEYE_CLI_LOGO


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
        self.error(f"Error {error.code} in module {error.module}: {error.code_text}")
        self.error(f"Error occurred {error.while_text}")
        self.error(f"Problem: {error.problem_text}")

    def debug_oe_error(self, error: OEError, /):
        self.debug(f"Error {error.code} in module {error.module}: {error.code_text}")
        self.debug(f"Error occurred {error.while_text}")
        self.debug(f"Problem: {error.problem_text}")
