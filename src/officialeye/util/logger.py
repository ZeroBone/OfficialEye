import click

from officialeye.context.singleton import oe_context


def oe_info(msg, *args, prefix: bool = True, **kwargs):
    if oe_context().quiet_mode:
        return
    if prefix:
        click.secho("INFO", bold=True, bg="blue", nl=False)
        click.echo("  ", nl=False)
    click.secho(msg, *args, **kwargs)


def oe_warn(msg, *args, prefix: bool = True, **kwargs):
    if oe_context().quiet_mode:
        return
    if prefix:
        click.secho("WARN", bold=True, bg="yellow", nl=False)
        click.echo("  ", nl=False)
    click.secho(msg, *args, **kwargs)


def oe_debug(msg, *args, prefix: bool = True, **kwargs):
    if not oe_context().debug_mode:
        return
    if oe_context().quiet_mode:
        return
    if prefix:
        click.secho("DEBUG", bold=True, bg="yellow", nl=False)
        click.echo(" ", nl=False)
    click.secho(msg, *args, **kwargs)


def oe_debug_verbose(msg, *args, prefix: bool = True, **kwargs):
    if not oe_context().debug_mode:
        return
    if oe_context().quiet_mode:
        return
    if not oe_context().verbose_mode:
        return
    if prefix:
        click.secho("DEBUG", bold=True, bg="yellow", nl=False)
        click.echo(" ", nl=False)
    click.secho(msg, *args, **kwargs)


def oe_error(msg, *args, prefix: bool = True, **kwargs):
    if oe_context().quiet_mode:
        return
    for line in msg.splitlines():
        if prefix:
            click.secho("ERROR", bold=True, bg="red", nl=False, err=True)
            click.echo(" ", nl=False, err=True)
        click.secho(line, *args, **kwargs, err=True)

