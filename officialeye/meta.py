import click

OFFICIALEYE_NAME = "OfficialEye"
OFFICIALEYE_GITHUB = "https://github.com/ZeroBone/OfficialEye"
OFFICIALEYE_VERSION = "1.0.1"
OFFICIALEYE_CLI_LOGO = """
 ▒█████    █████▒ █████▒██▓ ▄████▄   ██▓ ▄▄▄       ██▓       ▓█████▓██   ██▓▓█████ 
▒██▒  ██▒▓██   ▒▓██   ▒▓██▒▒██▀ ▀█  ▓██▒▒████▄    ▓██▒       ▓█   ▀ ▒██  ██▒▓█   ▀ 
▒██░  ██▒▒████ ░▒████ ░▒██▒▒▓█    ▄ ▒██▒▒██  ▀█▄  ▒██░       ▒███    ▒██ ██░▒███   
▒██   ██░░▓█▒  ░░▓█▒  ░░██░▒▓▓▄ ▄██▒░██░░██▄▄▄▄██ ▒██░       ▒▓█  ▄  ░ ▐██▓░▒▓█  ▄ 
░ ████▓▒░░▒█░   ░▒█░   ░██░▒ ▓███▀ ░░██░ ▓█   ▓██▒░██████▒   ░▒████▒ ░ ██▒▓░░▒████▒
░ ▒░▒░▒░  ▒ ░    ▒ ░   ░▓  ░ ░▒ ▒  ░░▓   ▒▒   ▓▒█░░ ▒░▓  ░   ░░ ▒░ ░  ██▒▒▒ ░░ ▒░ ░
  ░ ▒ ▒░  ░      ░      ▒ ░  ░  ▒    ▒ ░  ▒   ▒▒ ░░ ░ ▒  ░    ░ ░  ░▓██ ░▒░  ░ ░  ░
░ ░ ░ ▒   ░ ░    ░ ░    ▒ ░░         ▒ ░  ░   ▒     ░ ░         ░   ▒ ▒ ░░     ░   
    ░ ░                 ░  ░ ░       ░        ░  ░    ░  ░      ░  ░░ ░        ░  ░
                           ░                                        ░ ░            
"""
OFFICIALEYE_EYE = """
  ▒████████  
 ▒██▒     ██▒
▒██░  ██░  ██▒
 ▒██      ██░
  ░ ████▓▒░
  ░ ▒░▒░▒░ 
    ░ ▒ ▒░ 
  ░ ░ ░ ▒  
      ░ ░
"""


def print_logo():
    for logo_line, eye_line in zip(OFFICIALEYE_CLI_LOGO.splitlines(), OFFICIALEYE_EYE.splitlines()):
        click.secho(logo_line, fg="red", nl=False)
        click.echo("    ", nl=False)
        click.secho(eye_line, fg="blue", blink=True)
