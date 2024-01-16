import click

OFFICIALEYE_NAME = "OfficialEye"
OFFICIALEYE_GITHUB = "https://github.com/ZeroBone/OfficialEye"
OFFICIALEYE_VERSION = "1.1.2"
OFFICIALEYE_CLI_LOGO = """   ____  _________      _       __   ______         
  / __ \\/ __/ __(_)____(_)___ _/ /  / ____/_  _____ 
 / / / / /_/ /_/ / ___/ / __ `/ /  / __/ / / / / _ \\
/ /_/ / __/ __/ / /__/ / /_/ / /  / /___/ /_/ /  __/
\\____/_/ /_/ /_/\\___/_/\\__,_/_/  /_____/\\__, /\\___/ 
                                       /____/                   
"""


def print_logo():
    click.secho(OFFICIALEYE_CLI_LOGO, fg="red")
