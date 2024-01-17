---
icon: material/hammer-wrench
---

# Setup Guide

## Installation

OfficialEye requires Python 3.10+ to be installed. It works on multiple platforms including Linux, Windows and macOS.

!!! note
    The project can be run on older Python versions. However, there will be neither support for them nor a guarantee that all features work.

### Installation for usage

#### Recommended installation method

Start by installing [PIPX](https://github.com/pypa/pipx) (if you haven't installed it already).

=== "MacOS"

    ```shell
    brew install pipx
    pipx ensurepath
    ```

=== "Linux"

    ```shell
    sudo apt install pipx
    pipx ensurepath
    ```

=== "Windows"

    ```shell
    scoop install pipx
    pipx ensurepath
    ```

Next, use `pipx` to install OfficialEye.

```shell
pipx install officialeye
```

#### Installation via PIP

The tool can also be installed with the standard `pip` installation command:

```shell
pip install officialeye --break-system-packages
```

!!! warning
    The above command installs the package globally, which is not recommended due to possible conflicts between OS package managers and python-specific package management tools (see [PEP 668](https://peps.python.org/pep-0668/)).

### Installation for development

To set up the development environment on a Linux (prefferably Ubuntu) computer, start by cloning the [GitHub repository](https://github.com/ZeroBone/OfficialEye) and navigating to the projects' root directory:

```shell
git clone https://github.com/ZeroBone/OfficialEye.git
cd OfficialEye
```

Next, install the [PDM package manager](https://pdm-project.org/):

```shell
curl -sSL https://pdm-project.org/install-pdm.py | python3 -
```

!!! note
    PDM will not work without the `python3-venv` package. Make sure to have `curl` and `python3-venv` installed before running the above command.

Next, initialize a new `venv` environment and enter it:
```shell
pdm venv create
source .venv/bin/activate
```

At this point, a prefix of the form `(officialeye-x.xx)` should appear in the terminal. To complete the setup, run the following commands to install the dependencies and the `officialeye` package in development mode.

```shell
pdm install
pdm run install
```

!!! success
    The tool should now be available via the `officialeye` command. Note that if you leave the virtual environment, the `officialeye` command will no longer be available. Therefore, it is important to not forget to reenter `venv` via the
    ```shell
    source .venv/bin/activate
    ```
    command.

[YAML Basics](yaml-basics.md){ .md-button .md-button--primary}