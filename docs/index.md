# Introduction

OfficialEye is a perfect solution if you need to reliably extract important information from a document (e.g. passport or certificate) based on its image. The tool relies on modern AI to transform the original image to a standartized canonical form, whereupon it processes the information you need.

<p align="center">
  <a href="https://github.com/ZeroBone/OfficialEye/actions"><img
    src="https://github.com/ZeroBone/OfficialEye/workflows/ci/badge.svg?branch=main"
    alt="CI"
  /></a>
</p>

## Feature highlights

* **Example-driven and easy to use**. As a user, you need only describe how to recognize an example document. The tool will infer how to process arbitrary documents of that type based on your example.

* **Powerful template system**. Templates capture all aspects of how a certain kind of documents is to be recognized and processed. If you have multiple document types, you simply use multiple templates - OfficialEye will detect the concrete document type automatically. Every template can be configured via a `.yml` file, using an advanced and highly customizable template configuration language.

* **Highly modular and customizable design**. All the steps during document image analysis are clearly separated, with a possibility of easily changing the implementation of every component without recompiling the project, or even injecting custom implementations.

## Installation

OfficialEye requires Python 3.10+ to be installed. It works on multiple platforms including Linux, Windows and macOS.

!!! note
    The project can be run on older Python versions. However, there will be neither support for them nor a guarantee that all features work.

### Installation for usage

The tool can be installed with the standard `pip` installation command:

```shell
pip install officialeye
```

Especially if you are deploying the tool on a production server, you might want to set up `OfficialEye` in a `venv` virtual environment, which is an isolated Python runtime:

```shell
python3 -m venv venv
source venv/bin/activate
pip install officialeye
```

To leave the virtual environment, execute

```shell
deactivate
```

For more information about `venv` virtual environments, see the [official documentation](https://packaging.python.org/en/latest/guides/installing-using-pip-and-virtual-environments/#creating-a-virtual-environment).

### Installation for development

To se tup the development environment, start by cloning the [GitHub repository](https://github.com/ZeroBone/OfficialEye) and navigating to the projects' root directory:

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
pip install -e .
```

!!! success
    The tool should now be available via the `officialeye` command. Note that if you leave the virtual environment, the `officialeye` command will no longer be available. Therefore, it is important to not forget to reenter `venv` via the
    ```shell
    source .venv/bin/activate
    ```
    command.

[:octicons-arrow-right-16: Basics](./usage/basics.md){ .md-button .md-button--primary}