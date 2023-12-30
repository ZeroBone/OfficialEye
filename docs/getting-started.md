# Installation for usage

The simplest way to install OfficialEye is via the standard `pip` installation command:

```bash
pip install officialeye
```

Especially if you are deploying the tool on a production server, you might want to set up `OfficialEye` in a `venv` virtual environment:

```bash
python3 -m venv venv
source venv/bin/activate
pip install officialeye
```

## Leaving and re-entering the virtual environment

If you do want to leave the virtual environment, use the `deactivate` script:

```bash
deactivate
```

To re-enter the virtual environment, execute

```bash
source venv/bin/activate
```

while being located in the root directory of the project.

# Installation for development

The development environment can be setup as follows. First, clone the [GitHub repository](https://github.com/ZeroBone/OfficialEye) and navigate to the projects' root directory:

```bash
git clone https://github.com/ZeroBone/OfficialEye.git
cd OfficialEye
```

Next, setup a `venv` virtual environment and enter it:

```bash
python3 -m venv venv
source venv/bin/activate
```

You should see a `(venv)` prefix in the terminal at this point, meaning that you are in the virtual environment. Now install all of OfficialEye's dependencies using:

```bash
pip install -e .
pip install -r requirements.txt
```

At this point, the `officialeye` command should become available in the terminal. If you modify the code, no new installation is required to run the modified version of the tool via the `officialeye` command in the terminal. It is important, however, to not leave the `venv` environment.

# Basic usage

A good introduction to OfficialEye would be to show how to re-create the example of the [home page](index.md). First, we need a high-quality image of an example document. For this tutorial, we shall use the following example of a German identity card:

![Example of an identity card used in Germany](assets/img/identity_card_de.jpg "Example of an identity card used in Germany")

Broadly speaking, we now need to explain OfficialEye, which parts of this example document contain information we are interested in, and which parts are present on any document of this kind and can be used to recognize the document on other images. OfficialEye uses a concept called *template* to conveniently capture in a single unit the example document together with this information. In this case, it makes sense to create a template called `German ID Card` and identifier `id_de`:

```bash
officialeye create demo/templates/id_de.yml --name "German ID Card" --id id_de --force
```

This command creates the configuration file `demo/templates/id_de.yml` for the new template, so that we don't have to configure everything from scratch. 