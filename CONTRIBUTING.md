# Contributing to OfficialEye

Thanks for taking the time to contribute! Contributions include but are not restricted to:

* Reporting bugs
* Contributing to code
* Writing tests
* Writing documentation

The following is a set of guidelines for contributing.

## Recommended flow of contributing

1. First, fork this project to your own namespace.
2. Clone the **upstream** repository to local:
   ```bash
   git clone https://github.com/ZeroBone/OfficialEye.git
   ```
3. Add the fork as a new remote:
   ```bash
   git remote add fork https://github.com/YOUR_NAME/OfficialEye.git
   git fetch fork
   ```
   where `fork` is the remote name of the fork repository.

**Please:**

1. Don't modify code on the `main` branch, it should always keep track of `origin/main`.

   To update `main` branch to date:

   ```bash
   git pull origin main
   # In rare cases that your local main branch diverges from the remote main:
   git fetch origin && git reset --hard main
   ```

2. Create a new branch based on the up-to-date branch for new patches (or the `dev` branch if there is no specific branch for new patches).
3. Create a Pull Request from that patch branch.

## Local development

We strongly recommend following [this guide](https://officialeye.zerobone.net/usage/getting-started/#installation-for-development) to set up the development environment.

## Pull Requests

Before creating a pull request, please make sure that the following commands work without any errors. Specifically, the linting should not report any code style issues, and there should not be any broken tests.

```bash
pdm run dev-docs
pdm run dev-ruff
pdm run dev-pytest
```