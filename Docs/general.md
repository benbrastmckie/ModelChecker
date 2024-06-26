# General

This is a place for general information related to the project.
This may include notes about installing and using the tools involved.
The aim is to provide references that may be helpful at a later time and to new users.

## Pylint

To add libraries to Pylint, run the following:

    # Print the location of the PACKAGE module
    print(f"\nPACKAGE location: {PACKAGE}")

Copy the location, including the following in .pylintrc:

    init-hook='import sys; sys.path.append("LOCATION")'

Include .pylintrc in the directory.

## SSH

MIT Engaging OnDemand offers compute resources. Vist:

    https://engaging-ood.mit.edu/pun/sys/dashboard

To SSH in, run:

    ssh USERNAME@eofe10.mit.edu

To get Z3 to work, load an Anaconda module and install it with:

    module load anaconda3/2022.05
    pip install --user z3-solver

This is for eofe10 with Rochy 8 OS. For eofe7 with CentOS 7, load the following instead:

    module load anaconda3/2023.07

Z3 only needs to be installed once, but the Anaconda module must be loaded each time.
To avoid this, add the following line to the `.bashrc`:

    module load anaconda3/2022.05

Additionally, if backspace does not work in the ssh terminal, add the following to the `.bashrc`:

    export TERM=xterm-256color      

Further information can be found here:

    https://engaging-web.mit.edu/eofe-wiki/software/python_packages/
    https://orcd-docs.mit.edu/getting-started/

To be able to clone the GitHub repo onto the server, run for the email used in GitHub:

    ssh-keygen -t rsa -b 4096 -C "your_email@example.com"

Save the file, adding the contents to SSH keys in GitHub settings.

## Git

For adding an SSH Key and PAT to GitHub:

    https://github.com/benbrastmckie/.config?tab=readme-ov-file#adding-an-ssh-key-to-github

Basic Git tutorial:

    https://www.youtube.com/watch?v=HkdAHXoRtos

For learning how to use LazyGit if relevant:

    https://github.com/benbrastmckie/.config/blob/master/LearningGit.md

## Package

To update the package, complete the following steps:

1. Increment the version number in accordance with `(major.minor.patch)`.
2. Update the documentation to reflect any changes or new features.
3. Rebuild the package by running `python3 -m build` in the project directory where `pyproject.toml` is located.
4. Upload to `PyPI` by running `twine upload dist/*`

