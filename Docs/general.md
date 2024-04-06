# General

This is a place for general information related to the project.
This may include notes about installing and using the tools involved.
The aim is to provide references that may be helpful at a later time and to new users.

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

Further information can be found here:

    https://engaging-web.mit.edu/eofe-wiki/software/python_packages/
    https://orcd-docs.mit.edu/getting-started/

## Git

For adding an SSH Key and PAT to GitHub:

    https://github.com/benbrastmckie/.config?tab=readme-ov-file#adding-an-ssh-key-to-github

Basic Git tutorial:

    https://www.youtube.com/watch?v=HkdAHXoRtos

For learning how to use LazyGit if relevant:

    https://github.com/benbrastmckie/.config/blob/master/LearningGit.md

### NixOS

For loading Z3 libraries with nix/nixos.

- run `nix develop` in directory containing `flake.nix` to load shell.
