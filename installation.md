# Accessible Installation Instructions

> NOTE: the following instructions are intended to make the package more accessible.
If you run into any trouble, feel free to open an [issue](), carefully documenting the nature of the problem you are facing and what you have tried already, opening a new issue for each problem/topic.

## Terminal

Open the terminal (on MacOS, hit `Cmd + Space` and type `terminal`, hitting `Return`) and list the directories by typing `ls` and hitting `Return`. 
Navigate to your desired location with `cd directory/path/...`, replacing `directory/path/...` accordingly.
If you do not know the full path, you can change directory one step at a time by running `cd next_directory` where `next_directory` is to be replaced with the directory you want to change to, running `ls` after each move to see what to enter next.

Alternatively, if you are on MacOS, write `cd` followed by a space in the terminal but do not hit `return`.
Then you can open the desired project directory in Finder, dragging the Finder window onto the terminal.
This should paste the path into the terminal.
You can now hit return to change to the desired directory.
If you are in the directory in which the `test_file.py` exists, you can run `model-checker test_file.py` without specifying the full (or relative) path to that file.
Use the 'up'-arrow key to scroll through past commands, saving time when running the same file multiple times.

Files can be edited with your choice of text editor, e.g., run `vim test_file.py` to edit the named file in the terminal with Vim (for help, run `vimtutor`).
If you do not want to use Vim (exit with `:qa`), you might consider using this configuration of [NeoVim](https://github.com/benbrastmckie/.config) or [VSCodium](https://github.com/benbrastmckie/VSCodium) for working with LaTeX, Markdown, Python, etc., or any other editor you like (e.g., TextEdit on MacOS, or [PyCharm](https://www.jetbrains.com/pycharm/)).

## Python Packages

If you have not already, install [Python 3](https://www.python.org/downloads/) and run the following command in the terminal:

```
pip install model-checker
```

The project has the `z3-solver` as a dependency which should be installed automatically.
You can confirm that `z3-solver` is installed with:

```
pip show z3-solver
```

In case the dependency did not install automatically, you can run:

```
pip install z3-solver
```

More information can be found [here](https://packaging.python.org/en/latest/tutorials/installing-packages/).
