# Detailed Installation Instructions

This guide provides accessible installation instructions for the ModelChecker package across different operating systems.

## Table of Contents

- [Getting Started with the Terminal](#getting-started-with-the-terminal)
- [Installing Python](#installing-python)
- [Installing ModelChecker](#installing-modelchecker)
- [Platform-Specific Instructions](#platform-specific-instructions)
- [Troubleshooting](#troubleshooting)
- [Next Steps](#next-steps)

## Getting Started with the Terminal

If you're new to using the terminal (command line), this section will help you get started.

### Opening the Terminal

#### macOS

1. Press `Cmd + Space` to open Spotlight search
2. Type "Terminal" and press Enter
3. Alternatively, go to Applications → Utilities → Terminal

#### Windows

**Option 1: Command Prompt**

1. Press `Win + R` to open the Run dialog
2. Type "cmd" and press Enter

**Option 2: PowerShell (Recommended)**

1. Press `Win + X` and select "Windows PowerShell" or "Windows Terminal"
2. Alternatively, search "PowerShell" in the Start menu

**Option 3: Windows Subsystem for Linux (WSL) - Advanced**

1. Install WSL following [Microsoft's guide](https://docs.microsoft.com/en-us/windows/wsl/install)
2. This provides a Linux environment on Windows

### Basic Terminal Commands

Once you have the terminal open, here are some essential commands:

- `pwd` - Shows your current directory (where you are)
- `ls` (macOS/Linux) or `dir` (Windows) - Lists files in current directory
- `cd foldername` - Changes to a folder
- `cd ..` - Goes up one directory level
- `cd ~` - Goes to your home directory

## Installing Python

ModelChecker requires Python 3.8 or higher. Check if Python is installed:

```bash
python --version
```

or

```bash
python3 --version
```

### If Python is Not Installed

#### macOS

**Option 1: Official Python Installer (Recommended for beginners)**

1. Visit [python.org/downloads](https://www.python.org/downloads/)
2. Download the latest Python 3.x version
3. Run the installer and follow the prompts
4. Make sure to check "Add Python to PATH" during installation

**Option 2: Homebrew**

```bash
# Install Homebrew first if you don't have it
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"

# Install Python
brew install python
```

#### Windows

**Option 1: Microsoft Store (Easiest)**

1. Open Microsoft Store
2. Search for "Python"
3. Install Python 3.x from the Python Software Foundation

**Option 2: Official Python Installer**

1. Visit [python.org/downloads](https://www.python.org/downloads/)
2. Download the latest Python 3.x version
3. Run the installer
4. **Important**: Check "Add Python to PATH" during installation

#### Linux

**Ubuntu/Debian:**

```bash
sudo apt update
sudo apt install python3 python3-pip
```

**CentOS/RHEL/Fedora:**

```bash
sudo yum install python3 python3-pip
# or for newer versions:
sudo dnf install python3 python3-pip
```

**Arch Linux:**

```bash
sudo pacman -S python python-pip
```

**NixOS:**

````bash
# Python is typically available in NixOS
# For project-specific environments, see the Development section
nix-shell -p python3 python3Packages.pip

## Installing ModelChecker

Once Python is installed, you can install ModelChecker using pip (Python's package manager).

### Basic Installation

Open your terminal and run:

```bash
pip install model-checker
````

If you get a "command not found" error, try:

```bash
python -m pip install model-checker
```

or (on systems where Python 3 is the default `python3` command):

```bash
python3 -m pip install model-checker
```

### Installation with Optional Features

**For Jupyter notebook support:**

This adds interactive widgets, visualization tools, and notebook integration:

```bash
pip install model-checker[jupyter]
```

**For development tools:**

```bash
pip install model-checker[dev]
```

This installs testing frameworks and development dependencies. However, if you're planning to contribute to ModelChecker or modify the source code, you should clone the repository instead of installing via pip. See the [Development Guide](DEVELOPMENT.md) for the complete development setup.

**For everything:**

```bash
pip install model-checker[all]
```

### Verifying Installation

After installation, verify that ModelChecker is installed correctly:

```bash
model-checker --version
```

This should display the version number of ModelChecker.

### Updating ModelChecker

To update to the latest version:

```bash
pip install --upgrade model-checker
```

Or use the built-in upgrade command:

```bash
model-checker --upgrade
```

## Platform-Specific Instructions

### macOS Specific Notes

**If you get permission errors:**

```bash
pip install --user model-checker
```

**If you have multiple Python versions:**

```bash
python3 -m pip install model-checker
```

**Common macOS Issues:**

- If you get SSL certificate errors, update your certificates:
  ```bash
  /Applications/Python\ 3.x/Install\ Certificates.command
  ```

### Windows Specific Notes

**If pip is not recognized:**

1. Make sure Python was added to PATH during installation
2. Try using `py` instead of `python`:
   ```bash
   py -m pip install model-checker
   ```

**If you get permission errors:**

```bash
pip install --user model-checker
```

**Using Windows Subsystem for Linux (WSL):**
If you're using WSL, follow the Linux instructions above.

### Linux Specific Notes

**If you get permission errors:**

```bash
pip install --user model-checker
```

**If pip is not available:**

```bash
# Ubuntu/Debian
sudo apt install python3-pip

# CentOS/RHEL/Fedora
sudo yum install python3-pip
# or
sudo dnf install python3-pip
```

**Arch Linux Specific:**

- Use the AUR (Arch User Repository) if available
- Or install via pip with `--user` flag to avoid system conflicts

**NixOS Specific:**

```bash
# Check if ModelChecker is available in nixpkgs
nix search nixpkgs model-checker

# For development, clone the repository and use shell.nix:
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/Code
nix-shell
./dev_cli.py examples/my_example.py
```

For more NixOS details, see the [Development Guide](DEVELOPMENT.md#nixos-setup).

## Troubleshooting

### Common Issues and Solutions

**"pip: command not found"**

- Try `python -m pip` or `python3 -m pip` instead
- Make sure Python is properly installed and added to PATH

**"Permission denied" errors**

- Use `pip install --user model-checker` to install for your user only
- Or create a virtual environment (recommended)

**SSL Certificate errors**

- Update your system certificates
- On macOS: run the Install Certificates command mentioned above

**"model-checker: command not found" after installation**

- The installation might be in a location not in your PATH
- Try using `python -m model_checker` instead
- Or reinstall with `pip install --user model-checker`

**Import errors for Z3 solver**

- The Z3 solver should install automatically with ModelChecker
- If you get Z3-related errors, try:
  ```bash
  pip install z3-solver
  ```

### Getting Help

If you encounter issues not covered here:

1. Check the [project repository](https://github.com/benbrastmckie/ModelChecker) for known issues
2. Search for existing issues or create a new one
3. Make sure you're using a supported Python version and that the model-checker has been installed

## Virtual Environments

Virtual environments help keep your Python packages organized and prevent conflicts. This is the recommended approach for all users:

### Creating a Virtual Environment

```bash
# Create a new virtual environment
python -m venv modelchecker-env

# Activate it
# On macOS/Linux:
source modelchecker-env/bin/activate

# On Windows:
modelchecker-env\Scripts\activate

# Install ModelChecker in the virtual environment
pip install model-checker

# When you're done working, deactivate:
deactivate
```

### Alternative: NixOS Development Environments

NixOS users can leverage Nix's powerful environment management:

```bash
# Clone the repository
git clone https://github.com/benbrastmckie/ModelChecker.git
cd ModelChecker/Code

# Enter the Nix shell (automatically sets up environment)
nix-shell

# Run examples directly without installation
./dev_cli.py examples/my_example.py
```

The provided `shell.nix` automatically:

- Sets up Python with required dependencies
- Configures PYTHONPATH for local development
- Makes development scripts executable

For automatic environment activation with direnv:

```bash
nix-env -i direnv
direnv allow  # Run once in the project directory
```

## Next Steps

After successful installation, you're ready to begin using ModelChecker:

### Quick Start

```bash
# Create a new logos project
model-checker

# Or load a specific theory
model-checker -l imposition
```

### Essential Documentation

**Getting Started:**
- [Usage Guide](../Code/src/model_checker/theory_lib/docs/USAGE_GUIDE.md) - Basic usage patterns and examples
- [Theory Library](../Code/src/model_checker/theory_lib/README.md) - Available semantic theories
- [Examples Guide](../Code/src/model_checker/theory_lib/docs/EXAMPLES.md) - Working with examples

**In This Directory:**
- [README.md](README.md) - Documentation overview
- [DEVELOPMENT.md](DEVELOPMENT.md) - Contributing and development
- [METHODOLOGY.md](METHODOLOGY.md) - Research methodology
- [TOOLS.md](TOOLS.md) - Advanced debugging tools

**Theoretical Background:**
- [HYPERINTENSIONAL.md](HYPERINTENSIONAL.md) - Hyperintensional semantics
- [Z3_BACKGROUND.md](Z3_BACKGROUND.md) - Z3 theorem prover
- [Academic Papers](#academic-papers) - Published research

### Academic Papers

**Primary Sources:**
- Brast-McKie, B. (2025). ["Counterfactual Worlds"](https://link.springer.com/article/10.1007/s10992-025-09793-8). _Journal of Philosophical Logic_.
- Brast-McKie, B. (2021). ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w). _Journal of Philosophical Logic_.
- Fine, K. (2017). ["Truthmaker Semantics"](https://doi.org/10.1002/9781118972090.ch22). _Companion to Philosophy of Language_.

**Additional Resources:**
- [Author's Research](http://www.benbrastmckie.com/research#access)
