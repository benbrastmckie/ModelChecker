# Detailed Installation Instructions

This guide provides comprehensive installation instructions for the ModelChecker package across different operating systems, including detailed terminal usage for new users.

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

#### Linux
1. Press `Ctrl + Alt + T`
2. Or search for "Terminal" in your applications menu

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

**Option 2: Homebrew (Advanced users)**
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

## Installing ModelChecker

Once Python is installed, you can install ModelChecker using pip (Python's package manager).

### Basic Installation

Open your terminal and run:

```bash
pip install model-checker
```

If you get a "command not found" error, try:

```bash
python -m pip install model-checker
```

or

```bash
python3 -m pip install model-checker
```

### Installation with Optional Features

**For Jupyter notebook support:**
```bash
pip install model-checker[jupyter]
```

**For development tools:**
```bash
pip install model-checker[dev]
```

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

**Virtual Environment (Recommended):**
```bash
python3 -m venv modelchecker-env
source modelchecker-env/bin/activate
pip install model-checker
```

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
3. Make sure you're using a supported Python version (3.8+)

## Virtual Environments (Recommended for Advanced Users)

Virtual environments help keep your Python packages organized and prevent conflicts:

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

## Next Steps

After successful installation:

1. **Create your first project:**
   ```bash
   model-checker
   ```
   This will prompt you to create a new Logos project.

2. **Try an example:**
   ```bash
   model-checker -l logos
   ```
   This creates a copy of the Logos theory for you to explore.

3. **Check out the documentation:**
   - Read the main [README.md](README.md) for usage instructions
   - Explore the [theory library](src/model_checker/theory_lib/README.md)
   - Try the [Jupyter notebook integration](src/model_checker/jupyter/README.md)

4. **Learn the basics:**
   - Run the examples in your generated project
   - Modify the examples to explore different logical scenarios
   - Read about the semantic theories available

Welcome to ModelChecker! You're now ready to explore formal logic and semantic theories.