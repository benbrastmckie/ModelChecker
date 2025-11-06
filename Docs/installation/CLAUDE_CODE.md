# Using Claude Code with ModelChecker

[← Back to Installation](README.md) | [Basic Installation →](BASIC_INSTALLATION.md) | [Getting Started →](GETTING_STARTED.md)

## What is Claude Code?

Claude Code is Anthropic's official command-line interface that allows you to interact with Claude AI directly in your terminal. It's particularly useful for:

- **Automated Installation** - Let Claude handle dependency installation and environment setup
- **Project Creation** - Use the `model-checker new` command with AI guidance
- **Debugging** - Get intelligent help diagnosing and fixing issues
- **Code Understanding** - Ask questions about ModelChecker's implementation
- **Documentation** - Generate examples and understand theory configurations

**Why use Claude Code with ModelChecker?**

Rather than manually following installation steps, you can simply tell Claude Code to follow the installation guide, and it will:
- Check your Python version and install Python if needed
- Install ModelChecker via pip with correct options
- Set up virtual environments if requested
- Verify the installation works
- Create and test your first project

## Installation

### Prerequisites

Before installing Claude Code, you need:
- **Internet connection** - Required for Claude AI communication
- **Terminal access** - Command line interface (Terminal, PowerShell, etc.)
- **Git** (optional but recommended) - For repository management

### macOS

**Option 1: Using Homebrew (Recommended)**
```bash
brew install anthropics/claude/claude-code
```

**Option 2: Using curl**
```bash
curl -fsSL https://raw.githubusercontent.com/anthropics/claude-code/main/install.sh | sh
```

### Windows

**Option 1: Using winget (Windows 11)**
```powershell
winget install Anthropic.ClaudeCode
```

**Option 2: Using PowerShell**
```powershell
# Run in PowerShell (as Administrator)
irm https://raw.githubusercontent.com/anthropics/claude-code/main/install.ps1 | iex
```

**Option 3: Using WSL (Windows Subsystem for Linux)**
```bash
# Follow the Linux installation instructions below
curl -fsSL https://raw.githubusercontent.com/anthropics/claude-code/main/install.sh | sh
```

### Linux

**Debian/Ubuntu:**
```bash
# Download and install
curl -fsSL https://raw.githubusercontent.com/anthropics/claude-code/main/install.sh | sh

# Or using apt (if available)
sudo apt update
sudo apt install claude-code
```

**Arch Linux:**
```bash
# Using yay (AUR helper)
yay -S claude-code

# Or using paru
paru -S claude-code

# Or manual installation
curl -fsSL https://raw.githubusercontent.com/anthropics/claude-code/main/install.sh | sh
```

**Fedora/RHEL:**
```bash
# Using dnf
sudo dnf install claude-code

# Or using the install script
curl -fsSL https://raw.githubusercontent.com/anthropics/claude-code/main/install.sh | sh
```

### Verify Installation

After installation, verify Claude Code is installed correctly:

```bash
claude --version
```

You should see the version number displayed.

## Authentication

Before using Claude Code, you need to authenticate with your Anthropic account:

```bash
# Start the authentication process
claude auth login

# Follow the prompts to:
# 1. Open the provided URL in your browser
# 2. Log in with your Anthropic account
# 3. Authorize Claude Code
# 4. Return to the terminal
```

Once authenticated, you're ready to use Claude Code!

To check authentication status:
```bash
claude auth status
```

## Automated ModelChecker Installation

This is where Claude Code shines - instead of manually following installation steps, let Claude do the work!

### First-Time Installation

**Step 1: Start Claude Code**

Choose where you want to work (this will be your workspace):
```bash
# Create a workspace directory
mkdir -p ~/Documents/Philosophy/Projects
cd ~/Documents/Philosophy/Projects

# Start Claude Code
claude
```

**Step 2: Request Automated Installation**

Once Claude Code starts, simply paste this message:

```
Please follow the installation instructions at
https://github.com/benbrastmckie/ModelChecker/blob/master/Docs/installation/BASIC_INSTALLATION.md
to install ModelChecker and all dependencies. After installation, create a test project
to verify everything works.
```

**What Claude Code Will Do:**

1. **Check Prerequisites**
   - Verify Python is installed (version 3.8+)
   - Install Python if missing (with your permission)
   - Verify pip is available

2. **Install ModelChecker**
   - Run `pip install model-checker`
   - Or `pip install model-checker[jupyter]` if you want Jupyter support
   - Handle any platform-specific issues

3. **Verify Installation**
   - Run `model-checker --version`
   - Create a test example file
   - Run the example to confirm it works

4. **Create Your First Project**
   - Generate a new project using `model-checker new`
   - Help you understand the project structure
   - Guide you through modifying the example

### Alternative: Manual Installation with AI Assistance

If you prefer more control, install manually and ask Claude for help:

```bash
# Install ModelChecker
pip install model-checker

# Start Claude Code to get help
claude

# Ask questions like:
```

```
I just installed ModelChecker. Can you help me:
1. Verify it's working correctly
2. Create my first example checking modus ponens
3. Understand the output format
```

## Creating Projects with Claude Code

Once ModelChecker is installed, Claude Code can help you create and manage projects.

### Basic Project Creation

```bash
# Start Claude Code in your workspace
cd ~/Documents/Philosophy/Projects
claude
```

Then ask:
```
Please help me create a new ModelChecker project that checks whether
contraposition is valid in classical logic.
```

Claude will:
1. Run `model-checker new my_project`
2. Navigate to the project directory
3. Modify the example file to test contraposition
4. Explain the configuration options
5. Run the model checker
6. Interpret the results

### Working with Existing Projects

```bash
# Navigate to your project
cd ~/Documents/Philosophy/Projects/my_project
claude
```

Example requests:
```
Can you help me add a validity check for De Morgan's laws to this project?
```

```
I'm getting unexpected results. Can you review my premise and conclusion
definitions and help me debug?
```

```
How do I export these results to JSON format?
```

## GitHub Integration: Managing Repositories

Claude Code works seamlessly with GitHub CLI (`gh`) to manage repositories, create pull requests, and collaborate on projects.

### Installing GitHub CLI

**macOS:**
```bash
brew install gh
```

**Windows:**
```powershell
winget install GitHub.cli
```

**Linux (Debian/Ubuntu):**
```bash
sudo apt install gh
```

**Linux (Other):**
See [GitHub CLI installation docs](https://github.com/cli/cli#installation)

### Authenticating with GitHub

```bash
gh auth login
# Follow prompts to authenticate
```

### Using GitHub CLI with Claude Code

Once `gh` is installed and authenticated, Claude Code can help you with repository operations.

**Example: Creating a Repository for Your Project**

```bash
# Navigate to your project
cd ~/Documents/Philosophy/Projects/my_project

# Start Claude Code
claude
```

Then request:
```
Help me create a GitHub repository for this project and push the initial code.
```

Claude will:
1. Initialize git: `git init`
2. Create `.gitignore` for Python projects
3. Make initial commit: `git add . && git commit -m "Initial commit"`
4. Create GitHub repo: `gh repo create my_project --public --source=.`
5. Push code: `git push -u origin main`

**Example: Creating a Feature Branch**

```
I want to add support for modal operators. Help me create a feature branch,
make the changes, and prepare a pull request.
```

Claude will:
1. Create branch: `git checkout -b feature/modal-operators`
2. Help you implement the feature
3. Run tests to verify it works
4. Stage changes: `git add .`
5. Commit: `git commit -m "feat: add modal operator support"`
6. Push: `git push -u origin feature/modal-operators`
7. Create PR: `gh pr create --title "Add modal operators" --body "..."`

**Example: Viewing and Managing Pull Requests**

```
Show me all open pull requests for this repository and help me review PR #5.
```

Claude will:
1. List PRs: `gh pr list`
2. Show PR details: `gh pr view 5`
3. Check out PR locally: `gh pr checkout 5`
4. Help you review the code
5. Add review comments: `gh pr review 5 --comment`

**Example: Collaborating on the Main ModelChecker Repository**

If you want to contribute to ModelChecker itself:

```
Help me fork the ModelChecker repository, clone it locally, and set up
the development environment following the project's standards.
```

Claude will:
1. Fork repository: `gh repo fork benbrastmckie/ModelChecker --clone`
2. Navigate to directory: `cd ModelChecker`
3. Set up development environment (see [DEVELOPER_SETUP.md](DEVELOPER_SETUP.md))
4. Create feature branch for your contribution
5. Guide you through making changes following [Code Standards](../../Code/docs/core/CODE_STANDARDS.md)

### Common GitHub Workflows with Claude Code

**Syncing with Upstream:**
```
The main ModelChecker repository was updated. Help me sync my fork
with the upstream changes.
```

**Creating a Release:**
```
Help me create a new release (version 0.2.0) with a changelog
summarizing the changes since the last release.
```

**Managing Issues:**
```
Show me all open issues labeled "bug" and help me create a branch
to fix issue #42.
```

**Setting Up GitHub Actions:**
```
Help me add a GitHub Actions workflow to automatically run tests
on every pull request.
```

## Example Workflows

### Workflow 1: Complete First-Time Setup

```bash
# Install Claude Code (see platform-specific instructions above)
claude --version  # Verify installation

# Authenticate
claude auth login

# Create workspace
mkdir -p ~/Documents/Philosophy/Projects
cd ~/Documents/Philosophy/Projects

# Start Claude Code
claude
```

In Claude Code:
```
Please help me:
1. Install ModelChecker with Jupyter support
2. Create a new project checking the validity of modus ponens
3. Run the model checker and explain the results
4. Create a GitHub repository for this project
```

### Workflow 2: Adding a Theory to an Existing Project

```bash
cd ~/Documents/Philosophy/my_project
claude
```

```
I want to add exclusion theory to this project to compare how
the same arguments validate under different semantic theories.
Can you help me modify the code?
```

### Workflow 3: Debugging an Installation Issue

```bash
claude
```

```
I installed ModelChecker but when I run 'model-checker --version'
I get "command not found". Can you help me diagnose and fix this?
```

### Workflow 4: Understanding Theory Implementation

```bash
cd ~/Documents/Philosophy/Projects/ModelChecker  # Cloned repository
claude
```

```
Can you explain how the logos theory implements world semantics in
model_checker/theory_lib/logos/semantic.py? I want to understand
the Z3 encoding.
```

## Tips for Effective Use

### Be Specific About Your Goals

**Less effective:**
```
Help me with ModelChecker
```

**More effective:**
```
Help me install ModelChecker with Jupyter support and create a project
that checks whether the law of excluded middle is valid in intuitionistic
logic.
```

### Reference Documentation

```
Following the instructions in Docs/installation/BASIC_INSTALLATION.md,
install ModelChecker and verify it works.
```

### Ask for Explanations

```
Before installing, can you explain the difference between
'pip install model-checker' and 'pip install model-checker[jupyter]'?
```

### Request Validation

```
I modified my example file to add bimodal operators. Can you review it
for correctness before I run the model checker?
```

### Build on Previous Context

Claude Code maintains conversation history:

```
You: Install ModelChecker with all extras
Claude: I'll install ModelChecker with all available features...

You: Now create a test project using the logos theory
Claude: I'll create a new project configured for logos theory...

You: Add a validity check for disjunctive syllogism
Claude: I'll add that argument pattern to your project...
```

## Troubleshooting

### Claude Code Won't Start

```bash
# Check if Claude Code is in your PATH
which claude  # macOS/Linux
where claude  # Windows

# Try reinstalling
curl -fsSL https://raw.githubusercontent.com/anthropics/claude-code/main/install.sh | sh

# Check authentication
claude auth status
```

### Authentication Issues

```bash
# Log out and log back in
claude auth logout
claude auth login
```

### Python Environment Issues

If Claude Code has trouble with Python:

```bash
# Check Python version
python --version
python3 --version

# If using virtual environment, activate it first
source venv/bin/activate  # macOS/Linux
venv\Scripts\activate     # Windows

# Then start Claude Code
claude
```

### Permission Issues

If you see permission errors:

```bash
# Install ModelChecker with user flag
pip install --user model-checker

# Or use virtual environment (recommended)
python -m venv venv
source venv/bin/activate
pip install model-checker
```

### GitHub CLI Issues

```bash
# Check gh is installed
gh --version

# Re-authenticate if needed
gh auth logout
gh auth login

# Verify repository access
gh repo view benbrastmckie/ModelChecker
```

## Advanced Features

### Using Project Standards

ModelChecker has comprehensive development standards in `Code/docs/`. Claude Code can help you follow them:

```
Help me add a new theory following the standards in
Code/docs/core/CODE_STANDARDS.md and Code/docs/core/ARCHITECTURE.md
```

### Running Tests

```
Run the test suite for the logos theory and explain any failures:
PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/logos/tests/unit/ -v
```

### Building Documentation

```
Help me update the theory library documentation after adding my custom
theory implementation.
```

## Additional Resources

### ModelChecker Documentation
- **[Basic Installation](BASIC_INSTALLATION.md)** - Manual installation guide
- **[Getting Started](GETTING_STARTED.md)** - First steps with ModelChecker
- **[Developer Setup](DEVELOPER_SETUP.md)** - Contributing to ModelChecker
- **[Project README](../../README.md)** - Project overview

### Claude Code Documentation
- **[Claude Code Docs](https://docs.claude.com/claude-code)** - Official documentation
- **[Claude Code GitHub](https://github.com/anthropics/claude-code)** - Source code and issues

### GitHub CLI Documentation
- **[GitHub CLI Manual](https://cli.github.com/manual/)** - Complete gh command reference
- **[gh Cheatsheet](https://github.com/cli/cli/blob/trunk/docs/command-line-syntax.md)** - Quick reference

## Getting Help

### Within Claude Code

Simply ask:
```
Can you help me understand how to use Claude Code more effectively
with ModelChecker?
```

### Common Questions

**Q: Can Claude Code install Python if I don't have it?**
A: Yes! Claude can guide you through installing Python or even download and install it with your permission.

**Q: Will Claude modify my code without asking?**
A: No. Claude will show you proposed changes and ask for confirmation before modifying files.

**Q: Can I use Claude Code offline?**
A: No, Claude Code requires an internet connection to communicate with Claude AI.

**Q: How much does Claude Code cost?**
A: Pricing depends on your Anthropic account plan. See [anthropic.com/pricing](https://anthropic.com/pricing) for details.

**Q: Can Claude Code help with theory development?**
A: Yes! Claude can help you understand existing theories, create new theories following project standards, and debug theory implementations.

## Next Steps

Now that you have Claude Code installed:

1. **[Complete Installation](#automated-modelchecker-installation)** - Let Claude install ModelChecker
2. **[Create Your First Project](#creating-projects-with-claude-code)** - Build a simple validity checker
3. **[Set Up GitHub](#github-integration-managing-repositories)** - Prepare for version control
4. **[Explore Theories](../../Code/src/model_checker/theory_lib/README.md)** - Learn about available semantic theories

---

[← Back to Installation](README.md) | [Basic Installation →](BASIC_INSTALLATION.md) | [Developer Setup →](DEVELOPER_SETUP.md)
