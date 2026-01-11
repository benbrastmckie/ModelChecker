# Using Claude Code with ModelChecker

[← Back to Installation](README.md) | [Basic Installation →](BASIC_INSTALLATION.md) | [Getting Started →](GETTING_STARTED.md)

---

## 1. Getting Started

### What is Claude Code?

Claude Code is Anthropic's official command-line interface for interacting with Claude AI in your terminal. With ModelChecker, it provides:

- **Automated Installation** - Let Claude handle dependency installation
- **Project Creation** - Create ModelChecker projects with AI guidance
- **Debugging** - Get intelligent help diagnosing issues
- **GitHub Integration** - Manage repositories, issues, and PRs

### Prerequisites

Before installing Claude Code, you'll need the following:

- **Anthropic subscription** - Claude Code requires an active Anthropic account with API access. This provides the AI capabilities that power Claude Code's intelligent assistance.
  - [Sign up for Anthropic](https://console.anthropic.com/) and set up billing

- **Internet connection** - Required for Claude AI communication. Claude Code sends your queries to Anthropic's servers and returns responses in real-time.

- **Terminal access** - Claude Code runs in a command-line interface (Terminal on macOS/Linux, PowerShell on Windows). The terminal lets you navigate directories, run commands, and interact with Claude directly in your development workflow.
  - New to the terminal? See [Getting Started: Using the Terminal](GETTING_STARTED.md#before-you-begin-using-the-terminal)

- **Text editor** - A properly configured editor makes working with ModelChecker much easier, providing syntax highlighting, Unicode support for logical symbols (∧, ∨, ¬, □, ◇), and integrated terminal access.
  - See [Setting Up Your Editor](GETTING_STARTED.md#setting-up-your-editor) for recommended options (VSCodium for beginners, NeoVim for advanced users)

- **Git** - For version control and collaboration. Git tracks changes to your files, enables collaboration, and integrates with GitHub for issue tracking and pull requests.
  - New to Git/GitHub? See [Getting Started with GitHub](GIT_GOING.md)

---

## 2. Install Claude Code

### macOS

```bash
# Using Homebrew (recommended)
brew install anthropics/claude/claude-code

# Or using curl
curl -fsSL https://raw.githubusercontent.com/anthropics/claude-code/main/install.sh | sh
```

### Windows

```powershell
# Using winget (Windows 11)
winget install Anthropic.ClaudeCode

# Or using PowerShell (as Administrator)
irm https://raw.githubusercontent.com/anthropics/claude-code/main/install.ps1 | iex
```

### Linux

```bash
# Debian/Ubuntu
curl -fsSL https://raw.githubusercontent.com/anthropics/claude-code/main/install.sh | sh

# Arch Linux
yay -S claude-code

# NixOS
nix-env -iA nixpkgs.claude-code
```

### Verify and Authenticate

```bash
# Verify installation
claude --version

# Authenticate with Anthropic
claude auth login
# Follow the prompts to log in via browser

# Check authentication status
claude auth status
```

---

## 3. Install ModelChecker

Once Claude Code is set up, let it handle the installation:

### Step 1: Create a Workspace

```bash
mkdir -p ~/Documents/Projects
cd ~/Documents/Projects
claude
```

### Step 2: Request Installation

Paste this prompt into Claude Code:

```
Please follow the installation instructions at
https://github.com/benbrastmckie/ModelChecker/blob/master/Docs/installation/BASIC_INSTALLATION.md
to install ModelChecker and all dependencies. After installation, create a test project
to verify everything works.
```

Claude will:
1. Check Python version (3.8+ required)
2. Install ModelChecker via `pip install model-checker`
3. Verify installation with `model-checker --version`
4. Create and run a test project

### Working with Projects

```bash
cd ~/Documents/Projects
claude
```

Example prompts:
```
Help me create a ModelChecker project that checks whether contraposition is valid.
```

```
I'm getting unexpected results. Can you review my premise and conclusion definitions?
```

For detailed usage, see [Getting Started](GETTING_STARTED.md).

---

## 4. Set Up the Agent System

The ModelChecker repository includes an optional `.claude/` agent system that provides enhanced workflow commands.

### What It Provides

- **Task Management**: `/task`, `/research`, `/plan`, `/implement` cycle
- **Specialized Skills**: Python/Z3 development agents
- **Context Files**: Domain knowledge for semantics and theorem proving
- **State Persistence**: Track progress across sessions

### Installation

In Claude Code, paste this URL:

```
https://raw.githubusercontent.com/benbrastmckie/ModelChecker/master/.claude/docs/guides/copy-claude-directory.md
```

Then give this prompt:

```
Please read the instructions at the URL above and follow them to copy
the .claude/ directory into my current working directory.
```

### After Installation

1. **Restart Claude Code** - Exit and restart for commands to be available
2. **Test the setup**:
   ```
   /task "Test task"
   ```
3. **Learn the commands** - See [`.claude/docs/README.md`](../../.claude/docs/README.md)

### Available Commands

| Command | Purpose |
|---------|---------|
| `/task` | Create and manage tasks |
| `/research` | Conduct research on a task |
| `/plan` | Create implementation plan |
| `/implement` | Execute implementation |
| `/todo` | Archive completed tasks |

---

## 5. Using gh CLI for GitHub

GitHub CLI (`gh`) integrates with Claude Code for repository management and issue tracking.

### Install GitHub CLI

Ask Claude Code to install it:

```
Please install the GitHub CLI (gh) for my system and help me authenticate.
```

Or install manually:

```bash
# macOS
brew install gh

# Windows
winget install GitHub.cli

# Linux (Debian/Ubuntu)
sudo apt install gh
```

Then authenticate:

```bash
gh auth login
# Follow prompts to authenticate
```

### Creating Issues

When you encounter problems, report them to the ModelChecker repository:

```bash
cd ~/Documents/Projects/ModelChecker
claude
```

```
Help me create a GitHub issue for the bug I just found.
Include the error message and steps to reproduce.
```

Claude will:
1. Gather relevant information (error messages, environment)
2. Format the issue with proper structure
3. Submit using `gh issue create`

**Manual issue creation:**

```bash
gh issue create --repo benbrastmckie/ModelChecker \
  --title "Brief description" \
  --body "Detailed description with steps to reproduce"
```

### Creating Pull Requests

After making changes:

```
I've added a new feature. Help me create a pull request with proper documentation.
```

Claude will:
1. Create a feature branch
2. Commit your changes
3. Push to remote
4. Create PR using `gh pr create`

For comprehensive Git/GitHub workflows, see [Getting Started with GitHub](GIT_GOING.md).

---

## 6. Tips and Troubleshooting

### Effective Prompts

**Be specific:**
```
Help me install ModelChecker with Jupyter support and create a project
that checks whether the law of excluded middle is valid.
```

**Reference documentation:**
```
Following the instructions in Docs/installation/BASIC_INSTALLATION.md,
install ModelChecker and verify it works.
```

### Common Issues

**Claude Code won't start:**
```bash
which claude          # Check if in PATH
claude auth status    # Check authentication
```

**Authentication issues:**
```bash
claude auth logout
claude auth login
```

**Python environment issues:**
```bash
# Use virtual environment
python -m venv venv
source venv/bin/activate  # macOS/Linux
venv\Scripts\activate     # Windows
pip install model-checker
```

**GitHub CLI issues:**
```bash
gh auth logout
gh auth login
gh repo view benbrastmckie/ModelChecker  # Test access
```

---

## 7. Next Steps

- **[Getting Started](GETTING_STARTED.md)** - Using ModelChecker
- **[Getting Started with GitHub](GIT_GOING.md)** - Git/GitHub workflows
- **[Basic Installation](BASIC_INSTALLATION.md)** - Manual installation
- **[Developer Setup](DEVELOPER_SETUP.md)** - Contributing to ModelChecker
- **[Agent System Docs](../../.claude/docs/README.md)** - Full command reference

### Additional Resources

- **[Claude Code Docs](https://docs.claude.com/claude-code)** - Official documentation
- **[GitHub CLI Manual](https://cli.github.com/manual/)** - Complete gh reference

---

[← Back to Installation](README.md) | [Basic Installation →](BASIC_INSTALLATION.md) | [Developer Setup →](DEVELOPER_SETUP.md)
