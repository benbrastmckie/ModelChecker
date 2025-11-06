# Getting Started with GitHub

[← Back to Installation](README.md) | [Claude Code Guide →](CLAUDE_CODE.md) | [Developer Setup →](DEVELOPER_SETUP.md)

## What is GitHub?

GitHub is a platform for hosting and collaborating on code projects. Think of it as a combination of:
- **Cloud storage** for your code
- **Version control** to track changes over time
- **Collaboration tools** for working with others
- **Portfolio** to showcase your projects

For ModelChecker, GitHub allows you to:
- Share your custom theories with others
- Contribute improvements to the main project
- Track different versions of your work
- Collaborate on research projects

## Prerequisites

Before setting up GitHub, you should:
- Have a terminal open (see [Getting Started: Using the Terminal](GETTING_STARTED.md#before-you-begin-using-the-terminal))
- Have Git installed on your computer (instructions below)

**Automated Alternative:** [Claude Code](CLAUDE_CODE.md) can automate much of this process for you, including installing Git, setting up GitHub CLI (`gh`), creating repositories, and managing workflows. If you prefer AI-assisted setup, see the [Claude Code Guide](CLAUDE_CODE.md#github-integration-managing-repositories).

## Installing Git

Git is the version control software that works with GitHub. Check if it's already installed:

```bash
git --version
```

If you see a version number, Git is installed. If not, install it:

**macOS:**
```bash
# Git comes with Xcode Command Line Tools
xcode-select --install

# Or install via Homebrew
brew install git
```

**Windows:**
- Download from [git-scm.com](https://git-scm.com/download/win)
- Or use: `winget install Git.Git`

**Linux:**

**Debian/Ubuntu:**
```bash
sudo apt update
sudo apt install git
```

**Arch:**
```bash
sudo pacman -S git
```

**NixOS:**
Git is typically available in your system packages or development shell.

## Creating a GitHub Account

1. Visit [github.com](https://github.com)
2. Click "Sign up" in the top-right corner
3. Follow the prompts to create your account:
   - Choose a username (this will be public)
   - Enter your email address
   - Create a strong password
   - Verify your email

**Choosing a Username:**
- Use something professional (e.g., your name or research identity)
- It will appear in repository URLs: `github.com/your-username/project-name`
- You can change it later, but links will break

## Configuring Git

After installing Git, set your identity (used in commit messages):

```bash
# Set your name (use your real name or GitHub username)
git config --global user.name "Your Name"

# Set your email (use your GitHub email)
git config --global user.email "your.email@example.com"

# Verify settings
git config --list
```

## SSH Keys: Secure Authentication

SSH keys allow you to connect to GitHub without typing your password every time. Think of it as a secure digital handshake between your computer and GitHub.

### Why Use SSH Keys?

- **No password prompts** when pushing/pulling code
- **More secure** than password authentication
- **Required for many operations** on GitHub

### Checking for Existing SSH Keys

First, check if you already have SSH keys:

```bash
ls -al ~/.ssh
```

Look for files named:
- `id_rsa` and `id_rsa.pub` (older RSA keys)
- `id_ed25519` and `id_ed25519.pub` (modern Ed25519 keys)

If you see these files, you already have SSH keys. Skip to [Adding SSH Key to GitHub](#adding-ssh-key-to-github).

### Generating a New SSH Key

If you don't have SSH keys, create them:

```bash
# Generate Ed25519 key (recommended)
ssh-keygen -t ed25519 -C "your.email@example.com"

# If your system doesn't support Ed25519, use RSA
ssh-keygen -t rsa -b 4096 -C "your.email@example.com"
```

When prompted:
1. **File location**: Press Enter to use the default (`~/.ssh/id_ed25519`)
2. **Passphrase**: Enter a passphrase for extra security (optional but recommended)
3. **Confirm passphrase**: Enter it again

### Adding SSH Key to GitHub

1. **Copy your public key:**

   ```bash
   # macOS
   pbcopy < ~/.ssh/id_ed25519.pub

   # Linux (if xclip is installed)
   xclip -selection clipboard < ~/.ssh/id_ed25519.pub

   # Or just display it and copy manually
   cat ~/.ssh/id_ed25519.pub
   ```

2. **Add to GitHub:**
   - Go to [github.com/settings/keys](https://github.com/settings/keys)
   - Click "New SSH key"
   - Title: Name it (e.g., "My Laptop")
   - Key: Paste your public key (the text you copied)
   - Click "Add SSH key"

3. **Test the connection:**

   ```bash
   ssh -T git@github.com
   ```

   You should see: "Hi username! You've successfully authenticated..."

### Using SSH URLs

When cloning or creating repositories, use SSH URLs:

```bash
# SSH format (use this)
git clone git@github.com:username/repository.git

# HTTPS format (avoid if you have SSH keys)
git clone https://github.com/username/repository.git
```

To convert an existing repository from HTTPS to SSH:

```bash
git remote set-url origin git@github.com:username/repository.git
```

## Basic Git Concepts

Understanding these concepts will help you use Git effectively:

### Repository (Repo)
A project folder tracked by Git. Contains all your files and their history.

### Commit
A snapshot of your project at a specific point in time. Think of it as saving a checkpoint.

### Branch
An independent line of development. The default branch is usually called `main` or `master`.

### Remote
A version of your repository hosted on GitHub (or another server).

### Clone
Copy a repository from GitHub to your computer.

### Push
Send your local commits to GitHub.

### Pull
Download commits from GitHub to your computer.

### Fork
Create your own copy of someone else's repository.

### Pull Request (PR)
Propose changes to a repository. Used for contributing to projects.

## Essential Git Commands

Here are the commands you'll use most often:

### Starting a New Project

```bash
# Create a new local repository
mkdir my_project
cd my_project
git init

# Create a repository on GitHub and push
# (After creating repo on github.com)
git remote add origin git@github.com:username/my_project.git
git add .
git commit -m "Initial commit"
git push -u origin main
```

### Working with Existing Projects

```bash
# Clone a repository
git clone git@github.com:username/repository.git
cd repository

# Check status (what's changed)
git status

# Stage files for commit
git add filename.py        # Stage specific file
git add .                  # Stage all changes

# Commit changes
git commit -m "Describe what you changed"

# Push to GitHub
git push

# Pull latest changes from GitHub
git pull
```

### Creating Branches

```bash
# Create and switch to a new branch
git checkout -b feature-name

# List branches
git branch

# Switch branches
git checkout main

# Merge a branch
git checkout main
git merge feature-name

# Delete a branch
git branch -d feature-name
```

## Your First Repository

Let's create a simple repository:

```bash
# Create a project directory
mkdir ~/Documents/Projects/my_first_repo
cd ~/Documents/Projects/my_first_repo

# Initialize Git
git init

# Create a README file
echo "# My First Repository" > README.md
echo "This is a test project." >> README.md

# Stage and commit
git add README.md
git commit -m "Initial commit: Add README"

# Create repository on GitHub (via web or gh CLI)
# Then connect and push:
git remote add origin git@github.com:your-username/my_first_repo.git
git push -u origin main
```

## Contributing to ModelChecker

If you want to contribute a new theory or improvement:

### 1. Fork the Repository

- Go to [github.com/benbrastmckie/ModelChecker](https://github.com/benbrastmckie/ModelChecker)
- Click "Fork" in the top-right corner
- This creates your own copy

### 2. Clone Your Fork

```bash
git clone git@github.com:your-username/ModelChecker.git
cd ModelChecker

# Add the original repository as "upstream"
git remote add upstream git@github.com:benbrastmckie/ModelChecker.git
```

### 3. Create a Feature Branch

```bash
# Update your fork
git checkout main
git pull upstream main

# Create a new branch
git checkout -b feature/my-new-theory
```

### 4. Make Changes and Commit

```bash
# Make your changes to files
# ...

# Stage changes
git add .

# Commit with descriptive message
git commit -m "feat: Add new theory for temporal logic"

# Push to your fork
git push -u origin feature/my-new-theory
```

### 5. Create a Pull Request

- Go to your fork on GitHub
- Click "Pull Request" or "Compare & pull request"
- Write a clear description of your changes
- Submit the pull request

See [Claude Code Guide: Creating Pull Requests](CLAUDE_CODE.md#creating-a-pull-request) for how Claude Code can help with this process.

## Keeping Your Fork Updated

Regularly sync with the main repository:

```bash
# Fetch updates from original repository
git fetch upstream

# Switch to your main branch
git checkout main

# Merge updates
git merge upstream/main

# Push updates to your fork
git push origin main
```

## Common GitHub Workflows

### Personal Project Workflow

```bash
# Daily work cycle
git pull                               # Get latest changes
# ... make changes to files ...
git add .                              # Stage changes
git commit -m "Update feature X"      # Commit changes
git push                               # Push to GitHub
```

### Collaborative Project Workflow

```bash
# Start a new feature
git checkout main
git pull                               # Get latest
git checkout -b feature/new-feature    # New branch

# ... work on feature ...
git add .
git commit -m "Implement new feature"
git push -u origin feature/new-feature

# Create pull request on GitHub
# After review and merge, clean up
git checkout main
git pull
git branch -d feature/new-feature
```

## Troubleshooting

### "Permission denied (publickey)"

Your SSH key isn't set up correctly.
- Verify key is added to GitHub: [github.com/settings/keys](https://github.com/settings/keys)
- Test connection: `ssh -T git@github.com`
- Regenerate key if needed (see [Generating SSH Keys](#generating-a-new-ssh-key))

### "Failed to push some refs"

Your local repository is behind the remote.
```bash
git pull --rebase
git push
```

### "Merge conflicts"

Git can't automatically merge changes.
```bash
# Open conflicted files and resolve manually
# Look for <<<<<<, ======, >>>>>> markers
# Edit file to keep desired changes
git add resolved-file.py
git commit -m "Resolve merge conflict"
```

### "Detached HEAD state"

You checked out a specific commit instead of a branch.
```bash
git checkout main  # Return to main branch
```

## Learning More

### Official Resources
- **[GitHub Docs](https://docs.github.com)** - Comprehensive guides
- **[Git Book](https://git-scm.com/book)** - Free, in-depth Git guide
- **[GitHub Skills](https://skills.github.com)** - Interactive tutorials

### Quick References
- **[Git Cheat Sheet](https://education.github.com/git-cheat-sheet-education.pdf)** - Common commands
- **[Visualizing Git](https://git-school.github.io/visualizing-git/)** - Interactive visualization

### Video Tutorials
- Search YouTube for "Git and GitHub tutorial for beginners"
- GitHub's official channel has excellent guides

## Next Steps

Now that you have GitHub set up:

1. **[Install Claude Code](CLAUDE_CODE.md)** - AI assistant for development
2. **[Install GitHub CLI](CLAUDE_CODE.md#installing-github-cli)** - Command-line GitHub interface
3. **[Developer Setup](DEVELOPER_SETUP.md)** - Contribute to ModelChecker
4. **Practice** - Create a test repository and experiment

---

[← Back to Installation](README.md) | [Claude Code Guide →](CLAUDE_CODE.md) | [Developer Setup →](DEVELOPER_SETUP.md)
