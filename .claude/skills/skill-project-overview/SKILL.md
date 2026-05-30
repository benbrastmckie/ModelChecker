---
name: skill-project-overview
description: Interactive repository analysis and project-overview.md generation via task creation. Invoke for /project-overview command.
allowed-tools: Bash, Read, Write, Edit, Glob, Grep, AskUserQuestion
context: direct
---

# Project Overview Skill (Direct Execution)

Direct execution skill for analyzing a repository and creating a task with research artifact to generate `project-overview.md`. Uses a 3-stage workflow: auto-scan, interactive interview, and task+artifact creation.

**Key behavior**: The skill does NOT write `project-overview.md` directly. It creates a task and research artifact, then guides the user to `/plan` and `/implement` for the actual file generation.

## Context References

Reference (do not load eagerly):
- Path: `@specs/TODO.md` - Current task list
- Path: `@specs/state.json` - Machine state
- Path: `@.claude/context/repo/update-project.md` - Generation guide (template reference)
- Path: `@.claude/context/repo/project-overview.md` - Current project overview

---

## Execution

### Step 1: Generate Session ID

```bash
session_id="sess_$(date +%s)_$(od -An -N3 -tx1 /dev/urandom | tr -d ' ')"
```

### Step 2: Check Current State

Read `.claude/context/repo/project-overview.md` and check if it begins with `<!-- GENERIC TEMPLATE`:

```bash
head -1 .claude/context/repo/project-overview.md 2>/dev/null
```

If file does not exist or contains the generic template marker, proceed with full generation workflow.

If file exists and is already customized (no generic template marker), notify the user:

Use AskUserQuestion:
```json
{
  "question": "project-overview.md already exists and appears customized. What would you like to do?",
  "header": "Existing Overview",
  "multiSelect": false,
  "options": [
    {"label": "Regenerate from scratch", "description": "Re-scan repository and create new task to replace existing overview"},
    {"label": "Cancel", "description": "Keep existing project-overview.md as-is"}
  ]
}
```

If "Cancel" selected, display message and exit:
```
Project overview generation cancelled. Current file preserved at .claude/context/repo/project-overview.md
```

### Step 3: Stage 1 - Auto-Scan Repository

Perform automated repository analysis using bash commands. Collect findings into structured data.

#### 3.1: Directory Structure

```bash
# Top-level directory listing
ls -1d */ 2>/dev/null | head -20

# Key directories (check existence)
for dir in src lib pkg lua tests test after doc docs; do
  [ -d "$dir" ] && echo "Found: $dir/"
done
```

#### 3.2: Language Detection

Count files by extension to identify primary languages:

```bash
# Count files by extension (top 10)
find . -type f -name '*.*' \
  -not -path './.git/*' \
  -not -path './node_modules/*' \
  -not -path './.claude/*' \
  -not -path './specs/*' \
  | sed 's/.*\.//' | sort | uniq -c | sort -rn | head -10
```

#### 3.3: Package Managers and Build Tools

Check for common project configuration files:

```bash
# Package managers
for f in package.json Cargo.toml go.mod flake.nix pyproject.toml Gemfile composer.json; do
  [ -f "$f" ] && echo "Package: $f"
done

# Build tools
for f in Makefile justfile Taskfile.yml CMakeLists.txt build.gradle build.sbt; do
  [ -f "$f" ] && echo "Build: $f"
done
```

#### 3.4: Framework Detection

Identify frameworks from config files and dependencies:

```bash
# Framework-specific config files
for f in next.config.js next.config.ts vite.config.ts vite.config.js \
         nuxt.config.ts angular.json tsconfig.json webpack.config.js \
         init.lua lazy-lock.json; do
  [ -f "$f" ] && echo "Framework: $f"
done

# Check package.json dependencies if exists
if [ -f "package.json" ]; then
  jq -r '.dependencies // {} | keys[]' package.json 2>/dev/null | head -10
fi
```

#### 3.5: Testing Detection

```bash
# Test config files
for f in jest.config.js jest.config.ts vitest.config.ts pytest.ini \
         .pytest.ini conftest.py setup.cfg phpunit.xml; do
  [ -f "$f" ] && echo "TestConfig: $f"
done

# Test file patterns
find . -type f \( -name '*_test.*' -o -name '*_spec.*' -o -name 'test_*' \) \
  -not -path './.git/*' -not -path './node_modules/*' | head -5
```

#### 3.6: CI/CD Detection

```bash
# CI/CD config files
for f in .github/workflows .gitlab-ci.yml .travis.yml Jenkinsfile \
         .circleci/config.yml; do
  [ -e "$f" ] && echo "CI: $f"
done
```

#### 3.7: Key Files

```bash
# Important root files
for f in README.md CLAUDE.md LICENSE CHANGELOG.md ROADMAP.md \
         .gitignore .editorconfig .prettierrc .eslintrc*; do
  [ -f "$f" ] && echo "Key: $f"
done
```

#### 3.8: Entry Points

```bash
# Common entry points
for f in main.go main.py main.rs index.ts index.js init.lua \
         app.py app.ts server.ts server.js; do
  [ -f "$f" ] && echo "Entry: $f"
done

# Check src/ for entry points
for f in src/main.* src/index.* src/app.*; do
  [ -f "$f" ] && echo "Entry: $f"
done 2>/dev/null
```

Compile all findings into a structured summary for display.

### Step 4: Stage 2 - Interactive Interview

Present auto-detected findings and ask verification questions.

#### 4.1: Present Findings for Confirmation

Display the scan results in a readable format:

```
## Repository Scan Results

**Languages detected**: {languages with file counts}
**Build tools**: {list}
**Package managers**: {list}
**Frameworks**: {list or "None detected"}
**Testing**: {test framework/config or "None detected"}
**CI/CD**: {CI system or "None detected"}
**Key directories**: {list}
**Entry points**: {list}
```

Then ask for confirmation:

Use AskUserQuestion:
```json
{
  "question": "Are these findings accurate? Select any that need correction:",
  "header": "Verify Findings",
  "multiSelect": true,
  "options": [
    {"label": "Languages are correct", "description": "{detected languages}"},
    {"label": "Build/framework is correct", "description": "{detected build tools and frameworks}"},
    {"label": "Testing setup is correct", "description": "{detected test framework}"},
    {"label": "Everything looks correct", "description": "No corrections needed"},
    {"label": "I need to provide corrections", "description": "Will provide corrections in next step"}
  ]
}
```

If "I need to provide corrections" is selected, use AskUserQuestion with free text:
```json
{
  "question": "What corrections should be made to the scan results?",
  "header": "Corrections"
}
```

Apply corrections to the findings data.

#### 4.2: Ask About Project Purpose

Use AskUserQuestion:
```json
{
  "question": "What is the primary purpose of this project?",
  "header": "Project Purpose"
}
```

This is a free-text question. The user provides a description of what the project does.

#### 4.3: Ask About Development Workflow

Use AskUserQuestion:
```json
{
  "question": "What is your typical development workflow? Select all that apply:",
  "header": "Dev Workflow",
  "multiSelect": true,
  "options": [
    {"label": "Edit and test locally", "description": "Direct local development"},
    {"label": "Build then test", "description": "Compile/build step before testing"},
    {"label": "TDD/test-first", "description": "Write tests before implementation"},
    {"label": "CI/CD pipeline", "description": "Automated testing and deployment"},
    {"label": "REPL-driven", "description": "Interactive development environment"},
    {"label": "Other", "description": "Will describe in next step"}
  ]
}
```

If "Other" selected, ask for free text description.

#### 4.4: Ask About Additional Components (Optional)

Use AskUserQuestion:
```json
{
  "question": "Are there additional components or important details I should include?",
  "header": "Additional Info",
  "multiSelect": false,
  "options": [
    {"label": "Yes, I have more to add", "description": "Will provide additional information"},
    {"label": "No, that covers it", "description": "Proceed with task creation"}
  ]
}
```

If "Yes" selected, ask for free text.

### Step 5: Stage 3 - Create Task and Research Artifact

#### 5.1: Read Current State

```bash
next_num=$(jq -r '.next_project_number' specs/state.json)
```

#### 5.2: Create Task Directory and Research Artifact

Compute task directory:
```bash
padded_num=$(printf "%03d" "$next_num")
task_slug="generate_project_overview"
task_dir="specs/${padded_num}_${task_slug}"
mkdir -p "${task_dir}/reports" "${task_dir}/plans" "${task_dir}/summaries"
```

Write research artifact at `${task_dir}/reports/01_project-overview-scan.md`:

```markdown
# Research Report: Task #{N}

**Task**: {N} - Generate project-overview.md
**Started**: {ISO_DATE}
**Completed**: {ISO_DATE}
**Effort**: Low
**Dependencies**: None
**Sources/Inputs**:
- Repository auto-scan
- User interview responses
**Artifacts**:
- specs/{NNN}_{SLUG}/reports/01_project-overview-scan.md
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- Automated scan identified {language_count} languages, {framework} framework, {build_tool} build system
- User confirmed/corrected findings via interactive interview
- Project purpose: {user_provided_purpose}
- Development workflow: {workflow_description}

## Findings

### Technology Stack

**Primary Language**: {language}
**Framework/Platform**: {framework or "None"}
**Build System**: {build_tool}
**Package Manager**: {package_manager}
**Testing Framework**: {test_framework or "None detected"}
**CI/CD**: {ci_system or "None detected"}

### Directory Structure

{tree output with descriptions}

### Entry Points

{list of detected entry points}

### Key Files

{list of important files}

### Project Purpose

{user-provided purpose description}

### Development Workflow

{user-selected workflow with any additional details}

### Additional Notes

{any additional information from user, or "None"}

## Recommendations

This report provides all information needed to generate `.claude/context/repo/project-overview.md` using the template in `.claude/context/repo/update-project.md`.

Run `/plan {N}` to create an implementation plan, then `/implement {N}` to generate the file.
```

#### 5.3: Update state.json

Add new task to active_projects:
```bash
jq --argjson num "$next_num" \
   --arg name "$task_slug" \
   '.active_projects += [{
     "project_number": $num,
     "project_name": $name,
     "status": "researched",
     "task_type": "meta",
     "next_artifact_number": 2
   }] | .next_project_number = ($num + 1)' \
   specs/state.json > specs/state.json.tmp && mv specs/state.json.tmp specs/state.json
```

#### 5.4: Update TODO.md

Prepend new task entry to the Tasks section in TODO.md:

```markdown
### {N}. Generate project-overview.md [RESEARCHED]
- **Description**: Generate project-overview.md for this repository based on automated scan and user interview findings
- **Type**: meta
- **Priority**: Medium
- **Created**: {ISO_DATE}
- **Research**: [specs/{NNN}_{SLUG}/reports/01_project-overview-scan.md]
```

#### 5.5: Link Artifact

Use the link-artifact-todo.sh script if available:
```bash
.claude/scripts/link-artifact-todo.sh "$next_num" "Research" "specs/${padded_num}_${task_slug}/reports/01_project-overview-scan.md"
```

#### 5.6: Git Commit

```bash
git add specs/ .claude/
git commit -m "task ${next_num}: create and complete research

Session: ${session_id}"
```

### Step 6: Display Next Steps

Output to user:

```
## Project Overview Task Created

**Task #{N}**: Generate project-overview.md [RESEARCHED]
**Research artifact**: specs/{NNN}_{SLUG}/reports/01_project-overview-scan.md

The research artifact contains all scan findings and your responses. To generate the actual project-overview.md file:

1. Run `/plan {N}` to create an implementation plan
2. Run `/implement {N}` to generate the file

Alternatively, if you want to skip the plan step:
- Run `/implement {N} --force` to implement directly from the research
```

## Notes

- The skill intentionally does NOT write project-overview.md directly
- It creates a task in [RESEARCHED] status, ready for /plan and /implement
- The task type is "meta" since it modifies .claude/ content
- The auto-scan uses simple bash commands (ls, find, file checks) to keep execution fast
- The interactive interview uses AskUserQuestion for multi-turn dialogue
- If the user cancels at any point, no task is created
