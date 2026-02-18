# Slash Command Document Placement Research Report

## Metadata
- **Date**: 2025-09-30
- **Scope**: Analysis of `/report`, `/debug`, `/plan`, and related slash command document placement logic
- **Primary Directory**: /home/benjamin/Documents/Philosophy/Projects/ModelChecker
- **Files Analyzed**:
  - `.claude/commands/report.md`
  - `.claude/commands/plan.md`
  - `.claude/commands/debug.md`
  - `.claude/commands/implement.md`
  - `.claude/commands/refactor.md`
  - `specs/README.md`
- **Issue**: Documents not consistently placed in the deepest relevant directory's `specs/` subdirectory

## Executive Summary

The ModelChecker project uses custom Claude Code slash commands (`/report`, `/debug`, `/plan`, etc.) that create documentation artifacts in `specs/` directories. Currently, all these commands place documents in the **project root's** `specs/` directory (`/home/benjamin/Documents/Philosophy/Projects/ModelChecker/specs/`), regardless of the topic's actual scope.

**The Problem**: When working on a specific submodule (e.g., `Code/src/model_checker/theory_lib/exclusion/`), documents should be created in that module's `specs/` directory (e.g., `Code/src/model_checker/theory_lib/exclusion/specs/reports/`), not at the project root. This would improve organization and keep related documentation close to relevant code.

**Current State**: The project has multiple `specs/` directories:
- Root: `./specs/` (currently used by all commands)
- Package: `./Code/specs/`
- Theory library: `./Code/src/model_checker/theory_lib/specs/`

**Missing Implementation**: The slash commands describe a "Location Determination" process but don't actually implement it. They always default to the project root's `specs/` directory.

## Current State Analysis

### Slash Command Architecture

Custom slash commands in Claude Code are implemented as Markdown files in `.claude/commands/`:

```
.claude/commands/
├── report.md         # Creates research reports
├── plan.md           # Creates implementation plans
├── debug.md          # Creates debugging analyses
├── implement.md      # Executes plans with automated testing
├── refactor.md       # Creates refactoring analysis reports
└── [12 other commands]
```

Each command file contains:
- **Frontmatter**: Configuration (allowed tools, arguments, description)
- **Prompt Template**: Natural language instructions for Claude
- **Process Description**: Steps the AI should follow

### Document Placement Logic (Current)

All document-creating commands reference a `specs/` directory structure but don't implement location detection:

#### `/report` Command (.claude/commands/report.md:24-28)

```markdown
### 2. Location Determination
I'll find the deepest directory that encompasses all relevant files by:
- Searching for files related to the topic
- Identifying common parent directories
- Selecting the most specific directory that includes all relevant content
```

**Reality**: This is **descriptive intent only**. The command doesn't provide implementation details or require specific file path resolution. Claude interprets this by defaulting to the project root.

#### `/plan` Command (.claude/commands/plan.md:37-42)

```markdown
### 3. Location Determination
I'll find the deepest directory that encompasses all relevant files by:
- Identifying components that will be modified or created
- Finding common parent directories
- Selecting the most specific directory for the plan
```

**Reality**: Same issue—intent without implementation.

#### `/debug` Command (.claude/commands/debug.md:64)

```markdown
- Create numbered report in `specs/reports/` directory
```

**Reality**: No location determination at all; assumes single `specs/` directory.

### Actual Directory Structure

The project **already has** multiple `specs/` directories at different levels:

```bash
$ find . -path "*/specs/*" -type d | head -10
./specs/plans
./specs/baselines
./specs/findings
./specs/implementation
./specs/debug
./specs/research
./Code/specs/plans
./Code/specs/summaries
./Code/specs/reports
./Code/src/model_checker/theory_lib/specs/plans
```

This shows:
1. **Root level**: `./specs/` (6 subdirectories: plans, baselines, findings, implementation, debug, research)
2. **Package level**: `./Code/specs/` (3 subdirectories: plans, summaries, reports)
3. **Theory library level**: `./Code/src/model_checker/theory_lib/specs/` (2 subdirectories: plans, prompts)

**The infrastructure exists**, but the commands don't use it properly.

### What's Working

1. **Numbering System**: Commands correctly detect existing numbered documents and increment
2. **Subdirectory Structure**: `specs/reports/`, `specs/plans/`, etc., are properly organized
3. **Cross-referencing**: Commands can reference documents by path
4. **Metadata Tracking**: Reports include file paths and references

### What's Broken

1. **Location Detection**: No algorithm to find "deepest directory that encompasses all relevant files"
2. **Scope Analysis**: No mechanism to determine which `specs/` directory is appropriate
3. **Default Behavior**: Always defaults to project root, ignoring other `specs/` directories
4. **No Guidance**: Commands don't tell Claude **how** to implement location detection

## Key Findings

### Finding 1: Declarative vs. Imperative Instructions

**Issue**: Slash command prompts are **declarative** (describing what should happen) rather than **imperative** (specifying how to do it).

**Example from report.md:25-28**:
```markdown
I'll find the deepest directory that encompasses all relevant files by:
- Searching for files related to the topic
- Identifying common parent directories
- Selecting the most specific directory that includes all relevant content
```

This reads like a plan, not an algorithm. Claude interprets this as general intent and defaults to the simplest implementation (project root).

**What's Needed**: Explicit algorithmic steps or tool invocations.

### Finding 2: Missing Common Parent Algorithm

The "deepest directory that encompasses all relevant files" concept requires:

1. **Topic Analysis**: Extract key terms from the topic/query
2. **File Search**: Find all files related to those terms
3. **Path Analysis**: Extract directory paths from matching files
4. **Common Parent Calculation**: Find the lowest common ancestor directory
5. **Specs Directory Resolution**: Locate or create `{common_parent}/specs/`

**Current Implementation**: None of this exists. Commands mention it but don't implement it.

### Finding 3: Ambiguous "Relevant Files" Concept

**Problem**: What counts as a "relevant file"?

For a topic like "exclusion theory iterator improvements":
- Should we only consider `Code/src/model_checker/theory_lib/exclusion/` files?
- What about files in `Code/src/model_checker/iterate/` that process exclusion theories?
- What about test files in different directories?

**Impact**: Without clear rules, Claude can't consistently determine the appropriate location.

### Finding 4: Multiple Valid Specs Directories

The project has three levels where `specs/` directories exist:

| Level | Path | When to Use |
|-------|------|-------------|
| Root | `./specs/` | Cross-cutting concerns, project-wide changes |
| Package | `./Code/specs/` | Changes to the `model_checker` package as a whole |
| Theory Library | `./Code/src/model_checker/theory_lib/specs/` | Theory library infrastructure |

**Current Behavior**: Everything goes to root level.

**Desired Behavior**: Documents should go to the **deepest level that encompasses all affected files**.

### Finding 5: Command Interdependencies

The `/implement` command expects to find plans created by `/plan`:

```markdown
# 1. Find all plan files, sorted by modification time
find . -path "*/specs/plans/*.md" -type f -exec ls -t {} + 2>/dev/null
```

This **already searches multiple specs/ directories**! The implementation command handles multiple locations, but the creation commands don't.

**Insight**: The `/implement` command shows the pattern we need: search **all** `specs/` directories, not just one.

## Technical Details

### Algorithm for "Deepest Relevant Directory"

Here's a proposed algorithm the commands should implement:

```bash
# Step 1: Identify relevant files
# - If user mentions specific files/modules, use those
# - Otherwise, grep for topic-related terms in code

# Step 2: Extract unique directory paths
# Example: If files are:
#   - Code/src/model_checker/theory_lib/exclusion/semantic.py
#   - Code/src/model_checker/theory_lib/exclusion/operators.py
#   - Code/src/model_checker/theory_lib/exclusion/tests/unit/test_model.py

# Step 3: Find common parent directory
# Result: Code/src/model_checker/theory_lib/exclusion/

# Step 4: Check for existing specs/ directory
if [ -d "Code/src/model_checker/theory_lib/exclusion/specs" ]; then
    TARGET="Code/src/model_checker/theory_lib/exclusion/specs"
else
    # Step 5: Walk up the tree to find nearest specs/
    # Check: Code/src/model_checker/theory_lib/specs/ (exists!)
    TARGET="Code/src/model_checker/theory_lib/specs"
fi

# Step 6: Create document in TARGET/reports/ or TARGET/plans/
```

### Required Tool Invocations

To implement this, slash commands need to:

1. **Use Grep/Glob** to find relevant files based on topic
2. **Extract paths** from search results
3. **Calculate common parent** directory (pure string manipulation)
4. **Check for specs/** at each level (walking up the tree)
5. **Create directory** if needed (`mkdir -p`)
6. **Write document** to correct location

### Current vs. Desired Behavior

#### Current Behavior

```
User: /report "exclusion theory iterator bug"
Claude: [Creates specs/research/101_exclusion_theory_iterator_bug.md]
Location: /home/benjamin/.../ModelChecker/specs/research/
```

#### Desired Behavior

```
User: /report "exclusion theory iterator bug"
Claude: [Searches for "exclusion" and "iterator" in codebase]
        [Finds files primarily in Code/src/model_checker/theory_lib/exclusion/]
        [Identifies Code/src/model_checker/theory_lib/specs/ as nearest specs/]
        [Creates Code/src/model_checker/theory_lib/specs/research/101_exclusion_theory_iterator_bug.md]
Location: /home/benjamin/.../ModelChecker/Code/src/model_checker/theory_lib/specs/research/
```

## Recommendations

### Recommendation 1: Add Explicit Location Detection Algorithm

**Update**: `.claude/commands/report.md`, `.claude/commands/plan.md`, `.claude/commands/debug.md`

**Change**: Replace vague "Location Determination" sections with explicit step-by-step algorithms:

```markdown
### 2. Location Determination

I'll determine the appropriate specs/ directory using this algorithm:

**Step 1: Identify Relevant Files**
- Use Grep to search for topic keywords in the codebase
- If user mentions specific files, use those
- Collect all matching file paths

**Step 2: Calculate Common Parent Directory**
- Extract directory paths from all relevant files
- Find the deepest common parent directory
- Example: If files are in `Code/src/foo/` and `Code/src/foo/bar/`, common parent is `Code/src/foo/`

**Step 3: Locate Nearest specs/ Directory**
- Starting at common parent, check for `specs/` subdirectory
- If not found, walk up the directory tree
- Check parent directory for `specs/`
- Continue until found or reach project root

**Step 4: Create specs/ if Needed**
- If no specs/ exists in the hierarchy, create at common parent
- Create required subdirectories (reports/, plans/, etc.)

**Step 5: Assign Document Number**
- Check for existing numbered documents in target specs/[type]/
- Use next sequential number (NNN format)

**Example**:
```bash
# Topic: "exclusion theory model constraints"
# Grep results:
#   Code/src/model_checker/theory_lib/exclusion/semantic.py
#   Code/src/model_checker/theory_lib/exclusion/model.py
# Common parent: Code/src/model_checker/theory_lib/exclusion/
# Nearest specs/: Code/src/model_checker/theory_lib/specs/ (exists)
# Target: Code/src/model_checker/theory_lib/specs/reports/101_exclusion_theory_model_constraints.md
```
```

### Recommendation 2: Define "Relevant Files" Heuristics

**Add** to each command's frontmatter or early sections:

```markdown
## Determining Relevant Files

To find relevant files for location detection:

1. **User-Specified Files**: If user mentions specific files/modules, use only those
2. **Topic Keywords**: Extract key terms from topic (remove stopwords like "the", "and", "bug", "fix")
3. **Code Search**: Use Grep to find files containing those keywords in:
   - Class names, function names
   - Module names, file names
   - Comments and docstrings
4. **Limit Scope**:
   - For broad topics (>20 matching files), prefer higher-level specs/ directory
   - For narrow topics (<5 matching files), use deepest common parent
   - For tests-only topics, use the source code directory, not test directory

**Special Cases**:
- "Project-wide" topics → Use root `./specs/`
- "Package" or "installation" topics → Use `./Code/specs/`
- Theory-specific topics → Use `./Code/src/model_checker/theory_lib/specs/`
```

### Recommendation 3: Implement Path Calculation Utilities

**Option A: Use Bash Tools**

Add to command prompts:

```markdown
### Path Calculation Algorithm

Use these bash commands to find the common parent:

```bash
# Get list of relevant files
FILES=$(grep -rl "keyword" Code/src/)

# Extract directories and find common parent
DIRS=$(echo "$FILES" | xargs dirname | sort -u)
COMMON_PARENT=$(echo "$DIRS" | sed 's|/[^/]*$||' | sort -u | head -1)

# Find nearest specs/ directory
CURRENT="$COMMON_PARENT"
while [ "$CURRENT" != "." ]; do
    if [ -d "$CURRENT/specs" ]; then
        SPECS_DIR="$CURRENT/specs"
        break
    fi
    CURRENT=$(dirname "$CURRENT")
done

# Fallback to root if not found
SPECS_DIR="${SPECS_DIR:-./specs}"
```
```

**Option B: Use Python Script**

Create `.claude/utils/find_specs_dir.py`:

```python
#!/usr/bin/env python3
import os
import sys
from pathlib import Path

def find_common_parent(file_paths):
    """Find deepest common parent directory."""
    if not file_paths:
        return Path.cwd()

    paths = [Path(f).parent for f in file_paths]
    common = paths[0]

    for path in paths[1:]:
        while common not in path.parents and common != path:
            common = common.parent

    return common

def find_nearest_specs(start_dir):
    """Walk up tree to find nearest specs/ directory."""
    current = Path(start_dir).resolve()

    while current != current.parent:  # Stop at filesystem root
        specs_dir = current / "specs"
        if specs_dir.is_dir():
            return specs_dir
        current = current.parent

    # Fallback to project root
    return Path.cwd() / "specs"

def main(file_paths):
    common_parent = find_common_parent(file_paths)
    specs_dir = find_nearest_specs(common_parent)
    print(specs_dir)

if __name__ == "__main__":
    main(sys.argv[1:])
```

Reference in commands:

```markdown
**Step 3: Use Utility Script**
```bash
# Find relevant files
FILES=$(grep -rl "topic_keyword" Code/src/)

# Calculate specs directory
SPECS_DIR=$(python .claude/utils/find_specs_dir.py $FILES)

# Create report in calculated location
TARGET="$SPECS_DIR/reports/NNN_topic_name.md"
```
```

### Recommendation 4: Update specs/README.md

**Add** a section explaining the multi-level structure:

```markdown
## Multi-Level Specs Organization

The ModelChecker project uses specs/ directories at multiple levels:

### Root Level: ./specs/
Use for:
- Project-wide infrastructure changes
- Cross-cutting concerns affecting multiple packages
- Release planning and documentation
- Development process improvements

### Package Level: ./Code/specs/
Use for:
- model_checker package architecture changes
- Installation and build system updates
- Package-wide refactoring
- CLI tool improvements

### Theory Library Level: ./Code/src/model_checker/theory_lib/specs/
Use for:
- Theory infrastructure shared across theories
- Theory protocol changes
- Subtheory orchestration improvements

### Individual Theory Level: ./Code/src/model_checker/theory_lib/{theory}/specs/
Currently not used, but could be created for:
- Theory-specific semantic changes
- Individual theory operator improvements
- Theory-specific bug fixes

## Choosing the Right Level

When creating documents with `/report`, `/plan`, or `/debug`:

1. **Identify affected files** using Grep/Glob
2. **Find common parent** directory of all affected files
3. **Locate nearest specs/** directory at or above common parent
4. **Create document** in that specs/ subdirectory

**Example**: A report on "exclusion theory iterator improvements" that affects:
- `Code/src/model_checker/theory_lib/exclusion/semantic.py`
- `Code/src/model_checker/theory_lib/exclusion/operators.py`

Should be placed in:
- ✅ `Code/src/model_checker/theory_lib/specs/reports/` (theory lib level)
- ❌ `./specs/reports/` (too high level)
```

### Recommendation 5: Consistency Across Commands

Ensure all document-creating commands use the same location detection algorithm:

**Commands to Update**:
- `/report` - Research reports
- `/plan` - Implementation plans
- `/debug` - Debug analyses
- `/refactor` - Refactoring reports
- `/document` - Documentation updates

**Commands Already Compatible**:
- `/implement` - Already searches multiple specs/plans/ directories
- `/list-reports` - Already searches multiple specs/reports/ directories
- `/list-plans` - Already searches multiple specs/plans/ directories

**Note**: The "list" and "implement" commands show the correct pattern—they search **all** specs/ directories. Creation commands should match this behavior.

### Recommendation 6: Add Location Override Option

For cases where automatic detection fails or user wants manual control:

```markdown
### Advanced Usage: Manual Location Override

You can specify a target directory explicitly:

```bash
/report "topic description" --specs-dir=Code/src/model_checker/theory_lib/specs
```

This overrides automatic location detection and creates the report in the specified specs/ directory.
```

### Recommendation 7: Implement Sticky Context

**Problem**: Once a report is created in a specific specs/ directory, subsequent plans and debug reports should default to the **same location** unless the topic changes significantly.

**Solution**: Add context tracking to command prompts:

```markdown
### Context Awareness

Before calculating location:

1. **Check for related documents**: Search for recent reports/plans on similar topics
2. **Preserve context**: If found, use the same specs/ directory
3. **Detect topic shift**: If topic is significantly different, recalculate location

**Example**:
```bash
# First command
/report "exclusion theory iterator bug"
# Creates: Code/src/model_checker/theory_lib/specs/reports/101_exclusion_iterator_bug.md

# Follow-up command (same context)
/plan "fix exclusion iterator constraints"
# Creates: Code/src/model_checker/theory_lib/specs/plans/052_fix_exclusion_iterator_constraints.md
# (Uses same specs/ directory as previous report)

# New topic (different context)
/report "installation documentation improvements"
# Creates: Code/specs/reports/015_installation_docs.md
# (Different specs/ directory - package level, not theory level)
```
```

## Implementation Roadmap

### Phase 1: Foundation (High Priority)

1. **Update Command Prompts**
   - Add explicit location detection algorithm to `/report`, `/plan`, `/debug`
   - Replace vague descriptions with step-by-step instructions
   - Include bash commands or tool invocations

2. **Define Heuristics**
   - Document "relevant files" criteria
   - Specify rules for broad vs. narrow topics
   - Clarify special cases (project-wide, package-level, etc.)

3. **Test with Real Topics**
   - Try `/report "exclusion theory model constraints"` and verify correct placement
   - Test cross-cutting topics to ensure they use root specs/
   - Validate numbering still works correctly

### Phase 2: Tooling (Medium Priority)

4. **Create Utility Scripts** (Optional)
   - `find_specs_dir.py` for common parent calculation
   - Could simplify command prompts significantly

5. **Update specs/README.md**
   - Document multi-level structure
   - Explain selection criteria
   - Provide examples

### Phase 3: Advanced Features (Low Priority)

6. **Context Awareness**
   - Track recent documents in same specs/ directory
   - Maintain context for follow-up commands

7. **Manual Override**
   - Add `--specs-dir` option for manual control

8. **Validation**
   - Add checks to warn if placement seems wrong
   - Suggest alternative locations if ambiguous

## Testing Strategy

### Test Cases

1. **Theory-Specific Topic**
   - Input: `/report "exclusion theory semantic validation"`
   - Expected: `Code/src/model_checker/theory_lib/specs/reports/`

2. **Cross-Theory Topic**
   - Input: `/report "theory protocol improvements"`
   - Expected: `Code/src/model_checker/theory_lib/specs/reports/`

3. **Package-Level Topic**
   - Input: `/plan "CLI argument parsing refactor"`
   - Expected: `Code/specs/plans/`

4. **Project-Wide Topic**
   - Input: `/report "git workflow improvements"`
   - Expected: `./specs/research/`

5. **Narrow Scope Topic**
   - Input: `/debug "exclusion operator precedence bug in semantic.py"`
   - Expected: `Code/src/model_checker/theory_lib/specs/debug/` or theory-specific specs/

### Validation Commands

After implementing changes:

```bash
# Test 1: Theory-specific
/report "imposition theory witness constraints"
# Check: Should create in Code/src/model_checker/theory_lib/specs/research/

# Test 2: Package-level
/plan "refactor model_checker output formatting"
# Check: Should create in Code/specs/plans/

# Test 3: Project-wide
/debug "pytest configuration issues"
# Check: Should create in ./specs/debug/

# Verify numbering still works
ls -1 Code/src/model_checker/theory_lib/specs/research/
# Should show sequential numbers
```

## Metrics

### Current State
- **Specs Directories**: 3 levels (root, package, theory lib)
- **Commands Using Root Only**: 5 (`/report`, `/plan`, `/debug`, `/refactor`, `/document`)
- **Commands Searching Multiple**: 3 (`/implement`, `/list-reports`, `/list-plans`)
- **Location Detection Implementation**: 0% (described but not implemented)

### Target State
- **Specs Directories**: Same 3 levels, potentially 4 if individual theory specs/ needed
- **Commands Using Smart Detection**: 5 (all creation commands)
- **Location Detection Implementation**: 100%
- **Correct Placement Rate**: >90% (with manual override for edge cases)

## References

### Files Analyzed
- [.claude/commands/report.md](.claude/commands/report.md:24-28) - Location determination intent
- [.claude/commands/plan.md](.claude/commands/plan.md:37-42) - Common parent description
- [.claude/commands/debug.md](.claude/commands/debug.md:64) - Hardcoded specs/ reference
- [.claude/commands/implement.md](.claude/commands/implement.md:161) - Multi-directory search pattern
- [specs/README.md](specs/README.md) - Current specs organization

### Existing Specs Directories
```
./specs/                                                    # Root level
./Code/specs/                                               # Package level
./Code/src/model_checker/theory_lib/specs/                 # Theory lib level
```

### Related Documentation
- [CLAUDE.md](CLAUDE.md) - Project overview and specs protocol
- [Code/docs/README.md](Code/docs/README.md) - Development standards
- Claude Code docs on slash commands: https://docs.claude.com/en/docs/claude-code/slash-commands

## Conclusion

The ModelChecker project has a well-designed multi-level `specs/` directory structure, but slash commands don't currently use it. All documents are created at the project root level, making organization suboptimal for module-specific work.

**Root Cause**: Commands describe location detection as intent ("I'll find the deepest directory...") without providing implementation details.

**Solution**: Update command prompts with explicit algorithms using Grep, path manipulation, and directory traversal to find the appropriate specs/ level.

**Impact**:
- ✅ Better organization
- ✅ Documentation close to relevant code
- ✅ Easier navigation for future work
- ✅ Leverages existing infrastructure

**Effort**: Low to Medium
- Phase 1: ~2 hours to update command prompts
- Phase 2: ~1 hour to document and test
- Phase 3: ~2 hours for advanced features (optional)

**Next Steps**: Start with Recommendation 1 (update command prompts) and test with real topics before proceeding to advanced features.

---

## 📝 Implementation Update (2025-09-30)

**Status**: ✅ Partially Implemented - Simplified Approach Chosen

A simpler solution was implemented in [plan 102](../plans/102_improve_slash_command_organization.md):
- All non-root `specs/` directories were found to be mostly empty (only 16 files total)
- Decision made to use **single root `specs/` directory** for consistency
- Fixed incorrect `specs/reports/` references to correct subdirectories:
  - `/report` → `specs/research/`
  - `/debug` → `specs/debug/`
  - `/plan` → `specs/plans/`
  - `/refactor` → `specs/research/`
  - `/implement` → `specs/implementation/`

**Rationale for Simplification**:
1. Single location is easier to maintain and discover
2. Fixed paths are clearer than complex location detection
3. Organization by document TYPE (research, debug, plans) works better than by code location
4. Project scale doesn't warrant multi-level specs/ complexity

**Result**: Commands now properly organize documents with clear subdirectory guidance, using simple fixed paths instead of complex algorithms.

See [implementation summary](../implementation/102_implementation_summary.md) for details.
