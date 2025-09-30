---
allowed-tools: Read, Write, Bash, Grep, Glob, WebSearch, WebFetch, Task
argument-hint: <topic or question>
description: Research a topic and create a comprehensive report in the appropriate specs/reports/ directory
command-type: primary
dependent-commands: update-report, list-reports
---

# Generate Research Report

I'll research the specified topic and create a comprehensive report in the most appropriate location.

## Topic/Question
$ARGUMENTS

## Process

### 1. Topic Analysis
First, I'll analyze the topic to determine:
- Key concepts and scope
- Relevant files and directories in the codebase
- Most appropriate location for the specs/reports/ directory

### 2. Location Determination
I'll find the deepest directory that encompasses all relevant files by:
- Searching for files related to the topic
- Identifying common parent directories
- Selecting the most specific directory that includes all relevant content

### 3. Report Numbering
I'll determine the report number by:
- Checking for existing reports in the target `specs/reports/` directory
- Finding the highest numbered report (e.g., `002_*.md`)
- Incrementing to the next number (e.g., `003`)
- Using `001` if no numbered reports exist
- Ensuring consistent three-digit format with leading zeros

### 4. Research Phase
I'll conduct thorough research by:
- **Code Analysis**: Examining relevant source files
- **Documentation Review**: Reading existing docs and comments
- **Pattern Recognition**: Identifying implementation patterns and architectures
- **Dependency Mapping**: Understanding relationships between components
- **Web Research** (if needed): Gathering external context and best practices

### 5. Report Structure
The report will include:
- **Executive Summary**: Brief overview of findings
- **Background**: Context and problem space
- **Current State Analysis**: How things currently work
- **Key Findings**: Important discoveries and insights
- **Technical Details**: In-depth technical analysis
- **Recommendations**: Suggested improvements or next steps
- **References**: Links to relevant files and resources

### 6. Report Creation
I'll create the report as a markdown file with automatic numbering:

#### Numbering System
- Format: `NNN_topic_name.md` where NNN is a three-digit number
- I'll find the highest numbered report in the target directory
- The new report will use the next sequential number (e.g., 001, 002, 003...)
- If no reports exist, start with 001
- Example: `003_terminal_compatibility_analysis.md`

#### File Creation
- Located in `[relevant-dir]/specs/reports/NNN_[topic-name].md`
- Topic name will be converted to lowercase with underscores
- Following professional documentation standards
- Including diagrams and code examples where helpful
- Cross-referencing relevant files with precise locations

### 7. Report Metadata
Each report will include:
- Creation date and time
- Research scope and boundaries
- Files analyzed
- Search queries used
- Time investment estimate

## Output Format

The report will be formatted as:

```markdown
# [Topic] Research Report

## Metadata
- **Date**: [YYYY-MM-DD]
- **Scope**: [Description of research scope]
- **Primary Directory**: [Location of report]
- **Files Analyzed**: [Count and key files]

## Executive Summary
[Brief overview of findings]

## Analysis
[Detailed research findings]

## Recommendations
[Actionable insights and suggestions]

## References
[Links to relevant files and resources]
```

Let me begin researching your topic and determining the best location for the report.
