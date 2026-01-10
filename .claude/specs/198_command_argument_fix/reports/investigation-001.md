# Investigation Report: Command Argument Passing Issue

**Task**: 198  
**Date**: 2025-12-27  
**Investigator**: OpenCode System  
**Status**: Root Cause Identified, Better Solution Found

---

## Executive Summary

When invoking `/research 197` with the orchestrator agent, the command file loads but the task number argument (197) is not available to the workflow, causing the orchestrator to ask "Could you please specify which task?" 

**Root Cause**: The current system doesn't have a mechanism to pass command arguments from user invocation to command workflow execution.

**First Fix Attempted**: Added verbose CRITICAL notices and explicit argument extraction logic to command files and orchestrator.

**Better Solution Discovered**: The old system (`.opencode.backup.20251225_173342/`) used a simple `$ARGUMENTS` variable pattern that OpenCode automatically substitutes with user-provided arguments.

---

## Problem Description

### Symptom

When user invokes:
```
/research 197
```

Expected behavior:
- Orchestrator loads `/research` command
- Extracts `197` as task_number
- Proceeds with research workflow for task 197

Actual behavior:
- Orchestrator loads command file as context
- Does NOT see the `197` argument
- Responds: "Could you please specify which task you'd like me to research?"

### User Impact

All commands requiring arguments are broken:
- `/research TASK_NUMBER` - Can't specify which task to research
- `/plan TASK_NUMBER` - Can't specify which task to plan
- `/implement TASK_NUMBER` - Can't specify which task to implement
- `/task "DESCRIPTION"` - Can't pass task description

---

## Root Cause Analysis

### The OpenCode Command Flow

1. User types: `/research 197`
2. OpenCode system routes to `orchestrator` agent (specified in command frontmatter)
3. OpenCode loads `.opencode/command/research.md` as context for orchestrator
4. **ISSUE**: The command file content is loaded, but the `197` argument is NOT automatically available

### Why Arguments Get Lost

The command file (`.opencode/command/research.md`) contains:
- Frontmatter defining the command
- Context definitions
- Workflow stages
- Argument parsing specifications

But these are all **passive documentation**. The orchestrator sees:
- The command definition file
- Instructions on HOW to parse arguments (in `<argument_parsing>` section)
- But NOT the actual user input with arguments

### The Gap

There's no explicit mechanism to:
1. Capture the user's original invocation (`/research 197`)
2. Extract the arguments (`197`)
3. Make them available to the command workflow

The orchestrator receives the command file as instructions but not the actual invocation with parameters.

---

## First Attempted Fix (Verbose Approach)

### Changes Made

1. **Added CRITICAL notices to command headers**:
```markdown
**CRITICAL**: This command expects user invocation in the format:
`/research TASK_NUMBER [PROMPT]`

If you are the orchestrator reading this command file, you MUST:
1. Check the original user message/prompt for the task number
2. Parse the task number from the user's actual invocation
3. If no task number found in user input, ask user to provide it
4. DO NOT proceed with workflow without valid task number
```

2. **Added Stage 0 to workflows**:
```markdown
<stage id="0" name="ExtractUserInput">
  <action>CRITICAL: Extract task number from user's original invocation</action>
  <process>
    1. Look for the user's original message that invoked this command
    2. The user should have typed something like: "/research 197"
    3. Extract the task number (first argument after /research)
    ...
  </process>
</stage>
```

3. **Updated orchestrator Stage 1**:
```markdown
**CRITICAL REQUIREMENT**: You MUST locate the user's original invocation 
message to extract command arguments.
```

4. **Created documentation**:
- `.opencode/context/core/standards/command-argument-handling.md`

### Files Modified

- `.opencode/command/research.md`
- `.opencode/command/implement.md`
- `.opencode/command/plan.md`
- `.opencode/command/task.md`
- `.opencode/agent/orchestrator.md`
- `.opencode/context/core/standards/command-argument-handling.md` (new)

### Problems with This Approach

1. **Verbose**: Adds 10-15 lines of CRITICAL notices to every command file
2. **Fragile**: Relies on orchestrator "finding" user's original message in context
3. **Complex**: Requires explicit parsing logic in every workflow Stage 0
4. **Unproven**: No guarantee this pattern actually works with OpenCode's routing
5. **Maintenance burden**: Every new command needs verbose boilerplate

---

## Better Solution: $ARGUMENTS Pattern

### Discovery

Found in `.opencode.backup.20251225_173342/command/research.md`:

```markdown
**Task Input (required):** $ARGUMENTS (task number(s); ranges/lists allowed, 
e.g., `/research 160`, `/research 132-135`, `/research 132,133,134`)
```

### How It Works

OpenCode has a **built-in substitution mechanism**:
- When user invokes `/research 197`
- OpenCode automatically substitutes `$ARGUMENTS` with `197`
- The command file receives the actual argument value
- Workflow can parse directly from `$ARGUMENTS`

### Evidence from Old System

All argument-taking commands used this pattern:

```bash
$ grep -h "\$ARGUMENTS" .opencode.backup.20251225_173342/command/*.md

**Task Input:** $ARGUMENTS (task number(s); ranges/lists allowed)
**Task Input (required):** $ARGUMENTS (task number(s); ranges/lists...)
**Task Input (required):** $ARGUMENTS (single numeric task ID...)
```

Commands that used it successfully:
- `/research` - Task numbers, ranges, lists
- `/plan` - Task numbers, ranges, lists  
- `/implement` - Task numbers, ranges, lists
- `/revise` - Single task number + optional prompt
- `/task` - Task descriptions
- `/review` - Optional scope parameters

### Pattern Structure

**Standard format**:
```markdown
**Task Input (required):** $ARGUMENTS (description of expected format)
```

**In workflow Stage 1**:
```markdown
<stage id="1" name="ParseInput">
  <action>Validate task numbers</action>
  <process>
    1. Parse task number from $ARGUMENTS
    2. Validate format (integer, range, list)
    3. If invalid, return error with usage
  </process>
</stage>
```

### Advantages

1. **Simple**: Single line per command file
2. **Clean**: No verbose CRITICAL sections needed
3. **Proven**: Worked reliably in previous system
4. **Built-in**: Uses OpenCode's native substitution
5. **Reliable**: OpenCode handles extraction, not manual parsing
6. **Maintainable**: Easy to add to new commands

---

## Comparison: Verbose Fix vs $ARGUMENTS

### Verbose Fix (First Attempt)

**Command File**:
```markdown
**CRITICAL**: This command expects user invocation in the format:
`/research TASK_NUMBER [PROMPT]`

If you are the orchestrator reading this command file, you MUST:
1. Check the original user message/prompt for the task number
2. Parse the task number from the user's actual invocation
3. If no task number found in user input, ask user to provide it
4. DO NOT proceed with workflow without valid task number
```

**Workflow**:
```markdown
<stage id="0" name="ExtractUserInput">
  <action>CRITICAL: Extract arguments from user's original invocation</action>
  <process>
    1. Look for the user's original message that invoked this command
    2. The user should have typed: "/research 197"
    3. Extract required arguments (e.g., task number)
    ...
  </process>
  <critical_note>
    If you don't see the expected arguments in the user's input...
  </critical_note>
</stage>
```

**Total**: ~20-25 lines of boilerplate per command

### $ARGUMENTS Pattern (Better Solution)

**Command File**:
```markdown
**Task Input (required):** $ARGUMENTS (task number; e.g., `/research 197`)
```

**Workflow**:
```markdown
<stage id="1" name="ParseInput">
  <action>Parse and validate task number</action>
  <process>
    1. Extract task number from $ARGUMENTS
    2. Validate format
  </process>
</stage>
```

**Total**: ~1 line + normal workflow stage

### Comparison Table

| Aspect | Verbose Fix | $ARGUMENTS Pattern |
|--------|-------------|-------------------|
| Lines added | 20-25 per command | 1 per command |
| Complexity | High (manual parsing) | Low (automatic) |
| Reliability | Unknown | Proven |
| Maintenance | Difficult | Easy |
| OpenCode integration | External workaround | Native feature |

---

## Recommended Implementation Plan

### Phase 1: Revert First Fix

1. Remove CRITICAL notices from command headers:
   - `.opencode/command/research.md`
   - `.opencode/command/implement.md`
   - `.opencode/command/plan.md`
   - `.opencode/command/task.md`

2. Remove Stage 0 "ExtractUserInput" from workflows:
   - All above command files

3. Revert orchestrator Stage 1 changes:
   - `.opencode/agent/orchestrator.md`

4. Delete or rewrite:
   - `.opencode/context/core/standards/command-argument-handling.md`

### Phase 2: Implement $ARGUMENTS Pattern

1. Add to each command file after frontmatter:
```markdown
**Task Input:** $ARGUMENTS (description)
```

2. Update workflow Stage 1 to parse from $ARGUMENTS:
```markdown
<stage id="1" name="ParseInput">
  <action>Parse arguments from $ARGUMENTS</action>
  <process>
    1. Extract parameters from $ARGUMENTS
    2. Validate format and types
    3. Return error if invalid
  </process>
</stage>
```

3. Commands to update:
   - `/research` - `$ARGUMENTS (task number; e.g., /research 197)`
   - `/plan` - `$ARGUMENTS (task number; e.g., /plan 197)`
   - `/implement` - `$ARGUMENTS (task number or range; e.g., /implement 197)`
   - `/task` - `$ARGUMENTS (task description; e.g., /task "Fix bug")`
   - `/revise` - `$ARGUMENTS (task number and prompt; e.g., /revise 197 "Update")`

### Phase 3: Test

Test each command with arguments:
```bash
/research 172
/plan 172
/implement 172
/task "Test task creation"
/revise 172 "Test revision"
```

Expected: All commands receive and parse arguments correctly.

### Phase 4: Document

1. Update or replace `command-argument-handling.md` to document:
   - `$ARGUMENTS` pattern
   - When to use it
   - Format specifications
   - Examples from each command

2. Add to ARCHITECTURE.md or QUICK-START.md:
   - Brief mention of `$ARGUMENTS` for command arguments
   - Reference to full documentation

---

## Testing Validation

### Test Cases

1. **Simple task number**: `/research 172`
   - Should extract: `172`
   - Should proceed with research workflow

2. **Task number with prompt**: `/research 172 "Focus on CLI"`
   - Should extract: `172` and `"Focus on CLI"`
   - Should use prompt in research

3. **Task description**: `/task "Implement feature X"`
   - Should extract: `"Implement feature X"`
   - Should create task with description

4. **Missing arguments**: `/research`
   - Should detect missing arguments
   - Should return error with usage

5. **Invalid arguments**: `/research abc`
   - Should detect invalid format
   - Should return validation error

### Success Criteria

- [ ] All test cases pass
- [ ] No "please specify which task" errors
- [ ] Arguments are correctly parsed
- [ ] Error messages are helpful
- [ ] No regression in functionality

---

## Lessons Learned

### What Worked

1. **Systematic investigation**: Checking old system revealed proven pattern
2. **Root cause analysis**: Understanding the argument passing gap
3. **Comparison**: Old vs new system showed missing feature

### What Didn't Work

1. **Verbose workarounds**: Adding CRITICAL notices was overengineering
2. **Manual parsing**: Trying to find user message in context was fragile
3. **Complex workflows**: Stage 0 added unnecessary complexity

### Key Insight

**Always check existing/previous implementations before creating new patterns.**

The `$ARGUMENTS` pattern was there all along in the old system - we just needed to look at what worked before instead of inventing new solutions.

---

## Conclusion

The command argument passing issue has a **simple, proven solution**: the `$ARGUMENTS` variable pattern.

**Recommended Action**: 
1. Revert verbose first fix
2. Implement `$ARGUMENTS` pattern from old system
3. Test thoroughly
4. Document for future reference

**Estimated Effort**: 3-4 hours for complete revert and reimplementation

**Expected Outcome**: All slash commands with arguments work correctly with minimal boilerplate.

---

## References

- Old system command files: `.opencode.backup.20251225_173342/command/`
- Task 198: `.opencode/specs/TODO.md`
- First fix changes: Git history (commits on 2025-12-27)
- OpenCode documentation: (check for $ARGUMENTS documentation)

---

**Investigation Status**: COMPLETE  
**Recommended Solution**: Implement $ARGUMENTS pattern  
**Next Steps**: Create implementation plan and execute Phase 1-4
