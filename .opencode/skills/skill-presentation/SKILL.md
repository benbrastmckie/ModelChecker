---
name: skill-presentation
description: Presentation extraction and slide generation routing
allowed-tools: Task
---

# Presentation Skill

Thin wrapper that routes presentation operations to the `presentation-agent`.

## Trigger Conditions

### Direct Invocation
- User explicitly runs `/slides` command

### Implicit Invocation
- Plan steps mentioning PPTX to Beamer/Polylux/Touying conversion

### When NOT to trigger
- Document conversions (use skill-filetypes)
- Spreadsheet conversions (use skill-spreadsheet)

## Execution

1. Input Validation - Validate source is presentation format
2. Context Preparation - Prepare delegation context
3. Invoke Agent - Use Task tool to spawn presentation-agent
4. Return Validation - Validate return matches schema
5. Return Propagation - Return result to caller
