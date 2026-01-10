# Research Summary: Standardize Command Lifecycle Procedures

**Task**: 211  
**Date**: 2025-12-28  
**Status**: Completed

## Key Findings

Analysis of 4 workflow commands and 6 agents reveals 90% structural similarity in lifecycle patterns with significant duplication. All commands follow identical 8-stage pattern: Preflight, CheckLanguage, PrepareDelegation, InvokeAgent, ReceiveResults, ProcessResults, Postflight, ReturnSuccess. Pre-flight procedures duplicate status updates, validation, and delegation context generation across all commands. Post-flight procedures duplicate artifact linking, git commits, and return formatting. Agents show 85% consistency in return format with minor validation gaps in lean-implementation-agent and task-executor.

## Standardization Opportunities

Extract common 8-stage lifecycle pattern to command-lifecycle.md, reducing duplication from 1,961 lines to 1,200 lines (39% reduction). Create pre-flight and post-flight checklists for validation. Document command-specific variations in comprehensive tables covering status markers, timeouts, routing logic, and artifact types. All variations are legitimate and justified by workflow differences.

## Compliance Status

Commands show 100% compliance with status-markers.md and git-commits.md. Agents show 95% compliance with subagent-return-format.md (2 agents missing summary artifact validation). All follow artifact-management.md lazy directory creation and summary requirements.

## Implementation Estimate

4-phase implementation: Create command-lifecycle.md (4 hours), update commands (6 hours), update agents (4 hours), testing (4 hours). Total 18 hours with medium risk from undocumented variations.

## Recommendations

Proceed with standardization. Create command-lifecycle.md as single source of truth. Update commands to reference lifecycle and document only variations. Add summary artifact validation to lean-implementation-agent and task-executor. Benefits include reduced duplication, easier maintenance, and improved consistency.

## Full Report

See .opencode/specs/211_standardize_command_lifecycle_procedures/reports/research-001.md for detailed analysis, inconsistency matrix, and proposed command-lifecycle.md structure.
