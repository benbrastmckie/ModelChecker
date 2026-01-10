# Research Report: --divide Flag Implementation for /research Command

**Project**: #189  
**Date**: 2025-12-25  
**Research Type**: Implementation Strategy  

## Research Question

How should a `--divide` flag be implemented for the `/research` command to enable topic subdivision and multi-subagent research workflows while maintaining backward compatibility, protecting context windows, and following artifact-management.md standards?

## Sources Consulted

- **Codebase Analysis**: 5 core files (research.md, researcher.md, implement.md, artifact-management.md, status-markers.md)
- **Web Research**: 8 primary sources on multi-agent coordination and topic subdivision
- **Existing Patterns**: Flag implementations in /implement and /research commands
- **Standards Review**: artifact-management.md, status-markers.md, plan.md, report.md, summary.md

## Key Findings

### 1. Flag Implementation Patterns

#### Current Flag Usage in Commands

**Pattern Analysis from /research command**:
```markdown
input_format: "Required: task number(s) - single (e.g., /research 160), range (e.g., /research 132-135), or list (e.g., /research 132,133,134). Reject missing/non-numeric inputs."

usage_examples:
  - `/research 161 "Investigate parser regression"`
  - `/research 129 --lang lean "Temporal swap strategy"`
```

**Pattern Analysis from /implement command**:
```markdown
<stage id="2.5" name="AssessComplexity">
  <action>Assess task complexity for routing differentiation</action>
  <process>
    3. Allow manual override with flags:
       - --simple: Force simple path (skip complexity assessment)
       - --complex: Force complex path (full workflow)
  </process>
</stage>
```

#### Recommended Flag Implementation

**Flag Specification**:
- **Name**: `--divide` (boolean flag, no argument required)
- **Position**: After task number, before optional prompt
- **Format**: `/research {task_number} --divide [optional_prompt]`
- **Parsing**: Detect flag in $ARGUMENTS, remove from prompt string
- **Default**: `false` (no subdivision, current behavior)

**YAML Front Matter Documentation**:
```yaml
---
name: research
input_format: "Required: task number(s). Optional: --divide flag for topic subdivision. Format: /research {number} [--divide] [prompt]"
---
```

**Usage Examples**:
```markdown
<usage_examples>
  - `/research 161 "Investigate parser regression"` (standard, no subdivision)
  - `/research 189 --divide "Flag implementation patterns"` (with subdivision)
  - `/research 129 --lang lean --divide "Temporal logic"` (multiple flags)
</usage_examples>
```

**Validation Rules**:
1. Flag must come after task number
2. Flag is optional (default: false)
3. Multiple flags allowed (--lang, --divide can coexist)
4. Invalid flag combinations should error clearly
5. Batch mode (ranges/lists) incompatible with --divide (error: "Cannot use --divide with batch research")

### 2. Topic Subdivision Strategy

#### Research-Backed Approach

Based on multi-agent coordination research (Microsoft Research, OpenAI, academic sources), the optimal subdivision strategy is:

**Subtopic Count**: 3-5 subtopics (hierarchical for complex topics)
- **Simple topics** (1-2 dimensions): 3 flat subtopics
- **Moderate topics** (3-4 dimensions): 4-5 flat subtopics
- **Complex topics** (5+ dimensions): 5 hierarchical subtopics (2-3 levels deep)

**Subdivision Criteria**:
1. **Breadth**: Cover distinct aspects of the topic
2. **Orthogonality**: Minimize overlap between subtopics
3. **Depth**: Each subtopic should be researchable independently
4. **Balance**: Roughly equal research effort per subtopic
5. **Coherence**: Subtopics should relate to central research question

**Subdivision Process** (within researcher agent, not separate specialist):

```markdown
<stage id="1.5" name="SubdivideIfRequested">
  <action>Subdivide topic if --divide flag present</action>
  <process>
    1. Analyze research topic complexity (count dimensions/aspects)
    2. Determine subtopic count (3 for simple, 4-5 for moderate/complex)
    3. Generate subtopics using criteria (breadth, orthogonality, depth, balance, coherence)
    4. Validate subtopics (no overlap, comprehensive coverage, researchable)
    5. Record subtopics in research metadata
  </process>
  <subtopic_generation>
    Input: "Investigate flag implementation patterns for research command"
    
    Analysis:
    - Dimensions: flag parsing, validation, documentation, backward compatibility
    - Complexity: Moderate (4 dimensions)
    - Recommended count: 4 subtopics
    
    Generated Subtopics:
    1. "Flag parsing and validation patterns in existing commands"
    2. "YAML front matter and usage documentation standards"
    3. "Backward compatibility strategies for optional flags"
    4. "Error handling and validation for flag combinations"
  </subtopic_generation>
  <checkpoint>Subtopics generated and validated</checkpoint>
</stage>
```

**Subtopic Naming Convention**:
- Use descriptive, specific names (not generic "Part 1", "Part 2")
- Include key aspect or dimension in name
- Keep names concise (5-10 words)
- Use consistent grammatical structure

**Example Subdivisions**:

| Topic | Complexity | Subtopics |
|-------|-----------|-----------|
| "Flag implementation patterns" | Simple | 1. Parsing strategies<br>2. Validation approaches<br>3. Documentation standards |
| "Multi-agent coordination" | Moderate | 1. Orchestration patterns<br>2. Error handling strategies<br>3. Result aggregation methods<br>4. Performance optimization |
| "Research automation system" | Complex | 1. Topic analysis (1.1 Complexity assessment, 1.2 Subdivision criteria)<br>2. Agent coordination (2.1 Orchestration, 2.2 Communication)<br>3. Result synthesis (3.1 Aggregation, 3.2 Summarization)<br>4. Quality assurance (4.1 Validation, 4.2 Error handling)<br>5. Context protection (5.1 Token limits, 5.2 Artifact management) |

### 3. Multi-Subagent Coordination

#### Vertical Orchestration Pattern (Recommended)

**Architecture**:
```
researcher (coordinator)
    ├─> web-research-specialist (subtopic 1) [parallel]
    ├─> web-research-specialist (subtopic 2) [parallel]
    ├─> web-research-specialist (subtopic 3) [parallel]
    └─> web-research-specialist (subtopic 4) [parallel]
```

**Coordination Workflow**:

```markdown
<stage id="2" name="DelegateToSpecialists">
  <action>Route research tasks to specialist subagents</action>
  <process>
    1. If --divide flag NOT present:
       - Route single research task to web-research-specialist
       - Return when complete
    
    2. If --divide flag present:
       - Generate subtopics (stage 1.5)
       - Launch parallel web-research-specialist instances (one per subtopic)
       - Pass subtopic-specific context to each specialist:
         * Subtopic title
         * Subtopic research questions
         * Parent topic context
         * Project directory path (shared)
         * Subtopic index (for artifact naming)
       - Collect results from all specialists
       - Proceed to aggregation (stage 3)
  </process>
  <parallel_execution>
    - All subtopic research executes concurrently
    - No dependencies between subtopics
    - Coordinator waits for all to complete
    - Partial results preserved on failure
  </parallel_execution>
  <error_handling>
    - If one subtopic fails: Log error, continue with remaining subtopics
    - If majority (>50%) fail: Abort and report error
    - If all fail: Abort and report error
    - Partial success: Include successful subtopics in summary, note failures
  </error_handling>
  <checkpoint>All subtopic research completed (or handled failures)</checkpoint>
</stage>
```

**Specialist Invocation Pattern**:

```markdown
For each subtopic:
  Task(
    subagent_type="subagents/specialists/web-research-specialist",
    description=f"Research subtopic {index}: {subtopic_title}",
    prompt=f"""
    Research subtopic for parent topic: {parent_topic}
    
    Subtopic: {subtopic_title}
    Research Questions: {subtopic_questions}
    
    Project Directory: {project_dir}
    Artifact Path: {project_dir}/reports/research-{index:03d}-{subtopic_slug}.md
    
    Expected Output:
    - Research findings document at specified path
    - 3-5 sentence summary
    - Key resources and recommendations
    """
  )
```

**Result Collection**:
```python
subtopic_results = []
for i, subtopic in enumerate(subtopics):
    result = await research_specialist(subtopic)
    subtopic_results.append({
        "index": i + 1,
        "title": subtopic.title,
        "artifact_path": result.artifact_path,
        "summary": result.summary,
        "key_findings": result.key_findings,
        "status": result.status  # "completed" or "failed"
    })
```

**Error Handling Strategy**:

| Scenario | Action | Outcome |
|----------|--------|---------|
| 1 subtopic fails (of 4) | Log error, continue | Include 3 successful in summary, note 1 failure |
| 2 subtopics fail (of 4) | Log errors, continue | Include 2 successful in summary, note 2 failures |
| 3+ subtopics fail (of 4) | Abort, report error | Return error to orchestrator, no summary created |
| All subtopics succeed | Proceed to aggregation | Create comprehensive summary |

**Graceful Degradation**:
- Partial success is acceptable (>50% completion)
- Failed subtopics noted in summary with error details
- Successful subtopics provide value even if some fail
- User can re-run failed subtopics individually if needed

### 4. Research Summary Report Structure

#### Hierarchical Summarization Approach

**Three-Tier Structure**:

1. **Tier 1: Individual Subtopic Reports** (detailed, in reports/)
   - Full research findings for each subtopic
   - Created by web-research-specialist
   - Naming: `research-{index:03d}-{subtopic_slug}.md`
   - Example: `research-001-flag-parsing-patterns.md`

2. **Tier 2: Aggregated Research Summary** (brief, in summaries/)
   - Synthesizes all subtopic findings
   - References individual reports
   - Includes cross-references between related subtopics
   - Naming: `research-summary.md`
   - Token limit: <500 tokens (enforced)

3. **Tier 3: Return to Orchestrator** (minimal, in-memory)
   - Artifact references only
   - 3-5 sentence summary
   - Top 3-5 key findings
   - Token limit: <100 tokens

**Aggregated Summary Format**:

```markdown
# Research Summary: {topic}

**Project**: #{project_number}  
**Date**: {date}  
**Research Mode**: Divided (--divide flag)  
**Subtopics**: {count}  

## Overview

{2-3 sentence overview of research scope and approach}

## Subtopic Reports

### 1. {Subtopic 1 Title}
**Report**: [research-001-{slug}.md](../reports/research-001-{slug}.md)  
**Key Findings**:
- {finding 1}
- {finding 2}
- {finding 3}

### 2. {Subtopic 2 Title}
**Report**: [research-002-{slug}.md](../reports/research-002-{slug}.md)  
**Key Findings**:
- {finding 1}
- {finding 2}
- {finding 3}

### 3. {Subtopic 3 Title}
**Report**: [research-003-{slug}.md](../reports/research-003-{slug}.md)  
**Key Findings**:
- {finding 1}
- {finding 2}
- {finding 3}

## Cross-References

- Subtopics 1 and 2 both address {common_theme}
- Subtopic 3 provides implementation details for concepts in Subtopic 1
- {other cross-references as needed}

## Synthesis

{3-5 sentences synthesizing findings across all subtopics}

## Top Recommendations

1. {recommendation 1 from cross-subtopic analysis}
2. {recommendation 2 from cross-subtopic analysis}
3. {recommendation 3 from cross-subtopic analysis}

## Metadata

- **Total Sources Consulted**: {count across all subtopics}
- **Research Duration**: {estimated time}
- **Subtopics Completed**: {successful_count}/{total_count}
- **Failed Subtopics**: {list if any, with error details}

## Full Research Report

See: [research-001.md](../reports/research-001.md) (comprehensive synthesis)
```

**Token Budget Enforcement**:
- Individual subtopic reports: No limit (comprehensive)
- Aggregated summary: <500 tokens (enforced by validation)
- Return to orchestrator: <100 tokens (enforced by validation)
- Validation: Count tokens using `chars ÷ 3` estimation
- Error if over limit: Truncate and add "See full report for details"

**Cross-Referencing Strategy**:
1. **Identify common themes** across subtopics during synthesis
2. **Note dependencies** (e.g., Subtopic 2 builds on Subtopic 1)
3. **Highlight contradictions** (if any) and resolution
4. **Link related findings** with explicit references
5. **Create synthesis section** that integrates cross-subtopic insights

**Metadata Tracking**:
```json
{
  "research_mode": "divided",
  "subtopics_total": 4,
  "subtopics_completed": 4,
  "subtopics_failed": 0,
  "total_sources": 23,
  "research_duration_estimate": "2-3 hours",
  "artifacts": [
    {
      "type": "subtopic_report",
      "index": 1,
      "path": "reports/research-001-flag-parsing-patterns.md"
    },
    {
      "type": "subtopic_report",
      "index": 2,
      "path": "reports/research-002-yaml-documentation.md"
    },
    {
      "type": "subtopic_report",
      "index": 3,
      "path": "reports/research-003-backward-compatibility.md"
    },
    {
      "type": "subtopic_report",
      "index": 4,
      "path": "reports/research-004-error-handling.md"
    },
    {
      "type": "aggregated_summary",
      "path": "summaries/research-summary.md"
    },
    {
      "type": "comprehensive_report",
      "path": "reports/research-001.md"
    }
  ]
}
```

### 5. Lazy Directory Creation

#### Current Rules (from artifact-management.md)

**Existing Behavior** (no --divide flag):
```markdown
- `/research` creates project root immediately before writing first research artifact
- Creates only `reports/` when emitting that artifact
- Does NOT pre-create `plans/` or `summaries/`
- Does NOT write state until artifact exists
```

**New Behavior** (with --divide flag):

```markdown
<lazy_creation>
  1. Project root creation:
     - Create `.opencode/specs/NNN_{slug}/` when writing first artifact
     - Same timing as current behavior (no change)
  
  2. reports/ creation:
     - Create when writing first subtopic report (research-001-*.md)
     - Same as current behavior (no change)
  
  3. summaries/ creation:
     - Create ONLY when --divide flag is used
     - Create when writing research-summary.md
     - Do NOT create for standard (non-divided) research
  
  4. Timing:
     - Project root + reports/: Created together when writing first subtopic report
     - summaries/: Created separately when writing aggregated summary
     - No pre-creation of any directories
</lazy_creation>
```

**Decision Logic**:

```python
def create_directories(divide_flag: bool, artifact_type: str):
    if artifact_type == "subtopic_report":
        # First subtopic report triggers project root + reports/
        create_if_not_exists(".opencode/specs/NNN_slug/")
        create_if_not_exists(".opencode/specs/NNN_slug/reports/")
    
    elif artifact_type == "aggregated_summary":
        # Only create summaries/ if --divide flag used
        if divide_flag:
            create_if_not_exists(".opencode/specs/NNN_slug/summaries/")
        else:
            # Standard research: no summaries/ directory
            pass
    
    elif artifact_type == "comprehensive_report":
        # Comprehensive report goes in reports/ (already created)
        pass
```

**State Tracking**:

```json
{
  "project_number": 189,
  "research_mode": "divided",  // or "standard"
  "divide_flag_used": true,
  "artifacts": {
    "subtopic_reports": 4,
    "aggregated_summary": true,
    "comprehensive_report": true
  }
}
```

**Backward Compatibility**:
- Standard research (no --divide): No summaries/ directory created
- Divided research (--divide): summaries/ created when writing summary
- Existing projects: No changes to directory structure
- Migration: None needed (new feature, additive only)

### 6. Backward Compatibility

#### Compatibility Analysis

**Existing Behavior** (preserved):
1. `/research {task_number}` works unchanged
2. `/research {task_number} "prompt"` works unchanged
3. `/research {task_number} --lang lean` works unchanged
4. Batch mode `/research 132-135` works unchanged
5. No summaries/ directory created for standard research

**New Behavior** (additive):
1. `/research {task_number} --divide` enables subdivision
2. `/research {task_number} --divide "prompt"` enables subdivision with prompt
3. `/research {task_number} --lang lean --divide` combines flags
4. Batch mode + --divide errors clearly: "Cannot use --divide with batch research"

**Breaking Changes**: None

**Migration Path**: None needed (feature is opt-in via flag)

**Validation**:

```markdown
<validation>
  <pre_flight>
    - Validate task number (existing)
    - Validate --divide flag position (new)
    - Validate flag combinations (new):
      * --divide + batch mode → error
      * --divide + --lang → allowed
    - Validate prompt format (existing)
  </pre_flight>
  
  <mid_flight>
    - If --divide: Execute subdivision workflow
    - If no --divide: Execute standard workflow (existing)
  </mid_flight>
  
  <post_flight>
    - Standard research: Update TODO to [RESEARCHED], link research-001.md
    - Divided research: Update TODO to [RESEARCHED], link research-summary.md
    - State tracking: Record research_mode ("standard" or "divided")
  </post_flight>
</validation>
```

**Error Messages**:

| Scenario | Error Message |
|----------|---------------|
| Batch + --divide | "Error: Cannot use --divide flag with batch research (ranges/lists). Use --divide with single task numbers only." |
| Invalid flag position | "Error: Flags must come after task number. Format: /research {number} [--divide] [--lang {lang}] [prompt]" |
| Unknown flag | "Error: Unknown flag '{flag}'. Supported flags: --divide, --lang" |

**User Communication**:
- Update usage examples in research.md
- Add --divide to YAML front matter
- Document in NAVIGATION.md or user guide
- No migration guide needed (additive feature)

### 7. Status Markers and State Sync

#### Status Transitions

**Standard Research** (no --divide):
```
[NOT STARTED] → [IN PROGRESS] → [RESEARCHED]
```

**Divided Research** (--divide):
```
[NOT STARTED] → [IN PROGRESS] → [RESEARCHED]
```

**No Change**: Status transitions remain the same regardless of --divide flag

**Rationale**: 
- --divide is an internal implementation detail
- User sees same status progression
- Final status [RESEARCHED] indicates research complete (regardless of method)

#### TODO.md Linking

**Standard Research** (current behavior):
```markdown
### 189. Add --divide flag to /research command
**Status**: [RESEARCHED]
**Started**: 2025-12-25
**Completed**: 2025-12-25
- Research: [Research Report](189_research_divide_flag/reports/research-001.md)
```

**Divided Research** (new behavior):
```markdown
### 189. Add --divide flag to /research command
**Status**: [RESEARCHED]
**Started**: 2025-12-25
**Completed**: 2025-12-25
- Research Summary: [Research Summary](189_research_divide_flag/summaries/research-summary.md)
- Research Report: [Research Report](189_research_divide_flag/reports/research-001.md)
```

**Linking Strategy**:
- **Standard research**: Link to `research-001.md` (comprehensive report)
- **Divided research**: Link to BOTH `research-summary.md` (quick reference) AND `research-001.md` (comprehensive)
- **Order**: Summary first, then comprehensive report
- **Labels**: Clear distinction ("Research Summary" vs "Research Report")

#### State Tracking

**state.json Updates**:

```json
{
  "tasks": {
    "189": {
      "status": "researched",
      "started": "2025-12-25",
      "completed": "2025-12-25",
      "research_mode": "divided",  // NEW: track subdivision
      "artifacts": {
        "subtopic_reports": [
          "189_research_divide_flag/reports/research-001-flag-parsing.md",
          "189_research_divide_flag/reports/research-002-yaml-docs.md",
          "189_research_divide_flag/reports/research-003-compatibility.md",
          "189_research_divide_flag/reports/research-004-error-handling.md"
        ],
        "aggregated_summary": "189_research_divide_flag/summaries/research-summary.md",
        "comprehensive_report": "189_research_divide_flag/reports/research-001.md"
      }
    }
  }
}
```

**Project state.json**:

```json
{
  "project_number": 189,
  "project_name": "research_divide_flag",
  "type": "research",
  "phase": "completed",
  "status": "researched",
  "research_mode": "divided",
  "subtopics_count": 4,
  "subtopics_completed": 4,
  "created": "2025-12-25T23:15:00Z",
  "started": "2025-12-25",
  "completed": "2025-12-25",
  "artifacts": {
    "reports": [
      "research-001-flag-parsing.md",
      "research-002-yaml-docs.md",
      "research-003-compatibility.md",
      "research-004-error-handling.md",
      "research-001.md"
    ],
    "summaries": [
      "research-summary.md"
    ]
  }
}
```

**Status Sync Manager Integration**:

```markdown
<stage id="4" name="Postflight">
  <action>Sync and summarize</action>
  <process>
    1. Use @subagents/specialists/status-sync-manager to atomically mark:
       - TODO.md: [RESEARCHED] status with Completed date
       - state.json: status="researched", research_mode="divided" or "standard"
       - Project state.json: phase="completed", status="researched"
    
    2. Add research links to TODO.md:
       - Standard: Link to research-001.md
       - Divided: Link to research-summary.md AND research-001.md
    
    3. Update project state with artifact paths and metadata
    
    4. Return artifact references and summary to orchestrator
  </process>
</stage>
```

**No Impact on Other Commands**:
- `/plan` reads research links from TODO.md (works with both standard and divided)
- `/implement` reads research links from TODO.md (works with both standard and divided)
- `/review` analyzes artifacts (works with both standard and divided)
- No changes needed to downstream commands

## Implementation Recommendations

### Phase 1: Command Updates (research.md)

**Priority**: High  
**Effort**: 1-2 hours  

**Changes**:
1. Update YAML front matter with --divide flag documentation
2. Add flag parsing logic in ParseInput stage
3. Add validation for --divide + batch mode (error)
4. Update usage examples
5. Pass divide_flag to researcher agent

**Files**:
- `.opencode/command/research.md`

### Phase 2: Researcher Agent Updates (researcher.md)

**Priority**: High  
**Effort**: 3-4 hours  

**Changes**:
1. Add stage 1.5 "SubdivideIfRequested" for topic subdivision
2. Update stage 2 "DelegateToSpecialists" for parallel subtopic research
3. Add stage 3.5 "AggregateSubtopicResults" for result collection
4. Update stage 3 "SynthesizeFindings" to handle both standard and divided modes
5. Update stage 4 "CreateSummary" to create aggregated summary (divided mode only)
6. Update lazy creation logic for summaries/ directory
7. Update return format to include research_mode metadata

**Files**:
- `.opencode/agent/subagents/researcher.md`

### Phase 3: State Tracking Updates

**Priority**: Medium  
**Effort**: 1 hour  

**Changes**:
1. Add research_mode field to state.json schema
2. Update status-sync-manager to track research_mode
3. Update TODO.md linking logic for divided research
4. Update project state.json schema with subtopic metadata

**Files**:
- `.opencode/context/core/system/state-schema.md`
- `.opencode/agent/subagents/specialists/status-sync-manager.md`

### Phase 4: Documentation Updates

**Priority**: Low  
**Effort**: 1 hour  

**Changes**:
1. Update artifact-management.md with --divide lazy creation rules
2. Update status-markers.md with research_mode tracking
3. Add --divide examples to user documentation
4. Update NAVIGATION.md with new feature

**Files**:
- `.opencode/context/core/system/artifact-management.md`
- `.opencode/context/core/standards/status-markers.md`
- `Documentation/NAVIGATION.md`

### Phase 5: Testing and Validation

**Priority**: High  
**Effort**: 2 hours  

**Test Cases**:
1. Standard research (no --divide): Verify unchanged behavior
2. Divided research (--divide): Verify subtopic generation, parallel execution, aggregation
3. Error handling: Verify batch + --divide error, partial subtopic failure
4. State tracking: Verify research_mode in state.json, TODO.md links
5. Lazy creation: Verify summaries/ only created with --divide
6. Backward compatibility: Verify existing /research invocations work

**Validation**:
- Token limits enforced (<500 for summary, <100 for return)
- Cross-references present in aggregated summary
- Metadata tracking complete
- Status transitions correct

## Further Research Needed

1. **Performance Optimization**: Investigate caching strategies for repeated subtopic research
2. **Subtopic Refinement**: Explore LLM-based subtopic generation vs rule-based
3. **User Feedback**: Gather feedback on optimal subtopic count (3-5 vs dynamic)
4. **Advanced Features**: Consider hierarchical subdivision for very complex topics
5. **Integration Testing**: Test --divide with downstream commands (/plan, /implement)

## Specialist Reports

- **Web Research**: [web-research-findings.md](web-research-findings.md)
- **Codebase Analysis**: Inline in this report

## Conclusion

The --divide flag can be implemented as an optional, backward-compatible enhancement to the /research command. The recommended approach uses 3-5 subtopics with vertical orchestration, parallel execution, and hierarchical summarization to protect context windows while providing comprehensive research coverage. Implementation requires updates to research.md (flag parsing), researcher.md (subdivision and coordination logic), and state tracking (research_mode metadata). The feature is additive with no breaking changes, requires no migration, and maintains full backward compatibility with existing research workflows.

**Estimated Total Effort**: 8-10 hours across 5 phases
