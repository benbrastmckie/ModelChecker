# Research Report: Task #6 (Supplementary)

**Task**: Create model-checker researcher skill
**Date**: 2026-01-11
**Focus**: Skill architecture - single unified skill vs. multiple specialized skills

## Summary

Research on Claude Code skills best practices indicates that **a single unified model-checker skill is the recommended approach** for this use case. The key principle is that skills should be domain-specific rather than technique-specific. The workflows (operator definition, frame constraints, examples, testing, reporting) are tightly coupled and form a cohesive domain. Separating them would fragment context that is naturally needed together.

## Findings

### 1. Skills Best Practices from Official Documentation

Key insights from Claude Code documentation and Anthropic engineering blog:

**Single Responsibility = Domain, Not Technique**
- Skills should teach Claude to do "one thing well" - but "one thing" means a cohesive domain
- Example: document skills are separated as PDF, DOCX, PPTX - by document type (domain), not by "text extraction" vs "form filling" (technique)
- The model-checker is a single domain; Z3, TDD, theory patterns are techniques used within that domain

**Progressive Disclosure Architecture**
- Skills use three levels: metadata (always loaded), core SKILL.md (~500 lines max), supplementary files (on-demand)
- A unified skill with supplementary reference files is more token-efficient than multiple skills
- Multiple skills would each add metadata overhead and potentially load redundant context

**Skills Compose Automatically**
- Claude identifies needed skills from descriptions and loads them
- If a user is working with model-checker, they need all the pieces together
- Splitting into skill-z3, skill-tdd, skill-theory-patterns would require loading 3+ skills for every model-checker task

### 2. Analysis of Existing ModelChecker Skills

Current skill architecture patterns in `.claude/skills/`:

| Skill | Domain | Observations |
|-------|--------|-------------|
| skill-python-research | Python/Z3 research for ModelChecker | Already unified - includes Z3, codebase, testing patterns |
| skill-theory-implementation | Semantic theory implementation | Already unified - includes TDD, operator creation, tests |
| skill-researcher | General research | Unified by function (research), not by topic |
| skill-planner | Planning tasks | Unified by function (planning) |
| skill-orchestrator | Task routing | Unified by function (routing) |

**Key observation**: The existing skills are organized by **function** (research, implement, plan) or **domain** (Python/Z3, theories), not by **technique** (TDD, Z3 specifically).

### 3. Workflow Coupling Analysis

Evaluating whether model-checker workflows should be separate:

| Workflow | Dependencies | Use Alone? | Verdict |
|----------|-------------|------------|---------|
| Operator definition | Needs theory patterns, Z3 semantics, TDD testing | Rarely | Keep together |
| Frame constraints | Needs Z3 quantifiers, semantic class patterns | Never | Keep together |
| Example creation | Needs settings system, naming conventions | Sometimes | Could separate, but overhead not worth it |
| Testing | Needs pytest, theory fixtures, TDD workflow | Always needed | Keep together |
| Reporting | Needs model interpretation, result formatting | Sometimes | Could separate, but tightly coupled |

**Conclusion**: These workflows are interdependent. Creating an operator requires understanding frame constraints, writing tests, and creating examples. Separating them would fragment naturally connected knowledge.

### 4. Alternative Architectures Considered

**Option A: Single Unified Skill (Recommended)**
```
.claude/skills/skill-model-checker/
├── SKILL.md            # Core guidance (~400 lines)
├── reference/
│   ├── operators.md    # Full operator list
│   ├── settings.md     # All settings options
│   └── z3-patterns.md  # Z3 code patterns
└── templates/
    ├── operator.py.template
    └── example.py.template
```
- **Pros**: Single context load, coherent guidance, supports progressive disclosure
- **Cons**: Larger initial SKILL.md (but under 500 line limit)

**Option B: Multiple Specialized Skills (Not Recommended)**
```
.claude/skills/skill-mc-operator/SKILL.md
.claude/skills/skill-mc-frame/SKILL.md
.claude/skills/skill-mc-example/SKILL.md
.claude/skills/skill-mc-test/SKILL.md
.claude/skills/skill-mc-report/SKILL.md
```
- **Pros**: Each skill smaller
- **Cons**:
  - 5x metadata overhead
  - Context fragmentation (operator needs theory patterns from frame skill)
  - User must invoke multiple skills or rely on complex auto-detection
  - Harder to maintain consistency across skills

**Option C: Domain + Technique Split (Not Recommended)**
```
.claude/skills/skill-z3-patterns/SKILL.md      # Z3 technique
.claude/skills/skill-tdd-python/SKILL.md       # TDD technique
.claude/skills/skill-model-checker/SKILL.md    # Domain (thin wrapper)
```
- **Pros**: Z3 and TDD skills reusable elsewhere
- **Cons**:
  - Z3 patterns for model-checker are specialized (BitVec semantics, verification functions)
  - TDD is already covered by skill-theory-implementation
  - Creates skill coordination complexity

### 5. Token Efficiency Analysis

Estimated token usage:

| Architecture | Per-Activation Tokens | Notes |
|--------------|----------------------|-------|
| Single skill | ~2,500 | SKILL.md loads once, reference files on-demand |
| 5 split skills | ~4,000+ | Each skill loads separately, some overlap |
| Domain+technique | ~3,500+ | Must coordinate multiple contexts |

Single skill is most efficient when the domain is coherent.

## Recommendations

### Primary Recommendation: Single Unified Skill

Create **one `skill-model-checker` skill** with:

1. **Core SKILL.md** (~400 lines) containing:
   - Quick start and workflow overview
   - Sub-command documentation (/mc operator, /mc frame, etc.)
   - Essential patterns inline
   - Pointers to reference files

2. **Reference files** (loaded on-demand):
   - `reference/operators.md` - Full operator catalog
   - `reference/settings.md` - Complete settings reference
   - `reference/z3-patterns.md` - Z3 code patterns and examples
   - `reference/testing.md` - pytest patterns for model-checker

3. **Templates** (for code generation):
   - `templates/operator.py.template` - Operator class skeleton
   - `templates/example.py.template` - Example definition pattern

### Supporting Rationale

1. **Domain cohesion**: Model-checker is a single domain where all workflows interrelate
2. **Token efficiency**: Single context load with progressive disclosure
3. **User experience**: One skill to learn and invoke
4. **Maintenance**: Single source of truth for model-checker guidance
5. **Alignment with existing patterns**: Matches skill-python-research and skill-theory-implementation structure

### What NOT to Do

- Don't create separate skill-z3-patterns - too generic, model-checker Z3 is specialized
- Don't create separate skill-tdd-python - already covered by skill-theory-implementation
- Don't split by workflow - creates fragmented context and coordination overhead

## References

- [Agent Skills - Claude Code Docs](https://code.claude.com/docs/en/skills)
- [Introducing Agent Skills | Claude](https://claude.com/blog/skills)
- [How to create Skills for Claude](https://claude.com/blog/how-to-create-skills-key-steps-limitations-and-examples)
- [Anthropic Skills Best Practices](https://www.anthropic.com/engineering/equipping-agents-for-the-real-world-with-agent-skills)
- Existing skills: skill-python-research, skill-theory-implementation

## Next Steps

1. Proceed with implementation plan for single unified skill
2. Consider adding reference/ subdirectory for detailed documentation
3. Create templates/ for code generation support
4. Keep SKILL.md under 500 lines with pointers to reference files
