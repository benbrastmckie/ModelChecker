# Implementation Plan: Task #6

**Task**: Create model-checker researcher skill
**Version**: 001
**Created**: 2026-01-11
**Language**: meta

## Overview

Create a comprehensive skill for ModelChecker researchers that streamlines common workflows: defining operators, adjusting frame constraints, creating examples, running tests, and reporting findings. The skill will be invoked via `/mc` and provide sub-commands for each workflow type.

Based on research findings, the skill should leverage:
- Existing theory structure patterns (semantic.py, operators.py, examples.py)
- TDD workflow requirements
- Z3 constraint patterns
- Settings system for example configuration

## Phases

### Phase 1: Core Skill Structure

**Status**: [NOT STARTED]

**Objectives**:
1. Create skill directory and SKILL.md file
2. Define skill metadata and allowed tools
3. Create main skill prompt with workflow overview
4. Register skill in the system

**Files to create**:
- `.claude/skills/skill-model-checker/SKILL.md` - Main skill definition

**Steps**:
1. Create `.claude/skills/skill-model-checker/` directory
2. Write SKILL.md with frontmatter (name, description, allowed-tools)
3. Define the main skill workflow and sub-command routing
4. Document the `/mc` command invocation pattern

**Verification**:
- Skill file exists with valid frontmatter
- Skill appears in available skills list

---

### Phase 2: Operator Definition Workflow

**Status**: [NOT STARTED]

**Objectives**:
1. Document operator creation workflow
2. Provide code templates for operator classes
3. Define TDD steps for operator implementation
4. Include operator registration guidance

**Files to modify**:
- `.claude/skills/skill-model-checker/SKILL.md` - Add operator workflow section

**Steps**:
1. Add `/mc operator <name>` sub-command documentation
2. Include Operator class template with all semantic methods:
   - `true_at`, `false_at`
   - `extended_verify`, `extended_falsify`
   - `find_verifiers_and_falsifiers`
   - `print_method`
3. Document operator registration in operators.py
4. Add test template for operator tests
5. Include common Z3 patterns for operators

**Verification**:
- Operator workflow section complete with templates
- Code examples are syntactically correct

---

### Phase 3: Frame Constraints Workflow

**Status**: [NOT STARTED]

**Objectives**:
1. Document frame constraint modification workflow
2. Provide constraint templates
3. Explain semantic class extension patterns
4. Include common constraint patterns

**Files to modify**:
- `.claude/skills/skill-model-checker/SKILL.md` - Add frame constraints section

**Steps**:
1. Add `/mc frame` sub-command documentation
2. Document SemanticDefaults extension pattern
3. Include templates for common constraints:
   - Possibility downward closure
   - World constraints
   - Verifier/falsifier constraints
4. Add Z3 quantifier patterns (ForAll, Exists)
5. Document constraint testing approach

**Verification**:
- Frame constraints section complete
- Constraint examples are valid Z3

---

### Phase 4: Example Creation Workflow

**Status**: [NOT STARTED]

**Objectives**:
1. Document example definition workflow
2. Provide example templates for countermodels and theorems
3. Explain settings options
4. Include naming conventions

**Files to modify**:
- `.claude/skills/skill-model-checker/SKILL.md` - Add examples section

**Steps**:
1. Add `/mc example` sub-command documentation
2. Document example naming convention (SUBTHEORY_TYPE_NUMBER)
3. Include templates for:
   - Countermodel examples (CM)
   - Theorem examples (TH)
4. Document all settings options:
   - N, contingent, non_null, non_empty, disjoint
   - max_time, iterate, expectation
5. Explain example organization patterns

**Verification**:
- Examples section complete with templates
- Settings documentation is comprehensive

---

### Phase 5: Testing Workflow

**Status**: [NOT STARTED]

**Objectives**:
1. Document test execution commands
2. Provide test templates
3. Explain TDD workflow
4. Include troubleshooting guidance

**Files to modify**:
- `.claude/skills/skill-model-checker/SKILL.md` - Add testing section

**Steps**:
1. Add `/mc test` sub-command documentation
2. Document all test commands:
   - All tests: `PYTHONPATH=Code/src pytest Code/tests/ -v`
   - Specific theory: `PYTHONPATH=Code/src pytest Code/src/model_checker/theory_lib/{theory}/tests/ -v`
   - With coverage: `pytest --cov=model_checker --cov-report=term-missing`
3. Include pytest fixture templates
4. Add test organization patterns
5. Document common test failures and fixes

**Verification**:
- Testing section complete
- Commands are accurate and tested

---

### Phase 6: Reporting Workflow

**Status**: [NOT STARTED]

**Objectives**:
1. Document result reporting workflow
2. Provide report templates
3. Explain model interpretation
4. Include theory comparison approach

**Files to modify**:
- `.claude/skills/skill-model-checker/SKILL.md` - Add reporting section

**Steps**:
1. Add `/mc report` sub-command documentation
2. Document model output interpretation:
   - Countermodel structure
   - Verifier/falsifier assignments
   - World/state relationships
3. Include report template for findings
4. Document theory comparison workflow
5. Add result export options (--save, --maximize)

**Verification**:
- Reporting section complete
- Model interpretation guidance is clear

---

### Phase 7: Reference Materials

**Status**: [NOT STARTED]

**Objectives**:
1. Add formula syntax reference
2. Include operator quick reference
3. Add settings cheat sheet
4. Provide common patterns summary

**Files to modify**:
- `.claude/skills/skill-model-checker/SKILL.md` - Add reference section

**Steps**:
1. Create formula syntax reference with LaTeX operators
2. Add quick reference table for all operators by subtheory:
   - extensional, modal, constitutive, counterfactual, relevance
3. Include settings quick reference table
4. Add common workflow patterns summary
5. Cross-reference to full documentation

**Verification**:
- Reference materials complete
- Operator list matches codebase

---

### Phase 8: Skill Integration

**Status**: [NOT STARTED]

**Objectives**:
1. Register skill in available commands
2. Update CLAUDE.md with skill reference
3. Test skill invocation
4. Create usage examples

**Files to modify**:
- `.claude/CLAUDE.md` - Add skill reference (if needed)
- `.claude/skills/skill-model-checker/SKILL.md` - Finalize

**Steps**:
1. Verify skill frontmatter is complete
2. Test `/mc` invocation pattern
3. Verify sub-commands work:
   - `/mc operator`
   - `/mc frame`
   - `/mc example`
   - `/mc test`
   - `/mc report`
4. Add usage examples section
5. Final review and polish

**Verification**:
- Skill appears in available skills
- All sub-commands documented
- Usage examples work as expected

## Dependencies

- Research report from task 6
- Existing skill structure patterns
- ModelChecker codebase documentation

## Risks and Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Skill format incompatibility | High | Low | Follow existing skill patterns exactly |
| Incomplete operator coverage | Medium | Medium | Cross-reference all operators in codebase |
| Z3 pattern errors | Medium | Low | Validate all code examples |
| Workflow gaps | Low | Medium | Test with real use cases |

## Success Criteria

- [ ] Skill file created at `.claude/skills/skill-model-checker/SKILL.md`
- [ ] All 5 sub-workflows documented (operator, frame, example, test, report)
- [ ] Code templates are syntactically correct
- [ ] Reference materials cover all operators
- [ ] Skill invocable via `/mc` command
- [ ] Documentation cross-references existing guides

## Rollback Plan

If implementation fails:
1. Remove `.claude/skills/skill-model-checker/` directory
2. Revert any changes to CLAUDE.md
3. Task remains in PLANNED status for retry
