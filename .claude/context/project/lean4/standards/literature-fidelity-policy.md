# Literature Fidelity Policy

## Overview

This policy governs how lean-implementation-agent and lean-research-agent handle provided literature sources (papers, textbooks, lecture notes, proof sketches). When a literature source is referenced in the task description, research report, or plan artifacts, agents must follow it step-by-step. When no literature is provided, agents operate freely under existing standards.

## Mode Detection

### Literature-Guided Mode

Activated when ANY of these conditions hold:
- Task description references a paper, textbook, or proof sketch
- Research report extracts a proof structure from a literature source
- Plan artifacts include step-by-step proof outlines attributed to a source
- User explicitly requests "follow the book/paper/notes"

### First-Principles Mode

Default when no literature source is identified. Current behavior applies without restriction: tactic exploration, MCP search, automation, and novel proof strategies are all permitted.

## Literature-Guided Mode

### Core Principle

Follow the source step-by-step. Do not seek shortcuts. The user chose this reference for a reason -- respect that choice even when the proof is difficult or a seemingly easier path exists.

### Source Identification

What counts as a literature source:
- Published papers (arXiv, journals, conference proceedings)
- Textbooks and monographs
- Lecture notes provided by the user
- Proof sketches included in task descriptions or research reports
- Formalized proofs from other proof assistants (Coq, Isabelle, Agda)

### Translation Protocol

For each step in the literature proof:

1. **Read** the literature step carefully and completely
2. **Identify** the mathematical claim being made
3. **Find** the corresponding Lean type, lemma, or tactic
4. **Apply directly** if an exact Lean match exists
5. **Find equivalent formulation** if the encoding differs (e.g., different but isomorphic types)
6. **Escalate** if no faithful translation exists -- do NOT skip the step

### Deviation Handling

When deviating from the literature is genuinely necessary:
- Document the deviation in a code comment citing the original step
- Flag it to the user with explanation of why the deviation was required
- Never silently substitute a different approach

## Anti-Pattern Catalog

### FORBIDDEN: Shortcut-Seeking

**Pattern**: "The literature proof uses a manual induction argument, but `omega`/`simp`/`aesop` might close this goal faster."

**Why this is wrong**: Bypassing the literature's proof structure defeats the purpose of following a reference. The user wants the proof to mirror the source, not just any proof that type-checks.

**What to do instead**: Translate the literature's induction step faithfully into Lean's `induction` tactic with explicit case handling matching the source.

### FORBIDDEN: Easier-Route Substitution

**Pattern**: "The literature's approach is complex; I'll find an easier route using Mathlib lemmas the author didn't use."

**Why this is wrong**: Discards the user's chosen reference. The literature's approach may be pedagogically important, structurally informative, or prerequisite for later steps.

**What to do instead**: Follow the reference approach. If a Mathlib lemma directly corresponds to a literature step, use it -- but do not reorganize the proof structure.

### FORBIDDEN: Premature Abandonment

**Pattern**: Trying one tactic encoding of a literature step, failing, then declaring the step untranslatable and switching to a novel approach.

**Why this is wrong**: A single tactic failure does not mean the mathematical step is wrong or untranslatable. Lean encodings vary; the step likely needs a different formulation, not a different strategy.

**What to do instead**: Try at least three alternative Lean encodings before concluding the step resists translation. Then escalate per the protocol below.

### FORBIDDEN: Silent Mixing

**Pattern**: Following steps 1-3 from the literature, then inserting novel steps 4-5 without attribution, then resuming at literature step 6.

**Why this is wrong**: Makes the proof untraceable to the source. The user cannot verify which parts follow the reference and which are agent inventions.

**What to do instead**: Mark any deviation with `-- NOTE: deviates from [source], step N` and flag to the user.

## Escalation Protocol

When stuck on a literature step, follow this sequence strictly:

1. **Re-read the source** carefully -- often the issue is misunderstanding the step, not a translation barrier
2. **Try alternative Lean encodings** of the same mathematical step (different tactic sequences, term-mode vs tactic-mode, alternative type formulations)
3. **Check for intermediate lemmas** not stated in the source but implied (e.g., a step that assumes a fact the author considers obvious)
4. **Search for existing Lean/Mathlib formulations** of the concept (`lean_leansearch`, `lean_loogle`, `lean_local_search`)
5. **Flag the gap to the user** with:
   - The specific literature step that resists translation
   - What encodings were tried and why they failed
   - The current proof state (`lean_goal` output)
6. **NEVER skip the step and continue** to the next one -- an incomplete proof with a documented gap is better than a "complete" proof that silently omits a step

## First-Principles Mode

When no literature source is provided, all existing standards apply without additional restriction:
- Tactic exploration and automation (`simp`, `omega`, `aesop`) are freely permitted
- MCP search tools (`lean_leansearch`, `lean_loogle`, `lean_state_search`) can guide strategy
- Novel proof approaches are encouraged
- No attribution or deviation tracking is required

This policy adds no constraints in first-principles mode.

## Usage Checklist

- [ ] Literature source identified in task description, research, or plan (if provided)
- [ ] Correct mode determined (literature-guided vs. first-principles)
- [ ] Each literature step translated faithfully before trying alternatives
- [ ] No shortcuts taken over literature steps (no FORBIDDEN patterns)
- [ ] Deviations documented in code comments and flagged to user
- [ ] Escalation protocol followed when a step resists translation
- [ ] Proof structure mirrors the source's structure (same ordering, same decomposition)

## Cross-References

- `proof-debt-policy.md` -- Complementary policy: debt = "no sorries", fidelity = "follow the source"
- `proof-conventions-lean.md` -- Style and documentation conventions for Lean proofs
- `end-to-end-proof-workflow.md` -- Overall proof development workflow
