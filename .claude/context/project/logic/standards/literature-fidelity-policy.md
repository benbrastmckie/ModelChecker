# Literature Fidelity Policy

## Overview

This policy defines when and how agents should follow provided literature sources versus deriving arguments from first principles. It applies to all formal domains: logic, mathematics, and physics.

Formal reasoning tasks fall into two categories based on whether a literature source (paper, textbook, lecture notes) is provided. The distinction matters because literature sources encode expert decisions about proof structure, lemma decomposition, and argument ordering that should not be casually discarded.

**Scope**: This policy governs the formal extension's three domains (logic, math, physics). It does not contain tool-specific or proof-assistant-specific guidance -- those belong in the respective extension policies (e.g., the Lean extension's literature fidelity policy).

## Two Modes

### Mode 1: Literature-Guided

**When to use**: A literature source is provided in the task description, research report, or implementation plan. The source contains a proof, argument, or construction that the task asks to formalize, reproduce, or verify.

**Core principle**: Follow the source's argument structure step-by-step. Translate each step faithfully into the target formalism. Do not seek shortcuts even when the argument appears difficult or verbose.

**Requirements**:
- Translate each literature step into a corresponding formal step
- Preserve the source's lemma decomposition and argument ordering
- Document which literature step each formal step corresponds to
- Do not skip, merge, or reorder steps without explicit justification
- When the source leaves a step implicit, make it explicit rather than skipping it

### Mode 2: First-Principles

**When to use**: No literature source is provided, or the task explicitly asks for an original approach. This is the default mode.

**Core principle**: Use standard proof strategies freely. Choose the approach that best fits the problem based on the proof-construction.md workflow and domain-specific strategy guides.

**Behavior**:
- Choose strategy based on goal structure (direct, indirect, induction, case analysis)
- Explore multiple approaches when the first attempt fails
- Apply automation and search freely
- Follow proof-construction.md Phase 1-4 workflow as normal

## Activation Criteria

Literature-guided mode activates when ANY of the following conditions hold:

1. **Task description** references a paper, textbook, or notes by title, author, or citation
2. **Plan phases** are labeled with literature section numbers, theorem numbers, or page references
3. **Research report** documents a proof structure extracted from a source
4. **User instruction** explicitly asks to "follow the proof in [source]" or similar

When activation is ambiguous (e.g., a source is mentioned for background but not as the proof to follow), ask the user which mode to use rather than guessing.

## Step Translation Protocol

For each literature step in literature-guided mode:

### 1. Identify the Claim

Extract the precise mathematical or logical claim the step establishes. Distinguish between:
- The main claim of the step
- Side conditions or implicit assumptions
- Notational conventions specific to the source

### 2. Determine the Formal Encoding

Map the source's notation and concepts to the target formalism:
- Identify the corresponding definitions in the codebase
- Note any representational gaps (concepts the source uses that have no direct formal counterpart)
- Choose the encoding that most faithfully preserves the source's meaning

### 3. Construct the Formal Argument

Build the formal proof or construction for that step:
- Mirror the source's reasoning as closely as the formalism allows
- If the source uses a technique, use the same technique formally
- Add intermediate steps where the source relies on "obvious" claims

### 4. Annotate the Correspondence

Document the mapping between source and formal artifact:
- Reference the specific theorem/lemma/page number from the source
- Note any deviations, however minor, from the source's approach
- Flag steps where the formal version required additional detail

### 5. Verify Before Proceeding

Confirm the step is correct before moving to the next:
- Check that the formal claim matches the source's claim
- Verify the formal argument is valid
- Ensure no assumptions were introduced that the source does not use

If verification fails, enter the Escalation Protocol.

## Escalation Protocol

When a literature step does not translate cleanly into the target formalism, follow this decision tree in order:

### Level 1: Re-Read the Source

Return to the original text and re-read the step in its full context. Common resolutions:
- The source defined a term earlier that was forgotten
- A preceding lemma establishes a fact the step relies on
- The notation has a specific meaning in the source's conventions

### Level 2: Try Alternative Encodings

The same mathematical claim can often be encoded multiple ways. Try:
- Different but equivalent definitions
- Equivalent formulations of the same property
- Alternative decompositions that still mirror the source's intent

### Level 3: Check for Unstated Lemmas

Many sources omit "routine" steps. The gap may require:
- A well-known lemma the source considers obvious
- A technical fact specific to the domain
- A property that follows from earlier definitions

Identify and prove these subsidiary claims explicitly.

### Level 4: Document the Gap

If Levels 1-3 do not resolve the issue:
- Record precisely which source step fails to translate
- State what was tried and why each attempt failed
- Identify whether the gap is a representational issue (encoding mismatch) or a mathematical issue (the source may contain an error or unstated assumption)

### Level 5: Ask the User

Present the documented gap to the user with:
- The specific source step that does not translate
- The attempts made and their failure modes
- A proposed resolution (if any)
- A clear question about how to proceed

**NEVER improvise a novel argument to fill a gap without flagging it.** Silent deviation from the source is the primary failure mode this policy prevents.

## Anti-Pattern Catalog

### Anti-Pattern 1: Skipping Steps

**FORBIDDEN**: Omitting difficult intermediate steps from the literature because they are hard to formalize.

WRONG: "Steps 3-5 in the proof are routine, so I'll skip to step 6."
RIGHT: "Steps 3-5 are technically involved. I'll formalize each one, adding intermediate lemmas where the source is terse."

**Why it matters**: Steps that appear routine in informal mathematics often contain the deepest formal challenges. Skipping them creates gaps that compound in later steps.

### Anti-Pattern 2: Novel Arguments

**FORBIDDEN**: Inventing a different proof or argument when the literature's approach is the one being formalized.

WRONG: "The source uses a canonical model construction, but I found an easier algebraic argument."
RIGHT: "The source uses a canonical model construction. I'll follow that approach, even though alternatives exist, because the task is to formalize THIS proof."

**Why it matters**: The task is to formalize the source's argument, not to find the easiest proof. Novel arguments may be correct but fail to validate the source.

### Anti-Pattern 3: Premature Automation

**FORBIDDEN**: Using broad automation or search to bypass steps that the literature handles explicitly.

WRONG: "I'll use automated reasoning to close this goal instead of following the source's explicit construction."
RIGHT: "The source explicitly constructs the witness. I'll mirror that construction, using automation only for the parts the source treats as trivial."

**Why it matters**: Automation can obscure whether the formal proof actually follows the source's reasoning. When the task is literature-guided, the structure of the proof matters, not just its conclusion.

### Anti-Pattern 4: Abandoning After First Failure

**FORBIDDEN**: Switching to a novel approach after a single encoding attempt fails to work.

WRONG: "The source's approach didn't work with my first encoding, so I'll try a completely different proof strategy."
RIGHT: "The first encoding failed. I'll try alternative encodings of the same mathematical claim before considering whether the source's approach is viable in this formalism."

**Why it matters**: Encoding mismatches are common and rarely indicate that the source's approach is wrong. Multiple faithful attempts should precede any deviation.

### Anti-Pattern 5: Mixing Strategies Without Flagging

**FORBIDDEN**: Silently combining literature steps with novel steps, producing a hybrid argument that neither follows the source nor stands alone.

WRONG: "I followed steps 1-4 from the source, then used a different approach for steps 5-7 because they were easier."
RIGHT: "I followed steps 1-4 from the source. Steps 5-7 required deviation because [specific reason]. The deviation is documented in the step annotations."

**Why it matters**: Hybrid arguments that silently diverge from the source are the hardest to review. Explicit flagging lets reviewers assess whether the deviation is justified.

## Domain-Specific Guidance

### Logic

**Canonical model constructions**: When the source constructs a canonical model for completeness, follow the construction exactly:
- Use the source's definition of maximally consistent sets
- Follow the source's accessibility relation definition
- Mirror the source's truth lemma proof structure (typically by induction on formula complexity)
- Do not substitute alternative model constructions (e.g., do not use a filtration when the source uses canonical models)

**Induction structure**: When the source proves a property by induction:
- Use the same induction variable (formula complexity, derivation length, etc.)
- Follow the same case analysis breakdown
- If the source handles base cases before inductive cases, maintain that order

**Frame conditions**: When the source establishes frame properties:
- Use the source's characterization of the accessibility relation
- Follow the source's verification that the frame satisfies the required conditions
- Do not substitute equivalent but differently-structured frame conditions

### Mathematics

**Lemma decomposition**: When the source breaks a proof into lemmas:
- Formalize the same lemma boundaries, do not merge lemmas
- If the source proves Lemma A, then Lemma B, then combines them, follow that structure
- Auxiliary constructions should mirror the source's constructions

**Topological arguments**: When the source uses topological reasoning:
- Preserve the source's choice of open vs. closed set characterization
- Follow the source's construction of topological witnesses (open covers, compact subsets)
- Do not substitute equivalent characterizations without flagging (e.g., do not switch from nets to filters unless the formalism requires it)

**Category-theoretic proofs**: When the source reasons diagrammatically:
- Follow the source's diagram exactly, including the choice of arrows and objects
- Do not factor morphisms through different intermediate objects
- Preserve the source's use of universal properties vs. explicit constructions

### Physics

**Dynamical systems**: When the source constructs orbits or trajectories:
- Follow the source's iteration scheme step-by-step
- Use the source's convergence criteria, not alternative sufficient conditions
- Mirror the source's treatment of boundary cases and exceptional orbits

**Fixed point arguments**: When the source establishes fixed points:
- Use the source's contraction mapping or continuity conditions
- Follow the source's construction of the fixed point (iteration, Zorn's lemma, etc.)
- Do not substitute alternative fixed point theorems without flagging

## Interaction with Existing Processes

This policy interacts with three existing formal extension documents:

### proof-construction.md

The "Choose Strategy" section lists direct proof, indirect proof, induction, and case analysis. In literature-guided mode, the strategy is determined by the source: "follow the reference." The strategy choice in proof-construction.md applies only in first-principles mode.

### verification-workflow.md

Verification in literature-guided mode has an additional dimension: checking correspondence to the source's steps. Beyond the standard verification of correctness, each formal step should be verified against the literature step it claims to implement.

### proof-conventions.md

The existing docstring and annotation conventions apply in both modes. In literature-guided mode, literature step annotations (theorem/lemma/page references) supplement the existing step comment requirements from proof-conventions.md.

## Success Criteria

Use this checklist to verify literature-guided work:

- [ ] Every formal step has a documented correspondence to a literature step
- [ ] No literature steps were skipped or merged without explicit documentation
- [ ] No novel arguments were introduced without flagging the deviation
- [ ] Escalation protocol was followed for any gaps (documented at the appropriate level)
- [ ] Deviations from the literature, if any, are explicitly documented with justification
- [ ] The formal proof structure mirrors the source's argument structure
- [ ] Domain-specific guidance for the relevant domain was followed
- [ ] All implicit source steps were made explicit in the formalization
