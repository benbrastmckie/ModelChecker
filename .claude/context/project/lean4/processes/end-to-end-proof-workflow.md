# End-to-End Proof Workflow

## Overview

This file outlines the standard workflow for developing a proof in Lean 4, from stating the theorem to finalizing the proof.

## When to Use

- When starting a new proof.
- When reviewing an existing proof.

## Prerequisites

- A clear statement of the theorem to be proven.
- A good understanding of the relevant mathematical concepts.

## Process Steps

### Step 0: Check for Literature Source

**Action**: Determine whether a literature source (paper, textbook, lecture notes) is provided for this proof.
**Validation**: If a source exists, identify the specific proof or argument to follow.
**Output**: Mode determination -- literature-guided or first-principles.

When a literature source is provided:
- Extract the proof structure from the source before proceeding to Step 1
- Steps 2-4 should follow the source's argument structure
- See `literature-fidelity-policy.md` for full policy details

### Step 1: State the Theorem

**Action**: Write the theorem statement in Lean 4 syntax.
**Validation**: The theorem statement should be well-formed and type-check.
**Output**: A theorem statement with a `sorry` proof.

### Step 2: Outline the Proof

**Action**: Write a high-level outline of the proof in comments. In literature-guided mode, extract the outline from the literature source rather than composing one independently.
**Validation**: The outline should be a valid argument for the theorem. In literature-guided mode, it should mirror the source's argument structure (same decomposition, same ordering).
**Output**: A commented proof outline, with literature step references when applicable.

### Step 3: Fill in the Proof

**Action**: Fill in the proof using tactics and term-mode proofs.
**Validation**: The proof should be complete and type-check.
**Output**: A complete proof.

### Step 4: Refactor the Proof

**Action**: Refactor the proof to improve readability and maintainability.
**Validation**: The refactored proof should be more concise and easier to understand.
**Output**: A clean and readable proof.

## Context Dependencies

- `lean4-syntax.md`
- `mathlib-overview.md`
- `key-mathematical-concepts.md`
- `literature-fidelity-policy.md`

## Success Criteria

- The proof is complete and correct.
- The proof is readable and maintainable.
- When a literature source is provided, the proof structure mirrors the source.
