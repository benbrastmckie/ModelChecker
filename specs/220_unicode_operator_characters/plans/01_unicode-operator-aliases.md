# Implementation Plan: Unicode operator aliases

- **Task**: 220 - Implement user-specifiable unicode characters for operators in theory operators.py files with infix or prefix form
- **Status**: [NOT STARTED]
- **Effort**: 7.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/220_unicode_operator_characters/reports/01_unicode-operator-characters.md
- **Artifacts**: plans/01_unicode-operator-aliases.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

Give theory authors a way to declare, directly in a theory's `operators.py`, one or more
user-chosen Unicode glyphs that parse to the same operator class as its canonical LaTeX name.
The mechanism is a new optional `aliases: List[str]` class attribute on
`syntactic.Operator`, registered alongside `Operator.name` by
`OperatorCollection.add_operator`; the parser itself needs no changes, because research
confirmed `utils/parsing.py`, `syntactic/sentence.py`, and `syntactic/syntax.py` are already
fully generic with respect to operator-name spelling for arity-1 (prefix) and arity-2 (infix)
operators. Done means: a theory can ship `name = "\\wedge"` plus `aliases = ["∧"]`, both
spellings parse and evaluate identically through the `model-checker`/`dev_cli.py` CLI, every
existing LaTeX formula in `examples.py`/tests/docs still works unchanged, alias collisions fail
loudly at theory-load time, and `docs/usage/OPERATORS.md` no longer contradicts the new
capability.

### Research Integration

Key findings carried into this plan from
`specs/220_unicode_operator_characters/reports/01_unicode-operator-characters.md`:

- The parser is already Unicode-agnostic. `parse_expression`'s final fallback branch handles any
  non-paren, non-alnum, non-backslash token as a unary prefix operator, and `op_left_right`
  imposes no spelling restriction on the infix operator token. `syntactic/tests/unit/test_operators.py`
  and `test_syntax.py` already use `name = "∧"`, `"∨"`, `"¬"` as fixtures. **No parser changes
  are planned** (Phases 1-6 touch no file under `utils/parsing.py`, `syntactic/sentence.py`, or
  `syntactic/syntax.py`).
- The single bottleneck is `OperatorCollection.add_operator`, whose only dictionary write is
  `self.operator_dictionary[operator.name] = operator`. Dict keys chosen by a theory's
  `get_operators()` are discarded, so extra dict keys are *not* a viable alias route.
- `DuplicateOperatorError` and `UnknownOperatorError` are imported by
  `syntactic/collection.py` but never raised: duplicates silently `return`, unknown lookups raise
  a bare `KeyError`. Both are wired up in Phase 2.
- `jupyter/unicode.py`'s `UNICODE_OPERATOR_EXTENSIONS` and `builder/translation.py`'s
  `semantic_theory["dictionary"]` are prior art at the wrong layer (notebook display; whole-string
  pre-parse substitution in `examples.py`). Neither is built on or modified by this plan.
- `\top`/`\bot` (the only arity-0 operators, hardcoded by literal string at 8+ call sites) are a
  declared non-goal, per the task's own "infix or prefix form" phrasing.

### Prior Plan Reference

No prior plan. This is the first plan for this task (`next_artifact_number: 2`, round 1).

### Roadmap Alignment

No `roadmap_path` was supplied in this dispatch's delegation context, so `specs/ROADMAP.md` was
not loaded as roadmap context and no roadmap phases are included. A read-only relevance check
found no roadmap item covering operator notation; the only `operators.py` mention concerns the
canonical theory module set, which this plan does not alter.

## Goals & Non-Goals

**Goals**:
- Add an optional `aliases: List[str] = []` class attribute to `syntactic.Operator`, documented
  alongside `name`/`arity`/`primitive`.
- Extend `OperatorCollection.add_operator` to register the operator class under each alias in
  addition to its canonical `name`, with no change to canonical-name behavior.
- Make alias/name collisions fail loudly at theory-load time via `DuplicateOperatorError`, while
  keeping idempotent re-registration of the *same* class a silent no-op (required by
  `builder/serialize.py::deserialize_operators` and by `OperatorCollection`-merge).
- Raise `UnknownOperatorError` (with its `available_operators` suggestion list) instead of a bare
  `KeyError` when a formula uses an unregistered operator or a mistyped alias.
- Deliberately resolve `is_syntactically_wff`'s accidental acceptance of non-backslash operator
  heads through the "atomic sentence letter" branch.
- Adopt Unicode aliases in the shipped theories' `operators.py` files for arity-1/arity-2
  operators that have a standard glyph.
- Update `docs/usage/OPERATORS.md` so its "LaTeX Notation Requirements", "Best Practices", and
  "Troubleshooting" guidance no longer asserts the now-false "never use Unicode" rule.

**Non-Goals**:
- Aliasing the nullary `\top`/`\bot` constants. They are matched by hardcoded string literal at
  8+ call sites across `utils/parsing.py`, `syntactic/formulas.py`, `syntactic/sentence.py`,
  `syntactic/syntax.py`, `syntactic/collection.py`, `bimodal/semantic/formula.py`, and
  `logos/subtheories/counterfactual/frame_oracle.py`. Out of scope; a separate follow-up task.
- Changing `utils/parsing.py`, `syntactic/sentence.py`, or `syntactic/syntax.py` at all.
- Changing, extending, or wiring in `jupyter/unicode.py` / `UNICODE_OPERATOR_EXTENSIONS`, or
  `builder/translation.py`'s `dictionary` translation mechanism.
- A settings-file, environment-variable, or CLI-flag route for choosing notation. The task
  specifies the choice lives in `operators.py`.
- Changing any existing `examples.py` formula from LaTeX to Unicode. Backward compatibility of
  every existing LaTeX formula is a hard constraint, not an optional nicety.

## Decisions

Three points the research report explicitly deferred to the planner are resolved here so the
implementer does not re-litigate them:

1. **Duplicate policy is conflict-aware, not blanket-raise.** The report recommended switching
   `add_operator` to raise `DuplicateOperatorError` on any duplicate. That would break
   `builder/serialize.py::deserialize_operators`, which iterates *every* key of the serialized
   dictionary and calls `add_operator(op_class)` once per key — with aliases, the same class is
   re-registered N+1 times. The same applies to `add_operator(other_collection)` merging. The
   policy is therefore: re-registering the **same class** under a key it already owns is a silent
   no-op (current behavior preserved); registering a **different class** under an already-taken
   name or alias raises `DuplicateOperatorError`.
2. **`is_syntactically_wff` is tightened by structure, not by registry lookup.** The current
   `isinstance(head, str) and not head.startswith('\\')` branch accepts `["∧", ["p"], ["q"]]`
   through the "atomic sentence letter" path — the right answer for the wrong reason. The fix is
   to gate that branch on `len(prefix) == 1`, and add an explicit branch accepting a non-backslash
   string head with arguments as a connective. The function stays pure and registry-free (it has
   no access to an `OperatorCollection` today, and giving it one would change its signature and
   every call site). Unknown-operator detection remains the job of `OperatorCollection.__getitem__`
   (Phase 2), which is where it belongs.
3. **Alias adoption in shipped theories is curated, not exhaustive.** Only operators with a
   widely recognized Unicode glyph get an alias; theory-specific operators with no standard glyph
   (e.g. `\boxrightlogos`, `\diamondrightlogos`) get none, and this is recorded as an explicit
   comment rather than left unexplained.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Blanket `DuplicateOperatorError` breaks `deserialize_operators` (re-adds same class once per alias key) and `OperatorCollection` merge | H | H | Decision 1: conflict-aware duplicate policy (same class = no-op, different class = raise). Phase 2 adds a regression test exercising serialize/deserialize round-trip on an aliased collection. |
| Mutable class-attribute default (`aliases = []`) shared across all `Operator` subclasses | H | M | Declare as an immutable-by-convention empty list on the base class, never mutate it in place; `add_operator` reads via `getattr(operator, "aliases", []) or []` and never appends to it. Phase 1 adds a test asserting one subclass's aliases do not leak to a sibling. |
| Tightening `is_syntactically_wff` regresses formula validation — it is called on *every* `Sentence` via `_validate_well_formedness` | H | M | Phase 3 is `full` tier, TDD-first, with characterization tests written for the existing accepted/rejected shapes *before* the change; full suite run in Phase 6. |
| Alias collision between subtheories loaded together (e.g. logos constitutive `\equiv` and another subtheory wanting `≡`) | M | M | Phase 2's `DuplicateOperatorError` surfaces the collision at load time with the conflicting class named; Phase 4 runs each theory's examples to prove no shipped combination collides. |
| `UnknownOperatorError` replacing `KeyError` breaks callers that catch `KeyError` | M | L | Phase 2 greps for `except KeyError` around operator lookup before the change and updates any hit; `UnknownOperatorError` subclasses `ValidationError`/`SyntacticError`, not `KeyError`, so the grep is load-bearing. |
| Source-file encoding issues writing Unicode glyphs into `operators.py` | M | L | Python 3 source is UTF-8 by default; Phase 4 verifies by importing each modified module and asserting the alias string round-trips. |
| Docs left self-contradictory (three separate sections in `OPERATORS.md` assert the LaTeX-only rule) | L | M | Phase 5 treats all three sections (`### LaTeX Notation Requirements` ~L85, `## Best Practices` item 6 ~L415, `## Troubleshooting` item 3 ~L470) as one atomic edit. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 3 | -- |
| 2 | 2 | 1 |
| 3 | 4 | 1, 2 |
| 4 | 5, 6 | 4 (5); 1, 2, 3, 4 (6) |

Phases within the same wave can execute in parallel.

---

### Phase 1: Core alias attribute and registration [NOT STARTED]

**Goal**: One operator class can be looked up under its canonical `name` and under any number of
declared aliases, with canonical-name behavior byte-for-byte unchanged.

**Tasks**:
- [ ] Create `code/src/model_checker/syntactic/tests/unit/test_collection.py` (no such file
      exists today) and write failing tests FIRST (RED): an operator class with
      `name = "\\wedge"`, `arity = 2`, `aliases = ["∧"]` is retrievable from an
      `OperatorCollection` under both keys and returns the *same* class object; an operator with
      no `aliases` attribute at all still registers under `name` alone; a subclass declaring
      aliases does not cause a sibling subclass to inherit them.
- [ ] Add an end-to-end RED test parsing `"(p ∧ q)"` (infix, arity 2) and `"¬ p"` (prefix,
      arity 1) through `Syntax(...)` against a collection whose operators carry LaTeX canonical
      names plus Unicode aliases, asserting the resolved operator class matches the LaTeX-spelled
      equivalent.
- [ ] GREEN: add `aliases: List[str] = []` to `code/src/model_checker/syntactic/operators.py`'s
      `Operator` class attribute block, immediately after `primitive`, with a docstring entry in
      the class `Class Attributes:` list explaining it is the optional user-facing Unicode (or
      other) spellings that parse to this operator, and that it must never be mutated in place.
- [ ] GREEN: extend `OperatorCollection.add_operator`'s `isinstance(operator, type)` branch in
      `code/src/model_checker/syntactic/collection.py` to register each string in
      `getattr(operator, "aliases", []) or []` after the canonical `name` registration, reading
      the list without mutating it.
- [ ] Update `add_operator`'s docstring (the `For each operator added, its name is used as the
      key...` paragraph and the `Examples:` block) to document alias registration.
- [ ] REFACTOR: confirm `__iter__`, `items()`, and `__getitem__` behave sensibly when the same
      class appears under multiple keys; document in the `OperatorCollection` class docstring's
      `Attributes:` entry that `operator_dictionary` may map several keys to one class.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: full

**Scope Hypothesis**: This phase asserts it modifies exactly two source files
(`syntactic/operators.py`, `syntactic/collection.py`) and creates exactly one new test file.
Confirm at implementation time by re-running the research report's claim that
`add_operator` is the sole writer of `operator_dictionary`:
`grep -rn "operator_dictionary" code/src/model_checker --include='*.py'`. If any other writer
exists, stop and widen the phase before proceeding.

**Files to modify**:
- `code/src/model_checker/syntactic/operators.py` - add `aliases` class attribute + docstring entry
- `code/src/model_checker/syntactic/collection.py` - register aliases in `add_operator`; docstring updates
- `code/src/model_checker/syntactic/tests/unit/test_collection.py` - NEW; alias registration tests

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/syntactic/tests/unit/ -v` passes, including
  the new alias tests that were RED before the change.
- `PYTHONPATH=code/src pytest code/tests/ -q` shows no new failures.
- A collection built with no `aliases` anywhere produces an `operator_dictionary` identical to
  the pre-change one (assert by comparing key sets for one shipped theory).

---

### Phase 2: Collision and unknown-operator error handling [NOT STARTED]

**Goal**: An alias that collides with another operator's name/alias fails loudly at theory-load
time, and a mistyped or unregistered operator in a formula produces `UnknownOperatorError` with
an `available_operators` suggestion list instead of a bare `KeyError` — without breaking
idempotent re-registration.

**Tasks**:
- [ ] RED: add tests to `test_collection.py` for (a) two *different* classes claiming the same
      alias raises `DuplicateOperatorError`; (b) an alias colliding with another operator's
      canonical `name` raises `DuplicateOperatorError`; (c) re-adding the *same* class (directly,
      via `add_operator(other_collection)` merge, and via a `serialize_operators` /
      `deserialize_operators` round-trip on an aliased collection) is a silent no-op and raises
      nothing.
- [ ] RED: add a test that `collection["\\nosuchop"]` raises `UnknownOperatorError` whose context
      carries the available-operator list, and that `apply_operator` on a prefix list with an
      unregistered head surfaces the same error.
- [ ] Before changing the lookup path, run
      `grep -rn "except KeyError" code/src/model_checker --include='*.py'` and inspect every hit
      that could wrap an operator lookup; update any that relied on `KeyError` from
      `OperatorCollection.__getitem__`.
- [ ] GREEN: implement the conflict-aware duplicate policy in `add_operator` per Decision 1 —
      for both the canonical-name and alias registration paths, `return` silently when the
      existing entry `is` the same class, raise `DuplicateOperatorError(key, existing.__name__)`
      when it is a different class.
- [ ] GREEN: implement `OperatorCollection.__getitem__` to raise
      `UnknownOperatorError(value, available_operators=sorted(self.operator_dictionary))` on a
      missing key.
- [ ] Move the existing `if operator.name in self.operator_dictionary.keys(): return` guard so it
      runs *after* the `getattr(operator, "name", None) is None` check — the current ordering
      dereferences `operator.name` before validating it exists.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: full

**Scope Hypothesis**: Asserts that `builder/serialize.py::deserialize_operators` and
`add_operator`'s own `OperatorCollection`/iterable branches are the only paths that re-register
the same class. Confirm at implementation time with
`grep -rn "add_operator" code/src/model_checker --include='*.py'` (the research report found 6
non-test call sites: `imposition/operators.py:244`, `logos/operators.py:69`,
`exclusion/operators.py:387` and `bimodal/operators.py:630` via the constructor,
`syntactic/collection.py:72,75` recursion, `builder/serialize.py:73`) and re-check each for
idempotent re-add before relying on the count.

**Files to modify**:
- `code/src/model_checker/syntactic/collection.py` - duplicate policy, `__getitem__` error
- `code/src/model_checker/syntactic/tests/unit/test_collection.py` - collision + unknown tests
- Any file surfaced by the `except KeyError` grep - update the caught exception type

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/syntactic/tests/unit/ -v` passes.
- `PYTHONPATH=code/src pytest code/tests/ -q` passes with no new failures — in particular the
  builder/serialization tests, which exercise `deserialize_operators`.
- Each shipped theory still loads: `cd code && ./dev_cli.py` on one example file per theory
  (logos, exclusion, imposition, bimodal) produces the same output as before the change.

---

### Phase 3: Deliberate `is_syntactically_wff` structural tightening [NOT STARTED]

**Goal**: `is_syntactically_wff` classifies a non-backslash operator head as a connective because
of its structure, not by falling through the "atomic sentence letter" branch — with zero change
to which formulas are accepted or rejected in practice.

**Tasks**:
- [ ] RED/characterization: create
      `code/src/model_checker/syntactic/tests/unit/test_formulas.py` (no such file exists today)
      and pin the *current* accept/reject behavior for: `["p"]`, `["\\top"]`, `["\\bot"]`,
      `["\\neg", ["p"]]`, `["\\wedge", ["p"], ["q"]]`, `["∧", ["p"], ["q"]]`, `["¬", ["p"]]`, a
      Z3 `Const` head, `[]`, and a non-list input. These must all pass BEFORE the change.
- [ ] Add a RED test asserting the desired post-change discrimination: a bare non-backslash string
      head with arguments is accepted *as a connective*, and a multi-element prefix list is not
      reported as an atomic sentence letter.
- [ ] GREEN: in `code/src/model_checker/syntactic/formulas.py`, gate the
      `isinstance(head, str) and not head.startswith('\\')` branch on `len(prefix) == 1`, and add
      an explicit branch accepting a non-backslash string head when `len(prefix) > 1` (a
      Unicode/alias connective applied to arguments).
- [ ] Update the function docstring's grammar list to name the alias/Unicode connective case
      explicitly, so the next reader does not rediscover the coincidence.
- [ ] REFACTOR: confirm the final `return False, f"Unrecognized formula structure..."` is still
      reachable and still the right terminus for genuinely malformed input.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: full

**Scope Hypothesis**: Asserts `is_syntactically_wff` has exactly one production call site
(`syntactic/sentence.py:118` via `_validate_well_formedness`) plus the `syntactic/__init__.py`
re-export. Confirm with
`grep -rn "is_syntactically_wff" code/src --include='*.py'` before changing behavior; if a
second production caller exists, extend the characterization tests to cover it first.

**Files to modify**:
- `code/src/model_checker/syntactic/formulas.py` - structural branch ordering + docstring
- `code/src/model_checker/syntactic/tests/unit/test_formulas.py` - NEW; characterization + new tests

**Verification**:
- Every characterization test written before the change still passes after it (no accept/reject
  set change).
- `PYTHONPATH=code/src pytest code/src/model_checker/syntactic/tests/unit/ -v` passes.
- `PYTHONPATH=code/src pytest code/tests/ -q` passes with no new failures.

---

### Phase 4: Adopt Unicode aliases in shipped theory operators.py files [NOT STARTED]

**Goal**: Each shipped theory's `operators.py` declares Unicode aliases for its arity-1/arity-2
operators that have a standard glyph, demonstrating the mechanism and giving users the feature
out of the box, with every existing LaTeX formula still working.

**Tasks**:
- [ ] Enumerate the target operators and choose the glyph set. Starting proposal drawn from the
      research report's inventory (canonical name -> alias), applied per theory only where that
      theory defines the operator:
      `\neg`->`¬`, `\wedge`->`∧`, `\vee`->`∨`, `\rightarrow`->`→`, `\leftrightarrow`->`↔`,
      `\Box`->`□`, `\Diamond`->`◇`, `\boxright`->`□→`, `\diamondright`->`◇→`,
      `\equiv`->`≡`, `\leq`->`≤`, `\sqsubseteq`->`⊑`, `\preceq`->`⪯`, `\Rightarrow`->`⇒`,
      `\Future`->`⏵`, `\Past`->`⏴`, `\Until`->`U`-class glyph, `\Since`->`S`-class glyph.
      Reject any candidate that is alphanumeric (`str.isalnum()` is true) — those would be
      tokenized as sentence letters, not operators. Record the rejection in a comment.
- [ ] Verify the chosen set has no intra-theory and no intra-subtheory-combination collisions
      before editing, by building each shipped collection and diffing the alias keys.
- [ ] RED: add per-theory tests asserting a Unicode-spelled formula and its LaTeX equivalent
      resolve to the same operator class, in each theory's existing
      `tests/unit/` directory.
- [ ] GREEN: add `aliases = [...]` to the arity-1/arity-2 operator classes in:
      `theory_lib/logos/subtheories/extensional/operators.py`,
      `theory_lib/logos/subtheories/modal/operators.py`,
      `theory_lib/logos/subtheories/constitutive/operators.py`,
      `theory_lib/logos/subtheories/counterfactual/operators.py`,
      `theory_lib/exclusion/operators.py`,
      `theory_lib/imposition/operators.py`,
      `theory_lib/bimodal/operators.py`.
      Leave `\top`/`\bot` untouched (non-goal) and leave `\boxrightlogos`/`\diamondrightlogos`
      alias-free with a one-line comment saying no standard glyph exists.
- [ ] Sanity-check that each modified module imports cleanly and the alias strings round-trip
      (source encoding check).

**Timing**: 1.5 hours

**Depends on**: 1, 2

**Verification Tier**: full

**Scope Hypothesis**: Asserts 7 theory `operators.py` files and ~39 arity-1/arity-2 operator
classes (bimodal 15, exclusion 4, imposition 4, logos constitutive 5, counterfactual 2,
extensional 5, modal 4). This count came from a grep of `name = `/`arity = ` pairs and is a
hypothesis. Confirm at implementation time with
`grep -rn 'arity = [12]$' code/src/model_checker/theory_lib --include='operators.py' | wc -l`
and reconcile any discrepancy before claiming the phase covers the full set.

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/extensional/operators.py` - aliases on arity-1/2 classes
- `code/src/model_checker/theory_lib/logos/subtheories/modal/operators.py` - aliases
- `code/src/model_checker/theory_lib/logos/subtheories/constitutive/operators.py` - aliases
- `code/src/model_checker/theory_lib/logos/subtheories/counterfactual/operators.py` - aliases
- `code/src/model_checker/theory_lib/exclusion/operators.py` - aliases
- `code/src/model_checker/theory_lib/imposition/operators.py` - aliases
- `code/src/model_checker/theory_lib/bimodal/operators.py` - aliases
- Each theory's `tests/unit/` - Unicode/LaTeX equivalence tests

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/ -q` passes.
- Every theory's collection loads without raising `DuplicateOperatorError`.
- `cd code && ./dev_cli.py` on one example file per theory produces identical output to before.
- A hand-written example file using Unicode spellings produces the same model as its LaTeX twin.

---

### Phase 5: Documentation update [NOT STARTED]

**Goal**: `docs/usage/OPERATORS.md` documents the `aliases` convention and no longer asserts the
now-false "never use Unicode" rule anywhere.

**Tasks**:
- [ ] Rewrite the `### LaTeX Notation Requirements` section (~L85) as a LaTeX-canonical-name
      requirement plus an optional-alias allowance, keeping the existing operator table and
      adding a Unicode-alias column.
- [ ] Add a new `### Unicode Aliases` subsection with a worked example
      (`name = "\\wedge"`, `arity = 2`, `aliases = ["∧"]`) showing both spellings parsing, and
      stating the two constraints: an alias must not be alphanumeric, and `\top`/`\bot` cannot be
      aliased.
- [ ] Update `## Best Practices` item 6 (~L415) — replace "Always use LaTeX notation - never use
      Unicode in code" with guidance that the canonical `name` stays LaTeX and Unicode goes in
      `aliases`.
- [ ] Update `## Troubleshooting` item 3 (~L470) — replace the "LaTeX parsing errors: ... not `∧`"
      item with alias-aware guidance, and add an entry for `DuplicateOperatorError` (alias
      collision) and `UnknownOperatorError` (mistyped alias).
- [ ] Grep the docs tree for other assertions of the LaTeX-only rule
      (`grep -rn -i "never use unicode\|not ∧\|LaTeX notation" docs/ code/docs/`) and fix any hit.
- [ ] Apply the whole `OPERATORS.md` change as ONE edit pass so the three sections cannot drift
      into mutual contradiction.

**Timing**: 1 hour

**Depends on**: 4

**Verification Tier**: prose

**Files to modify**:
- `docs/usage/OPERATORS.md` - three contradicting sections + new Unicode Aliases subsection
- Any doc surfaced by the LaTeX-only grep

**Verification**:
- Diff read-through confirms every changed hunk is prose/markdown, no code file touched.
- `grep -rn -i "never use unicode" docs/ code/docs/` returns nothing.
- The worked example in the new subsection matches the actual attribute name and shape landed in
  Phase 1 (checked by eye against `syntactic/operators.py`).

---

### Phase 6: Full regression and acceptance validation [NOT STARTED]

**Goal**: The complete gate set is green and the feature demonstrably works end to end through
the CLI, not only through unit tests.

**Tasks**:
- [ ] Run the full suite: `PYTHONPATH=code/src pytest code/tests/ -v` and
      `PYTHONPATH=code/src pytest code/src/model_checker/ -q`.
- [ ] Run each theory's unit and integration tests explicitly, per CLAUDE.md's testing commands.
- [ ] Acceptance check: write a scratch example file (outside the repo tree, in the scratchpad)
      whose premises/conclusions use Unicode aliases, run it with `cd code && ./dev_cli.py`, and
      confirm the model output matches the LaTeX-spelled equivalent example run.
- [ ] Acceptance check: confirm an alias collision is reported as `DuplicateOperatorError` with
      both class names, and a mistyped alias as `UnknownOperatorError` with suggestions.
- [ ] Confirm zero changes landed in `utils/parsing.py`, `syntactic/sentence.py`,
      `syntactic/syntax.py`, `jupyter/unicode.py`, or `builder/translation.py`
      (`git diff --stat` review against the non-goals list).
- [ ] Confirm no `examples.py` formula was changed from LaTeX to Unicode.

**Timing**: 1 hour

**Depends on**: 1, 2, 3, 4

**Verification Tier**: full

**Files to modify**:
- None (validation only; any defect found routes back to its owning phase)

**Verification**:
- Full test suite green with no new failures relative to the pre-task baseline.
- Both acceptance checks above produce the expected output.
- `git diff --stat` shows no file outside the phases' declared file lists.

---

## Testing & Validation

- [ ] New `test_collection.py` covers: alias registration, multi-alias, no-alias, alias
      non-inheritance across sibling subclasses, same-class idempotent re-add, different-class
      collision raising `DuplicateOperatorError`, unknown lookup raising `UnknownOperatorError`.
- [ ] New `test_formulas.py` characterization tests pass identically before and after the
      `is_syntactically_wff` change.
- [ ] Per-theory Unicode/LaTeX operator-class equivalence tests pass for logos (all four
      subtheories), exclusion, imposition, and bimodal.
- [ ] `builder` serialization tests pass on an aliased collection round-trip.
- [ ] `PYTHONPATH=code/src pytest code/tests/ -v` green.
- [ ] `cd code && ./dev_cli.py` runs cleanly for one example file per theory.
- [ ] End-to-end CLI acceptance: a Unicode-spelled example produces the same model as its
      LaTeX twin.

## Artifacts & Outputs

- `code/src/model_checker/syntactic/operators.py` - `Operator.aliases` class attribute
- `code/src/model_checker/syntactic/collection.py` - alias registration, conflict-aware duplicate
  policy, `UnknownOperatorError` on lookup
- `code/src/model_checker/syntactic/formulas.py` - structurally correct `is_syntactically_wff`
- `code/src/model_checker/syntactic/tests/unit/test_collection.py` - NEW
- `code/src/model_checker/syntactic/tests/unit/test_formulas.py` - NEW
- Seven theory `operators.py` files with `aliases` declarations, plus per-theory tests
- `docs/usage/OPERATORS.md` - Unicode Aliases subsection; three contradicting sections corrected
- `specs/220_unicode_operator_characters/summaries/01_*-summary.md` - implementation summary

## Rollback/Contingency

Each phase commits independently per the Commit-Per-Green-Substep Mandate, so rollback is a
per-phase `git revert` of that phase's commit — no whole-tree reset is anticipated.

If a genuine whole-tree rollback becomes necessary (e.g. Phase 3's tightening proves to change
formula acceptance in a way the characterization tests missed), take a snapshot first per
`context/contracts/recovery.md`'s rollback rung, using its documented invocation shape including
the out-of-scope override flag, and only then run the destructive command. Do not emit a bare
default-mode snapshot call as a routine checkpoint.

Contingency by phase:
- **Phase 1/2 fail**: the feature is not shipped; revert both and the task is a no-op. Nothing
  else depends on them.
- **Phase 3 fails**: revert Phase 3 alone. It is independent of the alias mechanism (Wave 1,
  `Depends on: none`), so Phases 1, 2, 4, 5 still stand and the plan ships without the
  `is_syntactically_wff` cleanup — record the deferral explicitly rather than silently dropping it.
- **Phase 4 fails on one theory**: revert only that theory's `operators.py` edit. The core
  mechanism (Phases 1-2) remains usable by users in their own generated project copies, which is
  the task's primary requirement.
- **Phase 5 fails**: docs-only; revert freely with no code impact.
