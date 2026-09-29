# Implementation Plan: Task #221

- **Task**: 221 - Align operator Unicode aliases in theory operators.py files with the symbols of
  the Logos manual
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: None
- **Research Inputs**: specs/221_align_unicode_aliases_with_logos_manual/reports/01_align-unicode-aliases-logos-manual.md
- **Artifacts**: plans/01_align-unicode-aliases-logos-manual.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: python
- **Lean Intent**: false

## Overview

Bring every shipped theory's `aliases` declarations into correspondence with the Logos manual's
notation where a manual correspondent exists, retire the two alias glyphs with effectively no
monospace font coverage, and install a mechanical acceptance test that prevents a
poorly-printable or alphanumeric alias from re-entering any `operators.py`. The concrete diff is
small and fully enumerated by the research report (add `◁`/`▷` to `\Since`/`\Until`, remove
`⏵`/`⏴` from `\Future`/`\Past`, remove `⪯` from `\preceq`); the substantive new engineering is a
curated, offline-vetted glyph registry plus a cross-theory parametrized test, and a complete
manual-symbol table in `docs/usage/OPERATORS.md`. Done means: the printability test is green
across every registered theory and logos subtheory, the jupyter notation map no longer disagrees
with the declared aliases, and `OPERATORS.md` records the full mapping including the deliberately
unaliased operators and the manual concepts with no implementing operator yet.

### Research Integration

The research report settles the two hardest questions and this plan inherits both verbatim:

- **Tense letters** (`\Past`/`\Future`/`\past`/`\future`): the manual writes these as `H`/`G`/`P`/`F`,
  and `syntactic/collection.py`'s `apply_operator` treats any `isalnum()` token as a sentence
  letter, so no letter can ever be an alias. The manual's `△`/`▽` (`always-op`/`sometimes-op`) are
  *bidirectional derived* operators (`△φ := Hφ ∧ φ ∧ Gφ`) that no ModelChecker operator implements,
  so they are not substitutes. Policy: all four stay unaliased, matching the codebase's own
  existing, correct treatment of `\CFBox`/`\CFDiamond`/`\next`/`\prev`, and the current
  `⏵`/`⏴` aliases are removed rather than replaced.
- **Font coverage** (report §4, measured in this environment): `◁`/`▷` are carried by 47 fonts /
  17 monospace families, while `⏴`/`⏵` and `⪯` are carried by exactly 1 monospace family
  (`Adwaita Mono`). This is the evidence base for criterion 3 below and for retiring all three
  glyphs.
- **Test coupling** (report §7): two existing test files hard-code the operators this task
  changes and must be *edited*, not merely extended — `bimodal/tests/unit/test_unicode_aliases.py`
  and `logos/subtheories/constitutive/tests/test_unicode_aliases.py`.
- **Enforcement design** (report §8): reuse `theory_lib/tests/test_theory_conformance.py`'s
  registry-parametrized pattern, and back the printability check with a curated glyph registry
  vetted offline via `fc-list` rather than calling `fc-list` at test time.

One site the research report did not cover was found while grounding this plan and is added to
scope: `code/src/model_checker/jupyter/unicode.py` maintains a second, hand-written
bidirectional LaTeX↔Unicode map (four dict literals) that independently carries `⪯` and omits the
tense operators entirely. It is a drift-prone duplicate of exactly the data this task is fixing,
so Phase 4 syncs it and adds a drift guard.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md context was provided to this dispatch.

## Goals & Non-Goals

**Goals**:
- Add `◁` (U+25C1) to `SinceOperator` and `▷` (U+25B7) to `UntilOperator`, matching the manual's
  `since = triangle.l` / `until = triangle.r`.
- Remove `⏵` (U+23F5) from `FutureOperator` and `⏴` (U+23F4) from `PastOperator`, leaving both
  unaliased with an in-code comment explaining the `isalnum()` constraint and the coverage failure.
- Remove `⪯` (U+2AAF) from `RelevanceOperator` (see the Decision note below).
- Add a curated, offline-vetted glyph registry module and a cross-theory parametrized test
  enforcing the four-part printability acceptance criterion over every shipped `operators.py`.
- Sync `jupyter/unicode.py`'s notation maps with the declared aliases and add a drift-guard test.
- Rewrite `docs/usage/OPERATORS.md`'s alias documentation into a complete manual-symbol →
  operator → glyph → codepoint table, including deliberately-unaliased rows and a clearly-labeled
  "no implementing operator yet" reference subsection.

**Non-Goals**:
- Adding operators for manual concepts the codebase does not implement (`stably` `⊡`, would-cause
  `○→`, might-cause `⊙→`, store `↑`, recall `↓`, `always-op` `△`, `sometimes-op` `▽`). These are
  recorded as a forward-looking reference table only (report §5).
- Aliasing `\top`/`\bot`: they are matched by hardcoded string literal at several syntactic-layer
  call sites, independent of `OperatorCollection` lookup, and cannot be aliased at all.
- Changing any operator's canonical LaTeX `name`, arity, or semantics.
- Assigning aliases to `\next`, `\prev`, `\CFBox`, `\CFDiamond`, `\boxrightlogos`,
  `\diamondrightlogos`: each is already correctly unaliased with an accurate in-code reason
  (collision with `\Box`/`\Diamond` or with `\boxright`/`\diamondright` inside the same theory's
  collection). This plan confirms those comments read correctly and changes nothing else.
- Cleaning up `jupyter/unicode.py`'s four stale `exclusion_mappings` entries (`⦻`/`\exclude`,
  `⊓`/`\uniwedge`, `⊔`/`\univee`, `≔`/`\uniequiv`). No shipped operator carries any of those
  `name` values (exclusion declares only `\neg`, `\wedge`, `\vee`, `\equiv`), so they are dead
  aspirational data — out of scope here, and the Phase 4 drift guard is deliberately written to
  skip map entries with no corresponding shipped operator rather than fail on them.
- Any change to `specs/**` beyond this task's own artifacts.

### Decision: `\preceq` / `⪯` is retired (report §6, Recommendation 3)

The research left this open. This plan decides it: **remove the alias**, keeping `\preceq` as the
sole spelling. Three reasons, in order of weight:

1. This task authors the printability acceptance criterion, and `⪯` fails criterion 3 (1 monospace
   family). Keeping it would require grandfathering an exception into the very registry whose
   purpose is to make such exceptions impossible.
2. It is not actually a manual-aligned glyph: the manual has no relevance ordering in its
   Essence/Ground/Reduction table at all, and `logos-notation.typ:97` independently binds `⪯` to
   `durleq` (duration ordering, a Dynamical-Foundation concept). Reusing it would create a
   cross-document homograph.
3. It matches the policy applied everywhere else in this change: unaliased when no non-colliding,
   well-covered standard glyph exists (`\next`, `\prev`, `\CFBox`, `\CFDiamond`, and now the four
   tense operators).

This is reversible and costs nothing but doc churn if overridden, so it is surfaced as a
**non-blocking** `user_decision` on this dispatch's `.return-meta.json`; the plan proceeds on the
recommendation. Prose that merely *displays* `⪯` when naming the relevance relation stays (it is
display notation, like `⟹` for reduction in several READMEs); only text that presents `⪯` as
parseable input syntax is corrected (Phase 5).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A user's local `.py` example file already uses `⏴`/`⏵`/`⪯` and starts raising `UnknownOperatorError` | M | M | Canonical LaTeX spellings (`\Future`, `\Past`, `\preceq`) keep working unchanged; only the optional alias is withdrawn. Consistent with the project's No Backwards Compatibility principle — a clean break, no deprecation shim. Phase 5 records the retirement in `OPERATORS.md`. |
| The curated glyph registry drifts from real font availability on a future machine | M | M | Record the exact `fc-list` invocations and the measured per-glyph coverage figures as comments beside the registry, so re-verification is copy-paste (report §4 and Appendix). The test never calls `fc-list` — font availability is a property of the dev/CI box, not of correctness. |
| A theory or subtheory outside the research inventory declares an alias, so the printability test fails on something unanticipated | M | L | Phase 1's Scope Hypothesis makes this a checked gate: the RED run must name exactly `⏵`, `⏴`, `⪯` and nothing else. Any extra offender expands Phase 5's table and is recorded before proceeding. |
| Removing `FutureOperator.aliases` silently changes a subclass via attribute inheritance | M | L | `DefFutureOperator`/`DefPastOperator` are already asserted alias-free by the existing bimodal test, which Phase 2 keeps and extends; the Phase 1 registry test independently rejects any inherited out-of-registry glyph. |
| `◁`/`▷` collide with something already registered in `bimodal_operators` | H | L | `OperatorCollection.add_operator` raises `DuplicateOperatorError` at theory-load time, so a collision is a loud import failure, not a silent shadow; Phase 2's verification loads the collection explicitly. Cross-theory reuse cannot collide — each theory builds an independent collection. |
| `jupyter/unicode.py` has four dict literals (two module-level, two duplicated inside a lower function) and a partial edit leaves the map internally inconsistent | M | M | Phase 4 enumerates all four literals and the drift-guard test checks both directions, so an unedited literal fails the test rather than shipping. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4, 5 | 2, 3 |
| 4 | 6 | 1, 2, 3, 4, 5 |

Phases within the same wave can execute in parallel. Waves 2 and 3 are file-disjoint by design:
Phase 2 owns the bimodal Python files, Phase 3 owns the constitutive Python files, Phase 4 owns
the jupyter files, Phase 5 owns every `.md` file.

### Phase 1: Curated Glyph Registry and Printability Acceptance Test [NOT STARTED]

**Goal**: Establish the machine-checkable acceptance criterion first, as an intentional RED
baseline that names exactly the three glyphs later phases retire.

**Tasks**:
- [ ] Create `code/src/model_checker/syntactic/alias_glyphs.py` exporting
      `APPROVED_ALIAS_GLYPHS: frozenset[str]` containing exactly the 15 post-change alias strings:
      `¬ ∧ ∨ → ↔ □ ◇ □→ ◇→ ≡ ≤ ⊑ ⇒ ◁ ▷`.
- [ ] In that module's docstring, state the four-part printability acceptance criterion:
      (1) not `str.isalnum()`; (2) no character whose `unicodedata.east_asian_width` is `W` or `F`
      (double-width in a terminal); (3) present in the commonly pre-installed monospace families,
      vetted offline (never at test time) via `fc-list`; (4) no collision within a single theory's
      `OperatorCollection` — already enforced at load time by `DuplicateOperatorError`.
- [ ] Record per-glyph codepoint plus the measured all-fonts/monospace coverage figures as
      comments, and the two exact vetting invocations verbatim:
      `fc-list ":charset=<hex>" family` and `fc-list ":charset=<hex>:spacing=100" family`.
      Include a short "retired" comment block for `⏴` U+23F4, `⏵` U+23F5 and `⪯` U+2AAF recording
      that each is carried by exactly 1 monospace family, so a future author does not re-propose
      them.
- [ ] Export `APPROVED_ALIAS_GLYPHS` from `code/src/model_checker/syntactic/__init__.py` (import
      line plus `__all__` entry, following the existing per-module import style in that file).
- [ ] Create `code/src/model_checker/theory_lib/tests/test_alias_printability.py`, parametrized
      over `model_checker.registry.get_registered()` for whole theories and over
      `model_checker.theory_lib.logos.subtheories.AVAILABLE_SUBTHEORIES` for logos subtheories
      (using `LogosOperatorRegistry().load_subtheories([...])`, the idiom in
      `constitutive/tests/test_unicode_aliases.py`), mirroring
      `theory_lib/tests/test_theory_conformance.py`'s registry-parametrized structure.
- [ ] In that test: deduplicate operator classes per collection (`operator_dictionary` yields one
      key per `name`/alias, not per class), then for every entry of every class's `aliases` assert
      criterion 1, criterion 2, and membership in `APPROVED_ALIAS_GLYPHS`. Assertion messages must
      name the theory, the operator class, and the offending glyph with its codepoint.
- [ ] Run the new test and confirm the RED set is exactly the three expected offenders.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: the approved registry is exactly 15 glyph strings, and the RED run names
exactly three offending aliases — `⏵` on `\Future`, `⏴` on `\Past`, `⪯` on `\preceq`. Confirm at
implementation time by running the new test and diffing the reported offender set against that
list *before* starting Phase 2 or 3. If it names more, a theory or subtheory outside the research
inventory declares an alias: record it, and grow Phase 5's table accordingly. If it names fewer,
an expected alias declaration has already changed and the later phase must be re-scoped.

**Files to modify**:
- `code/src/model_checker/syntactic/alias_glyphs.py` - new: curated registry + criterion docstring
  + `fc-list` vetting record
- `code/src/model_checker/syntactic/__init__.py` - export `APPROVED_ALIAS_GLYPHS`
- `code/src/model_checker/theory_lib/tests/test_alias_printability.py` - new: cross-theory
  parametrized acceptance test

**Verification**:
- `PYTHONPATH=code/src python -c "from model_checker.syntactic import APPROVED_ALIAS_GLYPHS; print(len(APPROVED_ALIAS_GLYPHS))"` prints `15`
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/tests/test_alias_printability.py -v`
  fails, and the failure output names `⏵`, `⏴`, `⪯` and no other glyph (this is the expected RED
  baseline, recorded in the phase's commit message as intentional)
- `PYTHONPATH=code/src pytest code/src/model_checker/syntactic/tests -v` still passes (the new
  module adds no import cycle)

---

### Phase 2: Bimodal Alias Realignment [NOT STARTED]

**Goal**: Make `bimodal/operators.py` match the manual for `since`/`until` and retire the two
unprintable tense glyphs, keeping the existing bimodal alias tests truthful.

**Tasks**:
- [ ] `SinceOperator` (`bimodal/operators.py`, near line 434): replace the existing
      "No Unicode alias" comment with `aliases = ["◁"]  # U+25C1; manual: since = triangle.l`.
- [ ] `UntilOperator` (near line 402): replace its "No Unicode alias" comment with
      `aliases = ["▷"]  # U+25B7; manual: until = triangle.r`.
- [ ] `FutureOperator` (line 332): delete `aliases = ["⏵"]` and put in its place a
      `# No Unicode alias:` comment in the established style, giving both reasons — the manual
      symbol is the letter `G` (`allfuture`), rejected by the `isalnum()` tokenizer constraint; and
      `△` (`always-op`) is a distinct *bidirectional* derived operator, so it cannot stand in.
- [ ] `PastOperator` (line 362): same treatment for `⏴`, citing `H` (`allpast`) and `▽`
      (`sometimes-op`).
- [ ] `bimodal/tests/unit/test_unicode_aliases.py`: delete the two parametrize rows
      `("\\Future p", "⏵ p", FutureOperator)` and `("\\Past p", "⏴ p", PastOperator)`; add
      `("(p \\Since q)", "(p ◁ q)", SinceOperator)` and `("(p \\Until q)", "(p ▷ q)", UntilOperator)`
      with the matching imports (both are arity 2, so the rows are binary formulas).
- [ ] Same file: in `test_until_since_and_discrete_duals_have_no_alias`, remove `UntilOperator`
      and `SinceOperator` from the class tuple and add `FutureOperator` and `PastOperator`; rename
      the test to reflect its new membership and rewrite its docstring to state the new reasons
      (letter-valued manual symbols; no non-colliding standard glyph for the discrete duals).
- [ ] `bimodal/__init__.py`: update the module docstring's temporal-operator line (near line 15)
      and the `bimodal_operators` inline comment (near line 63) to drop `⏵`/`⏴` and name `◁`/`▷`.
- [ ] Confirm the theory still loads with no `DuplicateOperatorError`.

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: interface

**Scope Hypothesis**: exactly three bimodal Python files carry a `⏴`/`⏵` occurrence or a
Since/Until alias assertion — `operators.py`, `__init__.py`, `tests/unit/test_unicode_aliases.py`.
Confirm with `grep -rn $'⏴\|⏵' code/src/model_checker/theory_lib/bimodal --include=*.py | grep -v __pycache__`
before editing (expect hits only in those three) and again after (expect zero). `bimodal/docs/API_REFERENCE.md`
also carries the glyphs but is Phase 5's territory, not this phase's.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/operators.py` - add `◁`/`▷`, remove `⏵`/`⏴`, add
  reason comments
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_unicode_aliases.py` - swap the
  parametrize rows, re-partition the no-alias assertion list
- `code/src/model_checker/theory_lib/bimodal/__init__.py` - docstring and `__all__` comment

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/unit/ -v` passes
- `PYTHONPATH=code/src python -c "from model_checker import Syntax; from model_checker.theory_lib.bimodal.operators import bimodal_operators, SinceOperator, UntilOperator; assert Syntax(['(p ◁ q)'], [], bimodal_operators).premises[0].original_operator is SinceOperator; assert Syntax(['(p ▷ q)'], [], bimodal_operators).premises[0].original_operator is UntilOperator; print('ok')"`
- the same probe with `'⏵ p'` now raises (the alias is genuinely gone, not shadowed), while
  `'\\Future p'` still resolves to `FutureOperator`
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` (the whole
  bimodal suite, i.e. the enumerated direct dependents of the changed module) passes

---

### Phase 3: Relevance (`\preceq`) Alias Retirement [NOT STARTED]

**Goal**: Apply the `⪯` decision recorded above to the constitutive subtheory's Python sources.

**Tasks**:
- [ ] `logos/subtheories/constitutive/operators.py` (line 389): delete `aliases = ["⪯"]` from
      `RelevanceOperator` and put a `# No Unicode alias:` comment in its place recording all three
      reasons — no manual counterpart in the Essence/Ground/Reduction table; the manual's own `⪯`
      is `durleq` (duration ordering, `logos-notation.typ`), so reuse would be a cross-document
      homograph; and 1-monospace-family coverage fails criterion 3 of `alias_glyphs.py`.
- [ ] `logos/subtheories/constitutive/tests/test_unicode_aliases.py`: delete the
      `("(p \\preceq q)", "(p ⪯ q)", RelevanceOperator)` parametrize row.
- [ ] Same file: add a small explicit test asserting `RelevanceOperator.aliases == []` with the
      reason in its docstring, so the retirement is enforced rather than merely absent — mirroring
      the shape of bimodal's no-alias test.
- [ ] Confirm the other four constitutive rows (`≡`, `≤`, `⊑`, `⇒`) are untouched and still pass.

**Timing**: 0.75 hours

**Depends on**: 1

**Verification Tier**: interface

**Scope Hypothesis**: `⪯` appears as a *parseable-alias claim* in exactly three source files —
`constitutive/operators.py` and `constitutive/tests/test_unicode_aliases.py` (this phase) and
`jupyter/unicode.py` (Phase 4, four occurrences). Every other `⪯` occurrence in the repository is
display prose in a `.md` file and belongs to Phase 5. Confirm with
`grep -rn '⪯' code docs --include=*.py --include=*.md | grep -v __pycache__` before editing, and
classify each hit as alias-claim vs. display-prose in the phase's commit message.

**Files to modify**:
- `code/src/model_checker/theory_lib/logos/subtheories/constitutive/operators.py` - remove the
  `⪯` alias, add the reason comment
- `code/src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_unicode_aliases.py`
  - drop the `⪯` row, add the alias-free assertion

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/subtheories/constitutive/tests/ -v` passes
- `(p \preceq q)` still resolves to `RelevanceOperator` through a `LogosOperatorRegistry` loaded
  with `["extensional", "modal", "constitutive"]`; `(p ⪯ q)` now raises
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/logos/tests/ -v` passes (the
  logos theory still loads and its examples are unaffected)

---

### Phase 4: Jupyter Notation Map Sync and Drift Guard [NOT STARTED]

**Goal**: Stop `jupyter/unicode.py` from contradicting the declared aliases, and make a future
contradiction a test failure instead of a silent divergence.

**Tasks**:
- [ ] `jupyter/unicode.py`: remove the `⪯`/`\preceq` pair from all four dict literals — the
      module-level `unicode_to_latex` map (near line 64), the module-level `latex_to_unicode` map
      (near line 130), and the two duplicated inner maps (near lines 253 and 272).
- [ ] Same file: add `'◁': '\\Since'` / `'▷': '\\Until'` to both Unicode→LaTeX literals and
      `'\\Since': '◁'` / `'\\Until': '▷'` to both LaTeX→Unicode literals, with a comment noting the
      manual source (`triangle.l`/`triangle.r`).
- [ ] Add a drift-guard test (new `jupyter/tests/unit/test_unicode_alias_sync.py`, or a new class in
      the existing `jupyter/tests/unit/test_unicode.py`): for every `(unicode, latex)` pair in every
      map literal, look the `latex` string up against the `name` of every operator class shipped by
      any registered theory or logos subtheory; when a match exists, assert `unicode` is in that
      class's `aliases`. Entries whose `latex` matches no shipped operator are skipped with an
      explicit, commented rationale (the four dead `exclusion_mappings` entries — see Non-Goals).
- [ ] Add the reverse direction to the same test: for every shipped operator that declares
      aliases *and* whose `name` appears anywhere in the maps, assert the map's glyph for it equals
      its declared alias, so a future alias change that forgets this file fails here.

**Timing**: 0.75 hours

**Depends on**: 2, 3

**Verification Tier**: local

**Scope Hypothesis**: `jupyter/unicode.py` carries exactly four `⪯` occurrences and exactly four
dict literals needing the `◁`/`▷` additions (two module-level, two duplicated inside the lower
normalization function). Confirm with `grep -c '⪯' code/src/model_checker/jupyter/unicode.py`
(expect `4`, then `0` after) and by enumerating the `replacements = {` / map-literal openings in
the file before editing — a fifth literal would mean an unedited map, which the drift-guard test
is written to catch.

**Files to modify**:
- `code/src/model_checker/jupyter/unicode.py` - remove `⪯` pairs, add `◁`/`▷` pairs in all four
  literals
- `code/src/model_checker/jupyter/tests/unit/test_unicode_alias_sync.py` - new: bidirectional
  drift guard between the notation maps and the declared aliases

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/jupyter/tests/unit/ -v` passes (including the
  pre-existing `test_unicode.py` round-trip tests)
- the new drift-guard test fails if the `◁` entry is removed from any one of the four literals
  (confirm once by temporary local mutation, then revert — do not commit the mutation)

---

### Phase 5: Documentation — Complete Manual-Symbol Table [NOT STARTED]

**Goal**: Make `docs/usage/OPERATORS.md` the complete, authoritative manual-symbol → operator →
glyph → codepoint record, and correct every doc occurrence that presents a retired glyph as
parseable input syntax.

**Tasks**:
- [ ] `docs/usage/OPERATORS.md`, `## Unicode Aliases` section: add a complete table with columns
      Manual concept / Manual symbol (typst macro) / Theory · subtheory / Operator `name` / Unicode
      alias / Codepoint / Note, covering **every** row of the research inventory — the unchanged
      rows (`¬ ∧ ∨ → ↔ □ ◇ □→ ◇→ ≡ ≤ ⊑ ⇒`) as well as the changed ones — so the table is a
      complete record rather than a diff.
- [ ] Same section: add the deliberately-unaliased rows with their reasons: `\Past`, `\Future`,
      `\past`, `\future` (manual symbols are the letters `H`/`G`/`P`/`F`, rejected by the
      `isalnum()` tokenizer constraint), `\next`, `\prev`, `\CFBox`, `\CFDiamond`,
      `\boxrightlogos`, `\diamondrightlogos` (no distinct manual symbol; would collide inside the
      same theory's collection), `\preceq` (see the Decision note), and `\top`/`\bot` (unaliasable
      by construction).
- [ ] Same section: document the four-part printability acceptance criterion and point at
      `model_checker.syntactic.alias_glyphs.APPROVED_ALIAS_GLYPHS` as its machine-checked home,
      naming the enforcing test file.
- [ ] Same section: add a clearly-labeled "Manual symbols with no implementing operator yet"
      subsection listing `⊡` U+22A1 (`stably`), `○→` U+25CB U+2192 (would-cause), `⊙→` U+2299 U+2192
      (might-cause), `↑` U+2191 (`store`), `↓` U+2193 (`recall`), `△` U+25B3 (`always-op`),
      `▽` U+25BD (`sometimes-op`), stating explicitly that these are reserved candidates, not
      registered aliases.
- [ ] Update the "LaTeX Notation Requirements" table's Unicode Alias column if any listed row's
      alias changed (none of its 9 rows is affected by this change — confirm rather than assume).
- [ ] `code/src/model_checker/theory_lib/bimodal/docs/API_REFERENCE.md` (near lines 313-318): drop
      `⏵`/`⏴` from the `FutureOperator`/`PastOperator`/`DefFutureOperator`/`DefPastOperator` rows
      (leave the alias cell empty with a short dash/reason), and add `◁`/`▷` to the
      `SinceOperator`/`UntilOperator` rows.
- [ ] Correct the doc text that presents `⪯` as parseable input syntax rather than display
      notation: `constitutive/RELEVANCE.md` (the `**Symbol**: \preceq (displayed as ⪯)` line) and
      `constitutive/README.md`'s corresponding line — keep the displayed glyph, add that `⪯` is
      display-only and not a registered alias.
- [ ] Classify, then leave unchanged, the remaining display-prose `⪯` occurrences:
      `theory_lib/README.md`, `logos/docs/README.md`, `logos/subtheories/README.md`,
      `constitutive/CITATION.md`, `constitutive/notebooks/README.md`, `docs/usage/WORKFLOW.md`.
      Record the classification in the phase's commit message.

**Timing**: 1.25 hours

**Depends on**: 2, 3

**Verification Tier**: prose

**Scope Hypothesis**: ten `.md` files carry a `⏴`/`⏵`/`⪯` occurrence (the repo-wide grep in the
research, excluding `specs/**` and `.claude/**`). Only the *alias-claim* occurrences must change;
the count of files edited will therefore be smaller than ten. Confirm the live list at
implementation time with
`grep -rln $'⏴\|⏵\|⪯' code docs --include=*.md | grep -v __pycache__`, classify each occurrence
display-prose vs. alias-claim, and edit only the latter.

**Files to modify**:
- `docs/usage/OPERATORS.md` - complete manual-symbol table, acceptance criterion, no-operator-yet
  subsection
- `code/src/model_checker/theory_lib/bimodal/docs/API_REFERENCE.md` - operator table alias column
- `code/src/model_checker/theory_lib/logos/subtheories/constitutive/RELEVANCE.md` - `⪯` is
  display-only
- `code/src/model_checker/theory_lib/logos/subtheories/constitutive/README.md` - same

**Verification**:
- `grep -rn $'⏴\|⏵' code docs --include=*.md --include=*.py | grep -v __pycache__` returns nothing
- every changed hunk lies inside markdown prose or a markdown table (diff read-through, per the
  `prose` tier), with no Python file touched by this phase
- the `OPERATORS.md` table's operator rows cover every `name` that appears in any shipped
  `operators.py` (cross-check against the grep of `aliases`/`name` declarations)
- relative markdown links in the edited files still resolve (no renamed anchors)

---

### Phase 6: Full Gate and Regression Run [NOT STARTED]

**Goal**: Confirm the acceptance test is green, no theory regressed, and no straggler occurrence
of a retired glyph survives anywhere in the shipped tree.

**Tasks**:
- [ ] Run the printability acceptance test and confirm it is now green across every registered
      theory and logos subtheory (the RED baseline from Phase 1 flipped by Phases 2-3).
- [ ] Run the full project test suite and the per-theory unit suites.
- [ ] Smoke-run the dev CLI on a bimodal example to confirm real end-to-end parsing (not just
      unit-level `Syntax` construction).
- [ ] Final straggler grep for `⏴`, `⏵`, and alias-claim `⪯` across `code/` and `docs/`.
- [ ] Confirm every theory imports cleanly (no `DuplicateOperatorError` from any collection).

**Timing**: 0.5 hours

**Depends on**: 1, 2, 3, 4, 5

**Verification Tier**: full

**Files to modify**:
- none (verification-only phase; any fix it uncovers is attributed back to the owning phase)

**Verification**:
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/tests/test_alias_printability.py -v` passes
- `PYTHONPATH=code/src pytest code/tests/ -v` passes
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/ -v` passes
- `PYTHONPATH=code/src pytest code/src/model_checker/jupyter/tests/ -v` passes
- `cd code && ./dev_cli.py` on an existing bimodal example file completes without error
- `PYTHONPATH=code/src python -c "from model_checker import registry; [__import__('model_checker.theory_lib.'+t, fromlist=['get_theory']).get_theory() for t in registry.get_registered()]; print('all theories load')"`
- `grep -rn $'⏴\|⏵' code docs | grep -v __pycache__` returns nothing

## Testing & Validation

- [ ] New `test_alias_printability.py` is green over every registered theory and every logos
      subtheory, and its assertion messages name theory + class + glyph + codepoint on failure.
- [ ] Every alias declared anywhere satisfies: not `isalnum()`, no `east_asian_width` in `{W, F}`,
      member of `APPROVED_ALIAS_GLYPHS`.
- [ ] `bimodal` alias tests cover `◁`/`▷` positively and `\Future`/`\Past` as alias-free.
- [ ] `constitutive` alias tests cover `≡ ≤ ⊑ ⇒` positively and `\preceq` as alias-free.
- [ ] `jupyter` drift-guard test ties the notation maps to the declared aliases in both directions.
- [ ] No theory raises `DuplicateOperatorError` at load.
- [ ] Full suite (`code/tests/`) and per-theory unit suites pass.
- [ ] `dev_cli.py` smoke run on a bimodal example parses and solves.

## Artifacts & Outputs

- `code/src/model_checker/syntactic/alias_glyphs.py` (new) - curated glyph registry, the four-part
  criterion, and the recorded `fc-list` vetting methodology
- `code/src/model_checker/theory_lib/tests/test_alias_printability.py` (new) - cross-theory
  acceptance test
- `code/src/model_checker/jupyter/tests/unit/test_unicode_alias_sync.py` (new) - notation-map drift
  guard
- Modified: `syntactic/__init__.py`, `theory_lib/bimodal/{operators.py,__init__.py}`,
  `theory_lib/bimodal/tests/unit/test_unicode_aliases.py`,
  `theory_lib/logos/subtheories/constitutive/operators.py` and its
  `tests/test_unicode_aliases.py`, `jupyter/unicode.py`
- Documentation: `docs/usage/OPERATORS.md` (complete manual-symbol table + criterion +
  no-operator-yet reference), `theory_lib/bimodal/docs/API_REFERENCE.md`,
  `constitutive/{RELEVANCE.md,README.md}`
- `specs/221_align_unicode_aliases_with_logos_manual/summaries/01_*-summary.md` at implementation
  close

## Rollback/Contingency

Each phase is independently revertible and lands as its own commit (default `per-substep` commit
mode throughout — no phase here declares `atomic-batch`), so the ordinary contingency is
`git revert` of the offending phase commit; the canonical LaTeX `name` for every operator is
untouched by this change, so reverting any single phase leaves a working parser.

- **Before starting Phase 2 or 3** (the only phases that withdraw a currently-working user-facing
  spelling), take a durable, non-reverting checkpoint with
  `bash .claude/scripts/git-snapshot.sh 221 --no-revert`. This is a defensive checkpoint, not a
  rollback.
- **If a genuine rollback of uncommitted work is needed**, follow
  `.claude/context/contracts/recovery.md`'s rollback rung for the exact invocation shape,
  including its out-of-scope override flag for a deliberate whole-tree revert. Do not invoke
  `git-snapshot.sh` in its default reverting form as a routine checkpoint.
- **If Phase 1's RED run names more offenders than the three expected** (Scope Hypothesis
  failure): stop, record the extra offenders, and re-scope — either widen
  `APPROVED_ALIAS_GLYPHS` with fresh `fc-list` evidence for a legitimately well-covered glyph, or
  add a retirement phase for it. Do not silently add an unvetted glyph to the registry to make the
  test pass.
- **If `◁`/`▷` turn out to collide** inside `bimodal_operators` (a `DuplicateOperatorError` at
  load): revert Phase 2's alias additions only, keep the `⏵`/`⏴` removals (they stand on their own
  coverage evidence), and record the collision in the summary as a follow-up.
