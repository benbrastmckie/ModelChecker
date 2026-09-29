# Research Report: Align Operator Unicode Aliases with Logos Manual

- **Task**: 221 - Align operator Unicode aliases in theory operators.py files with the symbols
  of the Logos manual
- **Started**: 2026-09-29T00:00:00Z
- **Completed**: 2026-09-29T00:00:00Z
- **Effort**: ~2 hours (codebase survey + manual/Lean cross-reference + font-coverage probing)
- **Dependencies**: None
- **Sources/Inputs**:
  - Codebase: `code/src/model_checker/theory_lib/{bimodal,exclusion,imposition,logos}/operators.py`
    and `code/src/model_checker/theory_lib/logos/subtheories/{constitutive,counterfactual,extensional,modal}/operators.py`
  - `code/src/model_checker/syntactic/{operators.py,collection.py}` (alias registration/lookup
    machinery, `isalnum()` tokenizer constraint)
  - `code/src/model_checker/theory_lib/tests/test_theory_conformance.py` (registry-driven
    per-theory test pattern to mirror)
  - `code/src/model_checker/theory_lib/bimodal/tests/unit/test_unicode_aliases.py` and
    `code/src/model_checker/theory_lib/logos/subtheories/constitutive/tests/test_unicode_aliases.py`
    (existing per-theory alias tests that this change must update, not just add to)
  - `code/src/model_checker/theory_lib/logos/subtheories/constitutive/RELEVANCE.md`
  - `docs/usage/OPERATORS.md` (existing Unicode Aliases section/table to extend)
  - `~/Projects/Logos/Theory/typst/notation/extended-notation.typ`,
    `~/Projects/Logos/Theory/typst/notation/logos-notation.typ`
  - `~/Projects/Logos/Theory/typst/manual/chapters/02-constitutive.typ`,
    `~/Projects/Logos/Theory/typst/manual/chapters/03-dynamics.typ`
  - `~/Projects/Logos/Theory/Logos/Foundations/{Constitutive,Dynamical}/Syntax.lean`
  - `fc-list` (font-coverage probing) and Python `unicodedata` (width/category checks)
- **Artifacts**: this report
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- The manual's tense operators (`H`, `G`, `P`, `F`) are letters and cannot be used as
  Unicode aliases (the tokenizer treats any `isalnum()` token as a sentence letter,
  `syntactic/collection.py:166`) — there is no available non-colliding, non-alphanumeric
  standard glyph for `\Past`/`\Future`/`\past`/`\future`. Recommendation: leave all four
  **unaliased** and **remove** the current `⏴`/`⏵` aliases on `\Past`/`\Future` (poor font
  coverage — 3 fonts / 1 monospace font in this environment — and no manual counterpart).
- `\Since` and `\Until` (bimodal) should gain aliases `◁` (U+25C1) and `▷` (U+25B7),
  matching the manual's `since = triangle.l` / `until = triangle.r` exactly. These glyphs
  have strong font coverage (47 installed fonts / 17 monospace families in this
  environment) and do not collide with anything already registered in `bimodal_operators`.
- `\preceq` (`RelevanceOperator`, constitutive) has no manual counterpart at all — it is a
  ModelChecker/Fine-style relevance relation documented only in `RELEVANCE.md`, with no
  entry in the Logos manual's Essence/Ground/Reduction table. Its current alias `⪯` also has
  thin font coverage (9 fonts / 1 monospace) **and** the manual independently uses `⪯` for
  an unrelated concept (`durleq`, duration ordering in `logos-notation.typ`). This is an
  explicit open decision for the plan phase (see Recommendations); the research does not
  force a single answer.
- Three manual symbol families (`stably` → `⊡`, would-/might-cause → `○→`/`⊙→`, store/recall
  → `↑`/`↓`) have **no corresponding operator implemented anywhere in the codebase today**.
  No alias can be assigned to an operator that does not exist; these are documented as a
  forward-looking reference table only, not an action item for this task.
- `\CFBox`/`\CFDiamond`/`\next`/`\prev` (bimodal/modal) and `\boxrightlogos`/`\diamondrightlogos`
  (imposition) are already correctly unaliased, each with an accurate in-code comment
  explaining why (collision with `\Box`/`\Diamond`, or collision with `\boxright`/`\diamondright`
  within the same theory's collection). No change needed; `\top`/`\bot` remain correctly
  out of scope (matched by string literal, not the alias mechanism).
- Two existing tests hard-code the operators this task must change and will need updating as
  part of implementation, not just extending: `bimodal/tests/unit/test_unicode_aliases.py`
  (`test_until_since_and_discrete_duals_have_no_alias` asserts `UntilOperator.aliases == []`
  and `SinceOperator.aliases == []`; the `\Future`/`\Past` rows in the parametrized
  `test_unicode_alias_matches_latex_name` list use the `⏵`/`⏴` glyphs this report recommends
  removing).

## Context & Scope

The task is to make every shipped theory's Unicode operator aliases match the Logos manual's
notation where a manual correspondent exists, using a single terminal-printable glyph per
operator, and to add a mechanical acceptance test enforcing the printability criterion across
every shipped `operators.py`. Scope is limited to `aliases` declarations (the alternate,
optional spelling registered alongside an operator's canonical LaTeX `name` — see
`docs/usage/OPERATORS.md`'s Unicode Aliases section); it does not touch operator semantics,
`name` values, or add new operators for manual concepts the codebase does not yet implement.

## Findings

### 1. Alias mechanism and hard constraints (`code/src/model_checker/syntactic/`)

- `Operator.aliases: List[str] = []` (`operators.py:58`) — optional list of additional
  user-facing spellings registered by `OperatorCollection.add_operator` alongside the
  canonical `name` (`collection.py:61-119`).
- **Hard constraint**: the parser's `apply_operator` treats any `isinstance(atom, str) and
  atom.isalnum()` token as a sentence-letter constant (`collection.py:166-167`), not an
  operator lookup. An alias containing only alphanumeric characters would silently never
  match a formula token — this is why the manual's letter-named tense operators (`H`, `G`,
  `P`, `F`) cannot be aliased directly under those letters.
- **Hard constraint**: `\top`/`\bot` are matched by hardcoded string literal at several
  syntactic-layer call sites, independent of `OperatorCollection` lookup — they cannot be
  aliased at all (documented already in `OPERATORS.md:143-145`).
- **Collision constraint**: registering an alias already owned by a *different* class in the
  same `OperatorCollection` raises `DuplicateOperatorError` at theory-load time
  (`collection.py:73`, confirmed live in `imposition/operators.py:198-201`, where
  `LogosCounterfactual.aliases` is explicitly cleared to `[]` to avoid colliding with
  `ImpositionOperator`'s `"□→"` inside the same theory).
- Because `OperatorCollection.add_operator` is per-theory, cross-theory alias reuse (e.g.
  `bimodal`'s `◁`/`▷` vs. any other theory) cannot collide — each theory builds its own
  independent collection.

### 2. Current alias inventory across every shipped `operators.py`

| Theory / subtheory | Operator (`name`) | Current `aliases` | Manual symbol | Status |
|---|---|---|---|---|
| bimodal | `\neg` | `["¬"]` | `not` | matches |
| bimodal | `\wedge` | `["∧"]` | `and` | matches |
| bimodal | `\vee` | `["∨"]` | `or` | matches |
| bimodal | `\Box` | `["□"]` | `nec` (`□`) | matches |
| bimodal | `\Future` | `["⏵"]` | `allfuture` = `G` (letter) | **replace: remove alias** |
| bimodal | `\Past` | `["⏴"]` | `allpast` = `H` (letter) | **replace: remove alias** |
| bimodal | `\Until` | `[]` | `until` = `triangle.r` (`▷`) | **add alias `▷`** |
| bimodal | `\Since` | `[]` | `since` = `triangle.l` (`◁`) | **add alias `◁`** |
| bimodal | `\rightarrow` | `["→"]` | material conditional (`to`) | matches |
| bimodal | `\leftrightarrow` | `["↔"]` | `liff` | matches |
| bimodal | `\top` | none (unaliasable) | `top` (`⊤`) | out of scope |
| bimodal | `\Diamond` (defined) | `["◇"]` | `poss` (`◇`) | matches |
| bimodal | `\future` | none | `somefuture` = `F` (letter) | no change (see §3) |
| bimodal | `\past` | none | `somepast` = `P` (letter) | no change (see §3) |
| bimodal | `\next` | none | no manual counterpart | no change (correct) |
| bimodal | `\prev` | none | no manual counterpart | no change (correct) |
| exclusion | `\neg`/`\wedge`/`\vee`/`\equiv` | `¬`/`∧`/`∨`/`≡` | same as above | matches |
| imposition | `\boxright` | `["□→"]` | `boxright` | matches |
| imposition | `\diamondright` | `["◇→"]` | `diamondright` | matches |
| imposition | `\boxrightlogos` | `[]` (explicitly cleared) | no distinct manual symbol | no change (correct, documented) |
| imposition | `\diamondrightlogos` | none | no distinct manual symbol | no change (correct, documented) |
| logos/extensional | `\neg`/`\wedge`/`\vee`/`\rightarrow`/`\leftrightarrow` | matching | same as above | matches |
| logos/modal | `\Box`/`\Diamond` | `□`/`◇` | `nec`/`poss` | matches |
| logos/modal | `\CFBox`/`\CFDiamond` | none | no distinct manual symbol (would collide with `\Box`/`\Diamond`) | no change (correct, documented) |
| logos/counterfactual | `\boxright`/`\diamondright` | `□→`/`◇→` | `boxright`/`diamondright` | matches |
| logos/constitutive | `\equiv` | `["≡"]` | identity | matches |
| logos/constitutive | `\leq` (Ground) | `["≤"]` | `ground` (`≤`) | matches |
| logos/constitutive | `\sqsubseteq` (Essence) | `["⊑"]` | `essence` (`⊑`) | matches |
| logos/constitutive | `\Rightarrow` (Reduction) | `["⇒"]` | `reduction` (`⇒`) | matches |
| logos/constitutive | `\preceq` (Relevance) | `["⪯"]` | **no manual counterpart** | open decision, see §4 |

### 3. The tense-letter problem (`\Past`/`\Future`/`\past`/`\future`)

`extended-notation.typ` defines:
```
allpast = H     // Always past
allfuture = G   // Always future
somepast = P    // Sometimes past
somefuture = F  // Sometimes future
```
Cross-referenced against `03-dynamics.typ` (lines 84-89) and the bimodal operator docstrings,
the correspondence to the codebase is exact:

| ModelChecker operator | Semantics (docstring) | Manual symbol |
|---|---|---|
| `FutureOperator` (`\Future`) | "Truth at all future times" | `G` (`allfuture`) |
| `PastOperator` (`\Past`) | "Truth at all past times" | `H` (`allpast`) |
| `DefFutureOperator` (`\future`) | "holds at some future time" | `F` (`somefuture`) |
| `DefPastOperator` (`\past`) | "held at some past time" | `P` (`somepast`) |

All four manual symbols are bare letters, so none can be used as an alias
(`isalnum()` constraint, §1). No standard non-alphanumeric glyph distinct from the
already-claimed `□`/`◇` (modal necessity/possibility) represents "always-in-one-direction" /
"sometime-in-one-direction" without collision — this is exactly the same reasoning the
codebase already applies, correctly, to `\CFBox`/`\CFDiamond` (`modal/operators.py:137,191`:
"no distinct standard glyph from `\Box`/`\Diamond`; aliasing would collide with it").

The manual *does* define two further tense symbols, `always-op` = `triangle.t` (`△`) and
`sometimes-op` = `triangle.b` (`▽`) — but per `03-dynamics.typ:88-89` these are **derived,
bidirectional** operators, `△φ := Hφ ∧ φ ∧ Gφ` ("Always") and `▽φ := Pφ ∨ φ ∨ Fφ`
("Sometimes"), combining past, present, and future. They are semantically distinct from
`\Future`/`\Past`/`\future`/`\past` (each of which is one-directional) and **no ModelChecker
operator currently implements this combined always/sometimes semantics** — so `△`/`▽` are
not available as substitute aliases for the existing four operators; assigning them would
misrepresent the operators' semantics. They belong in the "no operator yet" reference table
(§5) instead.

**Recommendation**: leave `\Past`, `\Future`, `\past`, `\future` unaliased (matching the
existing, already-correct treatment of `\next`/`\prev`/`\CFBox`/`\CFDiamond`), and remove the
current `\Future`/`\Past` aliases `⏵`/`⏴` (see §4 for the font-coverage evidence). This
resolves dispatch problems (1) and (2) together: no alphanumeric alias is ever attempted, and
the poor-coverage glyphs are retired rather than replaced with an equally poor substitute.

### 4. Font-coverage / printability evidence

Measured in this environment via `fc-list ":charset=<hex>"` (all fonts) and
`fc-list ":charset=<hex>:spacing=100"` (monospace only), plus `unicodedata.east_asian_width`
for terminal-width safety (`W`/`F` = definitely double-width and must be rejected; existing
matched aliases such as `∧`, `□`, `⊑`, `⇒` are all `A` (Ambiguous) or `N`/`Na` (Narrow), never
`W`/`F` — this is the baseline the new glyphs are held to):

| Glyph | Codepoint | All fonts | Monospace fonts | `east_asian_width` | `isalnum()` |
|---|---|---|---|---|---|
| `◁` (since) | U+25C1 | 47 | 17 | A | False |
| `▷` (until) | U+25B7 | 47 | 17 | A | False |
| `△` (always-op, no operator yet) | U+25B3 | 47 | 17 | A | False |
| `▽` (sometimes-op, no operator yet) | U+25BD | 47 | 17 | A | False |
| `⊡` (stably, no operator yet) | U+22A1 | 28 | 17 | N | False |
| `○` (would-cause, no operator yet) | U+25CB | 51 | 19 | A | False |
| `⊙` (might-cause, no operator yet) | U+2299 | 46 | 17 | A | False |
| `↑` (store, no operator yet) | U+2191 | 59 | 19 | A | False |
| `↓` (recall, no operator yet) | U+2193 | 59 | 19 | A | False |
| `⏴` (current `\Past` alias) | U+23F4 | 3 | 1 | N | False |
| `⏵` (current `\Future` alias) | U+23F5 | 3 | 1 | N | False |
| `⪯` (current `\preceq` alias) | U+2AAF | 9 | 1 | N | False |

The 17-monospace-family figure for `◁`/`▷` (and the other well-covered glyphs) reflects
`DejaVu Sans Mono`, `FreeMono`, `Adwaita Mono`, `Liberation Mono` (for some), and the full
`JetBrains Mono`/`JetBrains Mono NL` weight family — i.e. every commonly pre-installed Linux
monospace family in this environment recognizes them. `⏴`/`⏵`/`⪯` are covered by exactly one
(`Adwaita Mono`), confirming the dispatch's own preliminary survey (3 fonts / 1 monospace for
the media-triangle glyphs, ~9 fonts / 1 monospace for `⪯`).

### 5. Manual symbols with no corresponding operator ("no operator yet")

These appear in `extended-notation.typ` / the manual chapters but have **no implementing
operator class anywhere in `theory_lib`** today. No alias can be assigned to a nonexistent
operator; recorded here only as a forward-looking reference table for a future task that
implements these operators (out of scope for this task):

| Manual concept | Typst macro | Symbol | Candidate alias | Codepoint |
|---|---|---|---|---|
| Stability | `stably` | dot-in-square | `⊡` | U+22A1 |
| Would-cause | `circleright` | circle + arrow | `○→` | U+25CB U+2192 |
| Might-cause | `dotcircleright` | dotted circle + arrow | `⊙→` | U+2299 U+2192 |
| Store | `store(n)` | `↑^n` | `↑` | U+2191 |
| Recall | `recall(n)` | `↓^n` | `↓` | U+2193 |
| Always (bidirectional) | `always-op` | `triangle.t` | `△` | U+25B3 |
| Sometimes (bidirectional) | `sometimes-op` | `triangle.b` | `▽` | U+25BD |

`would-cause`/`might-cause` correspond to the Lean `DynamicalFormula.causal`/`causalDefault`
constructors (`Logos/Foundations/Dynamical/Syntax.lean:331-338`, notation `o->`); no
`might-cause` (dotted-circle) constructor exists yet even in Lean, only in the Typst
notation macro — one further data point that this pair is aspirational/manual-only right now.

### 6. `\preceq` (Relevance) — no manual counterpart

`RelevanceOperator` (`logos/subtheories/constitutive/operators.py:379-389`) implements a
relevance relation ("A ⪯ B: A's content is relevant to B's content") documented at length in
`RELEVANCE.md`, which cites no Logos-manual source — it is presented purely as an internal
ModelChecker/Fine-style construct, weaker than Ground/Essence/Identity. Searching
`02-constitutive.typ`'s "Essence and Ground" section (`essence`, `ground`, `reduction`) finds
no fourth "relevance" ordering defined anywhere in the manual's constitutive chapter table.

Independently, `logos-notation.typ:97` defines `durleq = prec.eq` (`⪯`) for **duration**
ordering (`Dur`, a Discretion of the *Dynamical* Foundation's temporal structure) — an
unrelated concept from a different section of the manual. Reusing `⪯` for the *propositional*
relevance relation therefore both (a) has thin font coverage (§4) and (b) is not actually a
"manual-aligned" choice, since the manual's own use of `⪯` denotes something else entirely.

This is flagged as an open decision for the plan phase rather than resolved here (see
Recommendations) — there is no manual symbol to align to, so the choice is between keeping
`⪯` for its relevance-logic literature precedent (accepting weak font coverage) and removing
it (accepting `\preceq`-only spelling, consistent with the `\next`/`\prev`/`\CFBox` precedent).

### 7. Existing test coupling this change must account for

- `bimodal/tests/unit/test_unicode_aliases.py::test_until_since_and_discrete_duals_have_no_alias`
  currently asserts `UntilOperator.aliases == []` and `SinceOperator.aliases == []` by name
  (alongside `DefFutureOperator`, `DefPastOperator`, `DefNextOperator`, `DefPrevOperator`,
  which remain correctly alias-free). Adding `◁`/`▷` aliases requires removing `UntilOperator`/
  `SinceOperator` from this assertion list (not deleting the test — the remaining four
  operators' alias-free status is still correct and still worth enforcing).
- `bimodal/tests/unit/test_unicode_aliases.py::test_unicode_alias_matches_latex_name`'s
  parametrize list hard-codes `("\\Future p", "⏵ p", FutureOperator)` and
  `("\\Past p", "⏴ p", PastOperator)`. Removing those aliases makes these two rows fail
  (the Unicode-spelled formula would raise `UnknownOperatorError` once the alias is gone) —
  they must be deleted from the parametrize list as part of the same change, not left as
  regressions for a later task to discover.
- `logos/subtheories/constitutive/tests/test_unicode_aliases.py` already parametrizes
  `\preceq`/`⪯` — whatever the plan phase decides in §6, this row needs to move in lockstep
  with the operator's `aliases` declaration.
- No other `grep`-discoverable test currently references `⏴`, `⏵`, or `⪯` outside
  `__pycache__` artifacts (only source hits are the two files above plus `operators.py`
  itself, `bimodal/__init__.py`'s docstring/`__all__` comment, and doc files under
  `logos/docs/`, `logos/subtheories/README.md`, `docs/usage/WORKFLOW.md`, none of which are
  executable tests).

### 8. Existing registry pattern for the enforcement test

`theory_lib/tests/test_theory_conformance.py` establishes the pattern to reuse: parametrize
over `model_checker.registry.get_registered()` (the canonical, single source of truth for
`AVAILABLE_THEORIES`), call each theory module's `get_theory()`, and inspect the returned
`operators` value — an `OperatorCollection` instance (`operator_dictionary: Dict[str, Type[Operator]]`,
one entry per registered `name`/alias key, several keys may map to the same class —
`collection.py:23-30`). For the logos theory, subtheory-level iteration additionally goes
through `LogosOperatorRegistry`/`AVAILABLE_SUBTHEORIES` (see the constitutive
`test_unicode_aliases.py` fixture for the exact registry-loading idiom:
`LogosOperatorRegistry().load_subtheories([...])`.

A new cross-theory test should: (a) iterate every registered theory (and, for logos, every
subtheory) exactly as `test_theory_conformance.py` does; (b) deduplicate operator classes per
collection (since `.items()` yields one row per key, not per class); (c) for every declared
`aliases` entry, assert `not any(ch.isalnum() for ch in alias)`, assert every character's
`unicodedata.east_asian_width(ch) not in ("W", "F")`, and assert the alias is a member of a
curated, explicitly-vetted glyph registry (see Recommendations) rather than re-invoking
`fc-list` at test time (font availability is a property of the *development/CI* machine, not
something the test suite should depend on at every run — `fc-list` is the right tool for
*vetting* a candidate glyph once, offline, not for gating test correctness on a given CI
runner's installed font set). Collision detection (criterion 4 in the dispatch) is already
exercised for free: `get_theory()`/`load_subtheories()` build the `OperatorCollection` and
would raise `DuplicateOperatorError` at that point if two operators in the same theory
declared a colliding alias.

## Decisions

- Treat the tense-letter problem (§3) as resolved by policy: no alphanumeric alias is ever
  attempted, and `\Past`/`\Future`/`\past`/`\future` are aliased-free by design, matching the
  codebase's own existing precedent for `\CFBox`/`\CFDiamond`/`\next`/`\prev`.
- Treat manual concepts with no implementing operator (§5) as strictly out of scope for this
  task — no operator is added, only a reference table is recorded for a future task.
- Leave the `\preceq`/`⪯` question (§6) open for the plan phase rather than deciding it here,
  since there is no manual symbol to align to and the choice is a coverage/precedent
  trade-off, not a manual-fidelity question this research can settle unilaterally.

## Recommendations

1. **Add aliases** `◁` (U+25C1) to `SinceOperator` and `▷` (U+25B7) to `UntilOperator` in
   `code/src/model_checker/theory_lib/bimodal/operators.py`, matching `since`/`until` in
   `extended-notation.typ`. Update
   `bimodal/tests/unit/test_unicode_aliases.py` accordingly (§7).
2. **Remove** the `⏵`/`⏴` aliases from `FutureOperator`/`PastOperator` in the same file,
   replacing them with a `# No Unicode alias: ...` comment matching the style already used
   for `\Until`/`\Since`/`\future`/`\past`/`\next`/`\prev` (explain: manual symbol is the
   letter `G`/`H`, rejected by the `isalnum()` tokenizer constraint; no non-colliding
   standard glyph exists). Update the two affected rows in
   `test_unicode_alias_matches_latex_name`'s parametrize list (§7) — delete them rather than
   changing their glyph, since the recommendation is "no alias," not "different alias."
3. **Decide** the `\preceq`/`⪯` question explicitly in the plan (§6): either (a) keep `⪯`
   unchanged and document in `OPERATORS.md` that it has no manual counterpart and thin font
   coverage by design (an accepted trade-off for literature-mnemonic value), or (b) remove it
   for consistency with the "unaliased when no non-colliding standard glyph exists" policy
   applied everywhere else in this report. Either choice must be reflected consistently in
   `constitutive/tests/test_unicode_aliases.py` and `RELEVANCE.md`.
4. **Add a printability acceptance test** parametrized over `registry.get_registered()` (plus
   `AVAILABLE_SUBTHEORIES` for logos), per §8's design, backed by a small, explicitly-curated
   Python glyph registry (module-level constant, e.g. a new
   `code/src/model_checker/syntactic/alias_glyphs.py` or similar) rather than a live
   `fc-list` call — the registry's own construction should be documented as vetted via
   `fc-list`/`unicodedata` (the methodology and figures in §4 of this report), with the
   `fc-list` commands recorded as a comment so a maintainer can re-verify on a new
   environment. Every declared `aliases` entry across every shipped theory must satisfy:
   not `isalnum()`, `east_asian_width` never `W`/`F`, and membership in the curated registry.
5. **Update `docs/usage/OPERATORS.md`**: extend the existing "Unicode Alias" table
   (currently 8 rows, `OPERATORS.md:93-104`) into the complete manual-symbol → operator →
   Unicode table this task's dispatch requires, covering every row in §2's inventory
   (including the "no change, already correct" rows, so the table is a complete record, not
   just a diff), plus a clearly-labeled "no operator implemented yet" subsection for §5, and
   a short note on the printability acceptance criterion from Recommendation 4.

## Risks & Mitigations

- **Risk**: removing `⏴`/`⏵` is a user-facing breaking change for any external `.py` example
  file that already uses those glyphs. **Mitigation**: `\Future`/`\Past` (the canonical LaTeX
  spellings) continue to work unchanged; only the optional Unicode alias is removed. This
  matches the project's "No Backwards Compatibility" principle (CLAUDE.md) for a clean break
  rather than a deprecation shim.
- **Risk**: a curated glyph registry (Recommendation 4) can drift from actual font
  availability on a future machine. **Mitigation**: document the exact `fc-list` invocations
  used to vet each glyph (§4) as a comment alongside the registry, so re-verification is a
  copy-paste operation, not a re-derivation.

## Appendix

- `fc-list` invocations used for §4: `fc-list ":charset=<hex>" family` (all fonts) and
  `fc-list ":charset=<hex>:spacing=100" family` (monospace only), one call per candidate
  codepoint.
- Manual sources: `~/Projects/Logos/Theory/typst/notation/extended-notation.typ` (tense/
  causal/store-recall/stably macros), `~/Projects/Logos/Theory/typst/notation/logos-notation.typ`
  (`durleq`), `~/Projects/Logos/Theory/typst/manual/chapters/03-dynamics.typ:42-108` (tense
  operator table and `always-op`/`sometimes-op` derivations).
- Lean sources: `~/Projects/Logos/Theory/Logos/Foundations/Constitutive/Syntax.lean:363-387`
  (essence/ground/ident notation), `~/Projects/Logos/Theory/Logos/Foundations/Dynamical/Syntax.lean:464-530`
  (tense/since/until/causal notation, `Hd`/`Gd`/`Pd`/`Fd`/`<|d`/`|>d`/`o->`/`triangled`/`nablad`).
