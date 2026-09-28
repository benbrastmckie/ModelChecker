# Research Report: Certifying Countermodel Architecture

**Task**: 205 - certifying_countermodel_architecture
**Started**: 2026-09-28T01:17:35Z
**Completed**: 2026-09-28T01:30:00Z
**Effort**: ~3-5 days implementation across the three items (item 2's staging dominates)
**Dependencies**: 197 (certificate-wire hardening, completed) — consumed, not re-decided
**Sources/Inputs**:
- Codebase: `code/src/model_checker/theory_lib/bimodal/` (docs, `semantic/`, `tests/`)
- Companion repository: `~/Projects/BimodalLogic` (read-only inspection and direct binary invocation)
- Direct measurement: binary size/symbol inventory, live end-to-end gate timing, CI workflow grep
- No WebSearch/WebFetch used; no Mathlib lookup MCP calls (the open questions were all local and measurable)

**Artifacts**:
- `specs/205_certifying_countermodel_architecture/reports/01_certifying-countermodel-architecture.md`

**Standards**: report-format.md, subagent-return.md
**Task Type**: formal
**Domains**: logic (primary — the soundness/adequacy asymmetry and what a verdict establishes), math (secondary — the decidability argument underwriting the per-run check), plus a substantial engineering/packaging component in item 2 that is neither

---

## Executive Summary

1. **Item 1's central premise is stale, in the direction that helps.** The dispatch instructs that
   `check_certificate` is "verdict-producing today, not entailment-producing". It is no longer:
   the binary returns `"acceptance":"entailment"` **and** a bytewise-matching `"echo"` on a
   live-extracted certificate, measured this session. There is therefore no "interim gate over a
   weaker checker" question to answer — the gate can be built over the entailment-producing
   checker now, and the whole "is the weaker check worth shipping / would it misrepresent its own
   strength" branch of item 1 is moot.

2. **But two documents now overclaim that checker's strength, and a gate must not inherit the
   overclaim.** `ADEQUACY.md` §6.2 and `TRUST_PIPELINE.md`'s trust-base bullet call an
   `"acceptance":"entailment"` verdict "a kernel-checked proof for that particular certificate".
   The Lean module's own `Acceptance` docstring reserves exactly that third value and explicitly
   does not produce it; `CheckCertificateMain.lean` states "this is **not** per-certificate kernel
   checking". Reported as a finding, per COORDINATION — the wording sits in the wire task's
   territory.

3. **Item 2's cost is roughly 30x smaller than the binary size suggests, and the lever is one line
   upstream.** `check_certificate` is 299 MiB unstripped / 209 MiB stripped / ~66 MiB
   gzip-compressed — but 212,374 of its symbols are `l_Lean*` (38,581 of them `Lean.Elab`) and
   **zero** are Mathlib, FormalSystem or BimodalTools runtime code. The bulk is the Lean
   frontend/interpreter, linked by `supportInterpreter = true` in BimodalLogic's `lakefile.toml`.
   No packaging route should be costed before that flag is flipped and re-measured.

4. **Recommended route for item 2: the two-tier trust model now, an opt-in out-of-band verified
   binary next, in-wheel shipping only if the trimmed size justifies it.** Requiring the toolchain
   is declined on measured grounds (17 GB `~/.elan`, 9.2 GB `.lake/packages`). A Python
   re-implementation is declined but must be re-costed honestly: it **already exists** (`recheck`,
   ~190 lines of decision procedure) and is the live path's entire trust base today, so it adds
   nothing and removes nothing.

5. **A mandatory gate is cheap and works end to end today.** Measured on a live-extracted
   certificate: solve + Python re-check 0.0241s; direct binary invocation 0.0512s,
   `status=countermodel`, `acceptance=entailment`, echo matching bytewise. The ~2.2s figure
   recorded in the test suite is `lake exe`'s build check, not the checker — the binary alone runs
   in ~0.04-0.05s.

6. **Two blockers nothing else scopes.** (a) `tests/_lean_check.py` runs a 60-second `probe()` at
   import time and lives in the test tree; it cannot be the gate's resolver. (b)
   `BIMODAL_LOGIC_COMMIT` is declared, exported, and **never consumed anywhere** — and the local
   checkout has already drifted from it (HEAD `d1a24b30` vs. pin `d55e2760`). A gate over an
   unpinned external checker gates against an unknown contract.

7. **Item 3: all three already-applied `TRUST_PIPELINE.md` edits verified correct.** The extension
   work found three genuine inconsistencies elsewhere, the largest being that **`A2_GAP.md`'s
   section 8 limit 3 still records the per-candidate obligation as open** and still asserts "the
   leg (i)/(iii) comparison itself is aggregate, not per-candidate" — the exact staleness class the
   `TRUST_PIPELINE.md` repair fixed, left unfixed one document over.

---

## Context & Scope

This task owns three things: the output gate (item 1), the checker's runtime availability
(item 2), and the tier repositioning (item 3). Everything about the wire format, proof-carrying
acceptance and parse-echo verification belongs to the certificate-wire hardening task and is
consumed here. The harness reorganization and its performance work, the A1 compression bound, and
the divisor-period sweep driver are out of scope.

The governing asymmetry stated in the dispatch is not re-argued here — `TRUST_PIPELINE.md` already
states it carefully, and this report cites rather than re-derives it. What the asymmetry is used
for below is cost allocation: effort belongs where results are not independently checkable, and
that is what justifies both the mandatory per-run check (item 1) and the decision to keep the
expensive Tier 1 enumeration despite reclassifying what it establishes (item 3).

---

## Domain Analysis

**Logic (primary).** The load-bearing content is the soundness/adequacy asymmetry and the question
of what a `countermodel` verdict actually establishes — the difference between "four `Decidable`
instances returned true", "Lean constructed a term of `WitnessFamily.Refutes` by applying a
build-time kernel-checked implication to four run-time decisions", and "a kernel-checked proof for
this certificate". These are three distinct epistemic positions and the `Acceptance` inductive in
`BimodalTools/CertificateImport.lean` encodes exactly the first two while deliberately reserving
the third. Getting item 1's output label right *is* this distinction.

**Mathematics (secondary).** The decidability of (C1)-(C4) is what makes a per-run check possible
at all, and the window-collapse results (`coherent_iff_window`, `fulfil_iff_window`,
`mem_all_iff_window`, `scan_forward`/`scan_backward`) are what make the decision procedures
finite. This is cited, not re-derived: `ADEQUACY.md` §5.2 owns it.

**No physics content.** No dynamical-systems or ergodic material bears on this task. The lasso
structure is periodic-orbit-shaped, but the relevant results are order-theoretic and
model-theoretic, not dynamical.

**Substantial non-formal component.** Item 2 is a packaging and distribution question —
wheel size, platform tags, PyPI limits, CI cost. It is costed below on measurement, not on formal
grounds, and that is the right register for it.

---

## Findings

### Logic Findings — what a verdict establishes, and the two overclaims

**F1. The proof-carrying acceptance mode has landed and is live.** Measured directly this session
against `~/Projects/BimodalLogic/.lake/build/bin/check_certificate`:

```
status=countermodel  acceptance=entailment  echo_matches=True
```

on both a trivial probe certificate and a certificate extracted from a live
`BimodalStructure` search for `[] ⊢ [(p \Until q)]`. The dispatch's ALREADY SETTLED paragraph
("verdict-producing today, not entailment-producing ... the Lean development has its own task open
to change") describes a state that the wire-hardening task already moved past.

**Consequence for item 1**: the question "is an interim gate over today's verdict-producing
checker worth shipping before the proof-carrying mode lands, or would the weaker check
misrepresent its own strength" does not need answering. The gate can be specified directly over
the `entailment` acceptance level, with `decided` as the documented weaker fallback the Python
re-checker produces. This is the single most consequential finding for planning: it removes a
sequencing dependency the task description assumed.

**F2. Two documents overclaim the `entailment` level. A gate's label must not inherit it.** The
Lean side's own account, from `BimodalTools/CertificateImport.lean`'s `Acceptance` docstring:

- `decided` — "Four decision procedures returned `true`, and that is the whole of the claim."
- `entailment` — "Lean constructed a term of `WitnessFamily.Refutes …` for this certificate's
  target, **by applying a build-time kernel-checked implication to those four decisions**."
- and then, explicitly: "A third value, for per-certificate kernel checking by re-elaboration of a
  generated file, is deliberately **reserved and not introduced here**: nothing in this module
  produces it, and adding an inhabited-but-unreachable constructor would misrepresent what the
  binary can do."

`BimodalTools/CheckCertificateMain.lean` says the same in the other direction: "What is
kernel-checked is the **implication**, elaborated once when these modules compile. ... So this is
**not** per-certificate kernel checking: the verdict still inherits whatever trust is placed in
Lean's compiler and in this module's decoding."

Against that, this repository currently says:

- `ADEQUACY.md` §6.2: "*constructing* the paper-countermodel existence term rather than printing a
  verdict — **a kernel-checked proof for that particular certificate**, not merely four
  `Decidable` instances agreeing."
- `TRUST_PIPELINE.md`, "The trust base": "a `countermodel` verdict there is **a kernel-checked term
  Lean constructed for the certificate actually sent**".

Both phrasings name precisely the reserved third value. The accurate claim is narrower and still
strong: the implication is kernel-checked once at compile time; the hypothesis is decided per
certificate by compiled `Decidable` instances; the accepting branch cannot be taken without a term
of `WitnessFamily.Refutes`, so acceptance is structurally an entailment rather than a report about
four booleans — but the per-certificate step still rests on Lean's compiler and on this module's
decoding, not on the kernel.

**This is reported, not decided.** The sentences live in the wire task's documentation territory
and the COORDINATION paragraph directs this task to stop and defer at that boundary. What item 1
must not do is build an output label that repeats the overclaim — see Recommendations R1.

**F3. The Python re-check is already a mandatory output gate; what is missing is the independent
leg.** `semantic/model.py:62-95` runs `recheck` unconditionally on every satisfying solve,
deliberately outside any `try`/`except`, and raises `ModelConstructionError` on any verdict but
`countermodel`. Nothing in the package catches that exception (verified: the only non-test
occurrences of the name are its definition in `theory_lib/errors.py` and this raise). The
iteration path reaches the same site — `iterate.py`'s `build_new_model_structure` constructs a
`BimodalStructure`, so every iterated model is re-checked too.

So the honest framing of item 1 is not "add a gate where there is none". It is: **the gate exists,
it is backed by the Python re-checker alone, and the independent Lean leg that would make the gate
mean something beyond "our code agrees with our code" is a test tier that never runs in CI.**

`TRUST_PIPELINE.md`'s new remaining-work row currently says "in a default CI run the only check
validating a candidate countermodel against the semantics disappears". Read as "the only
*independent* check", that is exact. Read literally, it is too strong — the Python re-check
survives. Worth tightening when the row is extended (Recommendations R6).

**F4. The Lean leg never runs in CI, confirmed mechanically.** `BIMODAL_LOGIC_PATH` appears
nowhere in `.github/workflows/`, and no workflow installs `lake` or `elan`. Every Lean-differential
surface — `TestBoundedLeanCrossCheck`, `test_certificate_lean_agreement.py`, and
`test_semantics_core.py`'s live cross-check — therefore clean-skips on every CI run, by
`_lean_check.py`'s `SKIP_REASON` path. The `differential-tests.yml` workflow that *is* gating for
bimodal edits runs the Python/oracle cross-differential, which is a different comparison entirely.

### Math Findings — the check's cost is negligible, which is what makes a gate viable

**F5. The gate costs ~50ms, not ~2.2s. The test suite's figure measures `lake`, not the checker.**
`test_certificate_a2_triangle.py` records "`~2.2s` per `lake exe check_certificate` invocation
(measured at plan time)". Invoking the built binary directly:

| Invocation | Wall clock | Peak RSS |
|---|---|---|
| `check_certificate` on the trivial probe certificate (3 runs) | 0.04s each | ~120 MB |
| `check_certificate` on a live-extracted certificate (627 wire bytes) | 0.0512s | — |
| Whole `BimodalStructure` solve + Python `recheck`, same example | 0.0241s | — |

The ~2.2s is `lake`'s per-invocation build/manifest check. A production gate would invoke the
binary directly and pay ~50ms. Even under `iterate: N` that is N×50ms — negligible against solve
time on any nontrivial example.

This matters because it removes the obvious objection to making the check mandatory. The reason
the check is currently a sampled tier is availability, not cost.

**F6. The decision procedures' surface is small, which re-costs item 2's Python option.**
`semantic/certificate.py` is 518 lines, of which the decision procedures
(`_coherent_at`, `_fulfil_at`, `_box_faithful`, `_target_holds`, `recheck`) are roughly 190. The
dispatch asks that "a re-implementation in Python, which reintroduces the code-to-specification
gap this task exists to avoid" be "costed as such rather than dismissed". Costed honestly, the
implementation cost is *zero* — it is already written and running — and the epistemic cost is
*already being paid* on every live run. What a Python-only route forgoes is not the gap (the gap is
open regardless) but any per-run link between the running code and the Lean predicates that are
the contract (`ADEQUACY.md` §5.3). That is the correct basis on which to decline it.

### Cross-Domain Synthesis — item 2, the four routes costed on measurement

All sizes measured on this host, x86_64 Linux, from
`~/Projects/BimodalLogic/.lake/build/bin/check_certificate` (built 2026-09-27).

| Measurement | Value |
|---|---|
| Binary, as built (unstripped) | 313,863,000 B ≈ 299 MiB |
| Binary, stripped | 219,351,032 B ≈ 209 MiB |
| Binary, stripped + `gzip -9` (wheel-deflate proxy) | 69,143,681 B ≈ 66 MiB |
| Current `model_checker` wheel (1.3.7, `py3-none-any`) | 1,190,654 B ≈ 1.14 MiB |
| Dynamic dependencies | glibc only (`libc`, `libm`, `libpthread`, `libdl`, `librt`, `ld-linux`) — Lean runtime statically linked |
| Object files linked | 1,867 (1,496 Mathlib, 132 aesop, 74 batteries, rest small) |
| `l_Lean*` symbols in the binary | 212,374 |
| `Lean.Elab` (frontend/elaborator) symbols | 38,581 |
| Mathlib / FormalSystem / BimodalTools **runtime** symbols | 0 |
| `libleanshared.so` (toolchain) | 208,850,520 B ≈ 199 MiB |
| `libLean.a` (toolchain, frontend) | 249,403,904 B ≈ 238 MiB |
| `~/.elan` (full toolchain store) | 17 GB |
| `~/Projects/BimodalLogic/.lake/packages` (Mathlib et al. sources + builds) | 9.2 GB |

**F7. The binary is ~98% Lean frontend, and `supportInterpreter = true` is why.** The symbol
inventory is decisive: 212,374 `l_Lean*` symbols against zero from any mathematical library or
from the project's own modules, and a binary size (209 MiB stripped) that tracks `libLean.a`'s
238 MiB rather than any plausible size for the compiled mathematics. Every `[[lean_exe]]` in
BimodalLogic's `lakefile.toml` sets `supportInterpreter = true`, including `check_certificate`,
whose `main` is four lines of `IO` and needs no interpreter at run time.

**Every packaging route below should be re-costed after flipping that flag and re-measuring.** It
is a one-line change in the companion repository, it is squarely in that repository's territory,
and it plausibly moves the compressed artifact from ~66 MiB to single-digit or low-double-digit
MiB. This report does not claim the resulting number — it claims the measurement must precede the
decision, and names the evidence that makes it worth taking.

**Route A — extract the checker to a standalone verified artifact shipped in the wheel.**

- Buys: the gate becomes unconditional for every user with no Lean toolchain, at the `entailment`
  acceptance level. This is the only route that delivers item 1's strong form.
- Packaging cost, at today's size: the wheel goes from `py3-none-any` (one universal artifact,
  1.14 MiB) to per-platform wheels — `manylinux_x86_64`, `manylinux_aarch64`, `macosx_x86_64`,
  `macosx_arm64`, and Windows — each carrying ~66 MiB of binary. That is a ~58x wheel-size
  increase and a categorical change in the release pipeline (`release.yml` currently builds one
  universal wheel; it would need a cibuildwheel-style matrix).
- PyPI: the default per-file limit is 100 MB, so ~66 MiB fits with thin headroom; the 10 GB
  project limit is not at risk. Headroom is the concern, not the ceiling.
- Platform coverage: Lean 4 supports all five targets, but the binary built here links glibc 2.42
  from nix. A `manylinux` wheel needs a build inside a manylinux image to get a low glibc floor —
  standard practice, but new work here.
- CI: each platform needs a Mathlib-dependent Lean build. `lake exe cache get` covers Mathlib
  itself; `FormalSystem` and `BimodalTools` must be built per platform. Budget hours, not minutes,
  per release — and only per release, not per commit.
- Cross-repo coupling: the wheel would embed an artifact built from BimodalLogic at a pinned
  commit. `BIMODAL_LOGIC_COMMIT` is the right hook and is currently inert (F9).

**Route B — two-tier trust model: distinguish an unchecked from a checked countermodel.**

- Buys: honest labelling today at zero packaging cost. Output states become three, not two:
  *countermodel, independently checked (entailment)* / *countermodel, checked by the Python
  re-checker only* / *no certificate found within these bounds*.
- Cost: a production-side checker resolver (F8), a setting and its `SETTINGS.md` section, the
  labelling in `print_certificate`/`print_evaluation`, and tests. Small and entirely local.
- Does not buy: any improvement for the default user, who stays in the second tier. It converts a
  silent gap into a visible one — which is the point, but it is not the gate.

**Route C — Python re-implementation.** Already built (F6); adds nothing; declined, on the basis
that it supplies no per-run link to the Lean predicates rather than on the basis of a gap it would
"reintroduce" (the gap is already open on the live path).

**Route D — require the Lean toolchain.** Declined on measured grounds: 17 GB of toolchain store
and a 9.2 GB package tree on this machine, for a package whose current wheel is 1.14 MiB and whose
users are logicians running `model-checker examples.py`. It would also make the bimodal theory the
only theory in `theory_lib/` with a non-Python prerequisite.

**Recommended composition, and why it is not simply Route A.** Route A is the destination; its
current price tag is set almost entirely by a build flag in another repository. So:

1. **Route B now** — it is independently correct (an unchecked countermodel *should* say so),
   unblocks nothing else, and costs days not weeks.
2. **Measure the trimmed binary** — `supportInterpreter = false` in BimodalLogic, rebuild,
   re-measure stripped and compressed size. This is the decision input for step 3 and it is cheap.
3. **Out-of-band opt-in binary** — publish the per-platform checker as a GitHub release asset of
   the companion repository and add a `model-checker fetch-checker` (or equivalent) command that
   downloads and verifies it by hash. This delivers Route A's user-facing benefit with none of its
   wheel-size, platform-tag or PyPI-limit cost, keeps `py3-none-any`, and leaves the release
   pipeline universal. Users who opt in get tier 1; the wheel stays 1.14 MiB.
4. **In-wheel shipping only if step 2's number justifies it** — a single-digit-MiB compressed
   artifact changes the calculus; a 66 MiB one does not.

This staging also has the property that each step is independently valuable and none blocks on the
Lean development.

### Item 1 — the output gate, assessed

**F8. `tests/_lean_check.py` cannot be the gate's resolver.** Two disqualifying properties: it
computes `SKIP_REASON` at **module import time** by running `probe()` with a 60-second timeout
(`PROBE_TIMEOUT_SECONDS = 60`), and it lives in the test tree. The first is fatal in a production
import path; the second is a layering violation even though the tests *are* shipped in the wheel
(verified: 21 bimodal test files are present in `model_checker-1.3.7-py3-none-any.whl`). A
production gate needs its own resolver module under `semantic/` with lazy, bounded probing and a
resolution order that prefers a bundled/fetched binary over a `lake` checkout. The invocation and
echo-comparison logic itself (`run_check_certificate_with_sent`, `assert_echo_matches_sent`,
`canonical_wire_bytes`) is reusable as-is — `canonical_wire_bytes` already lives in
`semantic/certificate.py`, on the production side.

**F9. `BIMODAL_LOGIC_COMMIT` is a dead pin, and the checkout has already drifted from it.** The
constant is declared and exported in `_lean_check.py:77` and consumed by nothing in the repository
(verified across `*.py`, `*.md`, `*.yml` outside `specs/`). The local checkout's HEAD is
`d1a24b3076875c50431991385c749ad1bec9c1fd`; the pin is
`d55e2760e6731a2240f3db5d761658947bf69125` — drift within the same day the pin was refreshed. As a
provenance record that is acceptable; as the basis for a *gate* it is not. A gate must know which
checker contract it is gating against, because the acceptance vocabulary (`decided` vs.
`entailment`) and the `"echo"` field are both properties of a particular binary version. Whatever
identity check the gate uses — a `--version` handshake on the binary, a hash of a fetched
artifact, or an asserted commit — it must be *enforced*, not recorded.

**Impact on the user-facing contract.** Three output states instead of two. The change is additive
for the existing two and requires no change to the never-report-validity rule's substance, but
§7.4 should state explicitly that an *unchecked* countermodel is not a validity claim either — an
obvious point that becomes non-obvious once a third state exists, because a reader could take
"unchecked" as hedging about the *inference* rather than about the *certificate*.

**Impact on `SETTINGS.md`.** There is no verification-related setting today; `DEFAULT_EXAMPLE_SETTINGS`
is `back`/`mid`/`fwd`/`max_witnesses`/`max_time`/`expectation`/`iterate`/`solver`. Item 1 adds one
(the gate's strictness: label-only, or refuse to report an unchecked countermodel) plus a new
`SETTINGS.md` section. Note the existing document has no "Verification" section to extend, so this
is a new section rather than an edit — low collision risk with the wire task's own `SETTINGS.md`
overlap, but re-read before editing per COORDINATION.

**Impact on §7.4's guard.** None to the rule; the rendering guards in `print_certificate` and
`print_evaluation` ("This is not a validity claim (docs/ADEQUACY.md section 7.4)") are on the
no-certificate path and are untouched by a change to the countermodel path. The gate adds a
*third* rendering that needs its own honest wording, which is new text beside them, not a
modification of them.

**Verdict on item 1's explicit question.** Ship the gate. The "weaker check" concern is moot
(F1): the available check is the entailment level, not the four-booleans level. The residual risk
is not that the check is too weak but that the *documentation around it* currently describes it as
stronger than it is (F2) — so the gate's label must be written from the Lean module's own
vocabulary, not from `ADEQUACY.md` §6.2's sentence.

### Item 3 — ledger confirmation, and what the extension actually found

**F10. All three already-applied `TRUST_PIPELINE.md` edits read correctly against what landed.**
The edits are in commit `c545194d`; task 197's later commits (`f129de97`, `16a14e8d`) edited the
same table without disturbing them, and all three survive in the current file.

| Claimed edit | Verified against | Verdict |
|---|---|---|
| Stale "Widen the A2 grid to `nb = nf = 2`" remaining-work row removed | Row absent from the current table; the widened cases exist as `box_free_*_nb2_nf2` params and `test_boxed_closure_enumeration_agrees_with_z3_nb2_nf2` | **Correct** |
| "The standing test for A2" no longer claims blindness; records the closed `nb=2` blind spot with its measured cost, and the aggregate→per-candidate move | `TestExhaustiveTriangleWithBox`'s docstring records 10,485,760 candidates / 5,115 accepted / 123.29s under CI's invocation shape; 123.29/300 = 41%, so "roughly 59% inside the 300s per-test ceiling" is arithmetically right; `_run_exhaustive_triangle` raises on the first per-candidate divergence and `_assert_exhaustive_triangle_agrees` retains `(accepted > 0) == structure.z3_model_status` beside it | **Correct** |
| Two new remaining-work rows for this task's items 1 and 2 | Both present ("Make the Lean check a gate on reported output", "Ship the checker so the gate does not require a Lean toolchain") | **Correct** |

One wording refinement for the extension, not an error: the gate row's "the only check validating a
candidate countermodel against the semantics disappears" should read "the only *independent*
check", since the Python re-check survives in the live path (F3).

**F11. `A2_GAP.md` section 8's limit 3 is stale in exactly the way `TRUST_PIPELINE.md` was
repaired.** It still reads:

> **The leg (i)/(iii) comparison itself is aggregate, not per-candidate.** ... asserts
> `(accepted > 0) == structure.z3_model_status`, not "for each candidate, ..." ... **The open
> obligation this limit names, precisely**: assert per candidate that every emitted clause is true
> under the candidate's pinned assignment iff the re-checker accepts it. A solver-free pinned
> evaluator — substituting the candidate's fixed values into the emitted clause set and checking
> truth directly, rather than issuing a fresh Z3 call per candidate — is the affordable form of
> this check over the same enumerated space.

That obligation is discharged. `tests/_pinned_eval.py`'s `compile_and_bind` is precisely the
prescribed solver-free pinned evaluator, and `_run_exhaustive_triangle` runs the per-candidate
comparison and raises on the first divergence. The document names its own solution and does not
record that it was built. This is the single most consequential item-3 finding and is a direct
extension of the repair already applied one document over.

**F12. `ADEQUACY.md` §7.1's sweep arithmetic contradicts `SEARCH_COVERAGE.md`'s decision, in two
places.** §7.1 says the sweep is over "`(back, mid, fwd)` triples up to `f(|C|)` ... `f^3` solver
calls", and again at (iii-a): "sweep `(back, mid, fwd)` over the grid up to the bound (`f^3`
individually cheap solves ...)". `SEARCH_COVERAGE.md` §1 establishes that `mid` "has no
periodicity at all ... so it never participates in this gap", and §3(b) states the conclusion
explicitly: "This makes the sweep **quadratic**, `O(back * fwd)` solver calls, **not cubic** in the
three settings together", sweeping `back' ∈ [1, back] × fwd' ∈ [1, fwd]` with `mid` fixed. §7.1
predates that decision and was not updated when `SEARCH_COVERAGE.md` landed. `f^3` overstates the
cost of the route this repository has chosen by a factor of `f`.

**F13. `ADEQUACY.md` §7.3's "Two tiers" paragraph is stale in two respects.** It describes "an
exhaustive Tier 1 comparing legs (i) and (iii) over every candidate at `back = mid = fwd = 1`" and
then adds the wider grid two sentences later — so the first clause reads as the whole story. And
it never records either (a) that the comparison is now per-candidate, or (b) that each candidate's
leg (iii) is a **solver-free evaluation of the encoding's own emitted constraint list**, with the
retained aggregate assertion being the only check of the real Z3 *search* verdict. Both facts are
recorded in the test module's docstring and in `TRUST_PIPELINE.md`; §7.3, which is the section the
test cites as its specification, has neither.

**F14. The liveness/regression reclassification, and the cost reassessment it licenses.** The
dispatch asks that wherever the tiers are described, it be stated explicitly that the Tier 1
differential and the search-coverage grid pins are liveness and regression evidence for the UNSAT
direction rather than countermodel trust. The surfaces where "the tiers" are described:

| Surface | Current framing | What is missing |
|---|---|---|
| `TRUST_PIPELINE.md`, "The standing test for A2" | Localization value, the closed blind spot, the per-candidate move | The direction claim: this is (ADEQ)-side evidence, not (SOUND)-side |
| `ADEQUACY.md` §7.3, "Two tiers" | Tiering and grid | The direction claim, plus F13's two staleness points |
| `A2_GAP.md` §8 | Three limits on what passing establishes | The direction claim; limit 3 is also stale (F11) |
| `SEARCH_COVERAGE.md` §1 | "Neither test module is a claim of encoding *incompleteness*" | Partially there — says what it is *not*, not that it is UNSAT-direction liveness evidence |
| `tests/README.md:76` | One-line module description | The direction claim |
| `test_certificate_a2_triangle.py` docstring | "What is novel here", localization | The direction claim |
| `test_search_period_coverage.py` docstring | "What this module does and does not establish" | Closest of all — says it is not an encoding-completeness defect; still not framed as liveness evidence |

**Cost reassessment on that basis** (measured figures from the test docstrings, all under CI's own
invocation shape `-n 4 -q --timeout=300 --timeout-method=thread` over `tests/ src/model_checker`):

| Case | Cost | Marker | Reassessment |
|---|---|---|---|
| `box_free_until_conclusion_sat_nb2_nf2` | 1.94s | none | Keep unconditional |
| three remaining box-free cases | <0.01s each | none | Keep unconditional |
| `test_boxed_closure_enumeration_agrees_with_z3` (`nb=nf=1`) | 17.77s | `slow` | Keep |
| `test_boxed_closure_enumeration_agrees_with_z3_nb2_nf2` | 123.29s | `slow` | Keep — see below |
| `test_search_period_coverage.py`, all ten grid points | ~0.92s total | none | Keep unconditional |

The 123.29s case is the only one where the reclassification could plausibly argue for narrowing,
and it should not. Under the governing asymmetry, the UNSAT direction is exactly where results are
*not* independently checkable, so liveness/regression evidence there is not a lesser thing to be
economized — it is the only evidence available in that direction, and it covers the one A2 defect
known to have actually occurred. The honest caveat is the margin, which the test's own docstring
already states: 123.29s against a 300s ceiling assumes CI hardware no more than ~2.4x slower than
this host, and the named contingency (a deterministic stride, never a weakened assertion) is
already recorded. Nothing here licenses deleting or narrowing any test, and the retained aggregate
assertion stays.

### Deferred follow-on, recorded so it is not rediscovered

**Structural conformance check: the emitted Z3 constraint set matches the (C1)-(C4) schema
instantiated at the configured bounds.** Linear in formula size rather than in candidate space.
The infrastructure it would extend already exists and is worth naming precisely so the follow-on
is cheap to pick up:

- `tests/_pinned_eval.py`'s `full_constraints(structure)` — the complete post-`finalize_certificate`
  constraint set, now a named alias for `structure.model_constraints.all_constraints`, which the
  stale-snapshot task made a computed read-only property (that change is what makes such a check
  trustworthy rather than a snapshot comparison).
- `tests/unit/test_pinned_eval.py`'s `TestOperatorInventoryIsClosed` — every node in
  `full_constraints` compiles, and every leaf atom name falls in one of the three closed families
  `lab_`/`bx_`/`sel_`, at both grid sizes.
- `tests/unit/test_pinned_eval.py`'s `TestAssignmentCoverage` — the builder's key set is exactly
  the compiled atom index's key set: no unpopulated referenced atom, no stray key.

A conformance check would add, on top of these: that the *shape* of the emitted clause set matches
(C1)-(C4)'s schema at the configured `(nb, nm, nf)` — the right number of coherence clauses per
lasso position, the right fulfilment scan bounds, one one-hot `sel` block over
`WitnessRegistry.target_window()`, and no clause outside that schema.

**Sequencing: explicitly after everything above.** It is UNSAT-direction work. Under the governing
asymmetry it ranks below the output gate and the checker's availability, both of which are
(SOUND)-direction, and below item 3's ledger repair, which is nearly free. **Do not build it in
this task.**

---

## Decisions

- **D1. Report F2's overclaim rather than fix it.** The sentences are in `ADEQUACY.md` §6.2 and
  `TRUST_PIPELINE.md`'s trust base, both wire-task territory. COORDINATION directs deferral at
  that boundary. Item 1's own new text must be written from the Lean `Acceptance` vocabulary
  directly.
- **D2. Recommend the staged composition for item 2, not a single route.** Route A's price is set
  by a build flag in another repository (F7), so recommending it or rejecting it before that
  measurement would be guessing. Route B is recommended unconditionally because it is correct on
  its own terms.
- **D3. Recommend keeping the 123.29s case despite reclassifying what it establishes.** Argued
  from the governing asymmetry in F14, not from sunk cost.
- **D4. Treat F9 (the dead pin) as in scope for item 1, not as a wire-task concern.** The pin's
  *contents* are wire provenance; its *enforcement* is a precondition of gating, which item 1 owns.
- **D5. No file outside this task's report was edited.** Item 3's confirmations are recorded here;
  the extending edits belong to the implementation phase. Sibling task 206 is dispatched into the
  same working tree this cycle with no declared `file_scope`, and this dispatch touched only
  `specs/205_*/`.

---

## Risks & Mitigations

| Risk | Sev | Mitigation |
|---|---|---|
| The planner builds item 1 on the dispatch's stale "verdict-producing" premise and designs a weaker interim label than the checker supports | H | F1 states the measured verdict; R1 gives the label vocabulary |
| The gate's label repeats `ADEQUACY.md` §6.2's "kernel-checked proof for that particular certificate" | H | F2 quotes the Lean module's own three-level vocabulary; write the label from that source |
| Item 2 is costed against the 209 MiB / 66 MiB figures and Route A is rejected on a number that a one-line upstream change invalidates | H | F7's symbol inventory; step 2 of the staged path makes the measurement a precondition |
| A production gate imports `tests/_lean_check.py` and inherits a 60s import-time probe | H | F8; the gate needs its own resolver with lazy bounded probing |
| The gate is built over an unpinned checker, so the acceptance vocabulary it reads is not guaranteed present | M | F9; enforce the identity check rather than recording it |
| `ADEQUACY.md` §6.2 / §7.4 / `SETTINGS.md` edits collide with the wire task's own overlap | M | COORDINATION's re-read directive; §7.4 needs an addition beside its guards, not a modification, and `SETTINGS.md` needs a new section rather than an edit |
| Item 3's edits duplicate rather than extend the three already-applied ones | M | F10's table states exactly what is already there; F11-F14 state what is not |
| `A2_GAP.md` limit 3 is left stale while the other documents are repaired, recreating the same divergence one document over | M | F11 |
| Cold-cache first invocation of a 209 MiB binary pays page-in cost | L | ~120 MB RSS observed; unmeasured cold, but bounded by that and one-time per process |
| The trimmed-binary measurement requires a BimodalLogic build the plan cannot schedule | L | It is a one-line lakefile change plus a rebuild in that repository; if unavailable, Route B still stands alone and step 3 can use the untrimmed artifact |

---

## Recommendations

**R1. Specify item 1's output states from the Lean `Acceptance` vocabulary, not from §6.2's
sentence.** Three states: *countermodel, independently checked (`acceptance: entailment` — Lean
constructed a `WitnessFamily.Refutes` term by applying a compile-time kernel-checked implication to
four run-time decisions)*; *countermodel, re-checked in Python only (`decided`-equivalent — four
decision procedures returned true)*; *no certificate found within these bounds (not a validity
claim)*. Never describe the first as a per-certificate kernel-checked proof.

**R2. Build a production-side checker resolver under `semantic/`,** with lazy bounded probing,
resolution order (bundled/fetched artifact → `BIMODAL_LOGIC_PATH` checkout → unavailable), an
enforced version handshake (F9), and reuse of `canonical_wire_bytes` plus the echo comparison.
Refactor `tests/_lean_check.py` to consume it rather than duplicating it — but keep the test
module's import-time probe behaviour where the tests rely on it, or move that probe behind an
explicit call.

**R3. Ship the two-tier labelling and its setting first,** with a `SETTINGS.md` "Certificate
verification" section, an addition to §7.4 stating that an unchecked countermodel is not a validity
claim either, and tests covering all three output states.

**R4. Measure `supportInterpreter = false` before deciding the packaging route.** One-line change
in BimodalLogic's `lakefile.toml` for the `check_certificate` target, rebuild, record stripped and
`gzip -9` sizes. This is the single highest-leverage unknown in the task.

**R5. Then implement the out-of-band opt-in artifact** (GitHub release asset + hash-verified fetch
command), keeping the wheel `py3-none-any`. Defer in-wheel shipping until R4's number justifies
the per-platform release matrix.

**R6. Item 3's ledger edits, in dependency order:**
   a. `A2_GAP.md` §8 limit 3 — record the obligation as discharged, naming
      `tests/_pinned_eval.py`'s evaluator and `_run_exhaustive_triangle`'s first-divergence raise;
      keep the aggregate/per-candidate distinction and the retained aggregate assertion (F11).
   b. `ADEQUACY.md` §7.1 — correct `f^3` to the quadratic `O(back × fwd)` sweep in both places,
      and state that `mid` never participates, citing `SEARCH_COVERAGE.md` §3(b) (F12).
   c. `ADEQUACY.md` §7.3 — lead with both grid sizes, record the per-candidate comparison and the
      solver-free pinned evaluation of leg (iii), and note that the retained aggregate assertion is
      the only check of the real Z3 search verdict (F13).
   d. The direction claim, added at each of the seven surfaces in F14's table: the Tier 1
      differential and the search-coverage grid pins are liveness and regression evidence for the
      UNSAT direction, not countermodel trust.
   e. `TRUST_PIPELINE.md`'s gate row — "the only *independent* check" (F3/F10).

**R7. Record the structural conformance check as a follow-on** in `TRUST_PIPELINE.md`'s remaining
work, with the reasoning and the anchors named above, explicitly sequenced after items 1 and 2. Do
not build it.

---

## Deferred to the certificate-wire hardening task (reported, not decided)

- The `ADEQUACY.md` §6.2 and `TRUST_PIPELINE.md` trust-base overclaim (F2). A one-sentence
  correction in each; the accurate narrower claim is stated in F2.
- Whether `BIMODAL_LOGIC_COMMIT`'s *contents* should track the companion repository automatically.
  Item 1 owns only that some identity check must be enforced (F9/D4).

## Incidental observations, not acted on

- `~/Projects/BimodalLogic` now contains a `translate_sentence` executable (built 2026-09-27) and a
  `BimodalTools.TranslateSentenceMain` target described as "the verified reference for the
  companion repository's own elimination of its defined operators". `TRUST_PIPELINE.md` and
  `ADEQUACY.md` §6.3 both record a Lean-side translation as "confirmed absent from the local
  `BimodalLogic` checkout" and deferred. That is obligation S4, out of scope here, but the ledger
  claim appears to have been overtaken by events and is worth a look by whoever owns S4.
- BimodalLogic's `lean-toolchain` pins `leanprover/lean4:v4.33.0-rc1` while the locally built
  binaries came from Lean 4.27.0-rc1 / Lake 5.0.0. The binary works; noted only because a gate
  would care which toolchain produced the artifact it trusts.
- The wheel ships 21 bimodal test files. Out of scope (harness reorganization territory), noted
  because F8's layering argument brushes against it.
