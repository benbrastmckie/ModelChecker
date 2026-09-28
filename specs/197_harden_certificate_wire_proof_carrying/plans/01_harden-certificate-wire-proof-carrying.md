# Implementation Plan: Harden Certificate Wire Proof-Carrying

- **Task**: 197 - Harden certificate wire proof carrying
- **Status**: [IMPLEMENTING]
- **Effort**: 6.75 hours
- **Dependencies**: BimodalLogic task 677 (landed, committed — axis 1 unblocked); BimodalLogic
  task 678 phase 9 (in flight, uncommitted — axis 2 gated, see Phase 5's admission gate)
- **Research Inputs**: `specs/197_harden_certificate_wire_proof_carrying/reports/01_harden-certificate-wire-proof-carrying.md`
- **Artifacts**: plans/01_harden-certificate-wire-proof-carrying.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: z3
- **Lean Intent**: false

## Overview

The wire protocol between this repository's certificate exporter and `lake exe check_certificate`
has become **canonical-bytes-only** on the consuming side, and this repository has not caught up:
the differential test tier is, as of this plan's own measurements, silently dead. This plan first
restores that tier by emitting canonical bytes, then hardens the tier so a protocol failure can
never again masquerade as a clean skip, then consumes the landed `"acceptance"` key (axis 1) and
corrects the doc sites that understate what a `countermodel` verdict now means. Axis 2 (parse-echo
verification) is carried as a **gated** phase with a concrete admission measurement, because its
`"echo"` interface exists in BimodalLogic's working tree but is not yet committed. Done means: the
differential tier runs (does not skip) against a present checkout, asserts on `"acceptance"`, the
docs state the narrower true claim, and axis 2 is either implemented or closed with a recorded
gate measurement — never half-asserted.

### Research Integration

The research report (F1-F6) established that axis 1 is unblocked, that the addition is purely
additive on the wire, that the joint "fast pre-filter" claim needs both halves, that no live
per-run Lean consumption point exists on this side (only the test tier), and which doc sites
understate the landed state. All of that is carried forward unchanged.

**Three findings this plan adds by direct measurement, which supersede or extend the report's
picture** (the report ran roughly an hour before this plan; BimodalLogic committed two further
phases in that window):

- **M1 — The differential tier is currently dead, silently.** BimodalLogic's committed HEAD
  (`12be620c2`, "task 678 phase 8: migrate the certificate envelope onto the verified codec")
  routes `parseCertificate` through `parseCertificateCanonical`, a strict canonical-bytes parser
  that **rejects interior whitespace** (trailing whitespace only is skipped). `_lean_check.py`'s
  `run_check_certificate` sends `json.dumps(payload)`, whose default separators are `", "` and
  `": "`. Measured directly:

      $ PYTHONPATH=code/src python3 -c "from model_checker.theory_lib.bimodal.tests import
        _lean_check as lc; print(repr(lc.SKIP_REASON))"
      "probe certificate produced unexpected verdict: {'status': 'error',
       'message': 'expected a decimal numeral'}"

  Because `probe()` collapses every non-`countermodel` verdict into a `SKIP_REASON` string, the
  whole differential tier — `test_certificate_lean_agreement.py`,
  `test_certificate_a2_triangle.py`, and `test_semantics_core.py`'s
  `TestExportedCertificateAgreesWithLeanBinary` — now **clean-skips with a present checkout and a
  working binary**. This is a committed-side reality, not in-flight work, and it is the single
  most urgent item here. Re-sent with `separators=(",", ":")` the same payload yields
  `{"status":"countermodel","time":0,"acceptance":"entailment","echo":"…"}`.

- **M2 — Axis 2's `"echo"` key exists, but only in BimodalLogic's uncommitted working tree.**
  `git status --porcelain` in that checkout shows `M BimodalTools/CertificateImport.lean`,
  `M BimodalTools/README.md`, `M Tests/BimodalToolsTest.lean`, `?? Tests/BimodalToolsTest/CanonicalWireTest.lean`
  — phase 9 is being written right now. `git diff` confirms the uncommitted hunks add
  `CheckResult.toJsonWithEcho` and route `checkLineToJson` through it, echoing `raw.toJson`. The
  committed README still carries the "**The downstream payoff is jointly gated, and has not landed
  yet.**" paragraph that phase 9's task list slates for replacement. So the interface is
  observable but not yet a contract.

- **M3 — When it does land, axis 2 is bytewise-implementable, and the echo is a canonical
  *reprint*, not a verbatim copy.** Sending each of the four corpus fixtures as
  `json.dumps(fixture, separators=(",", ":"), ensure_ascii=False)` produced `echo == sent` bytewise
  on all four (`01_positive_box` → `countermodel`; the other three → `rejected`, each with the
  expected `condition`, and each carrying an `"echo"`). `error` carries no echo. Sending the same
  certificate with **reordered top-level keys** still succeeded, but the echo came back in
  canonical key order — so bytewise equality holds only because this repository's
  `WitnessFamily.to_json` / `formula.to_json` already emit canonical key order
  (`target{premises,conclusions,time}`, `bx`, `lassos{back,mid,fwd}`; `imp{left,right}`,
  `untl`/`snce`{`event`,`guard`}, `box{child}`, `atom{name}`). A non-ASCII atom name round-tripped
  only with `ensure_ascii=False`, matching phase 9's own producing-side hand-off note.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in this dispatch's delegation context, so no roadmap consultation
was performed.

## Goals & Non-Goals

**Goals**:
- Restore the differential test tier by emitting canonical wire bytes from a single, protocol-owned
  serializer (M1).
- Make a protocol-level failure from a present, working binary a **loud failure**, never a clean
  skip — the error-versus-rejected distinction, enforced on this side of the wire too.
- Consume the landed `"acceptance"` key on accepting verdicts, with the absent-reads-as-`"decided"`
  rule encoded explicitly (axis 1).
- Correct `ADEQUACY.md`, `TRUST_PIPELINE.md` and `A2_GAP.md` to state the narrower true claim about
  what a `countermodel` verdict now means, and to record the canonical-bytes requirement as part of
  the §6.1 wire contract.
- Carry axis 2 (parse-echo verification) as a gated phase with an explicit admission measurement,
  so an implementer who finds it unblocked implements it and one who does not closes it with
  evidence.

**Non-Goals**:
- **Do not** write the joint "the Python re-checker is a fast pre-filter, no longer in the trust
  base" claim anywhere unless Phase 5 actually executes (not excluded). BimodalLogic's own
  committed README states this payoff "is jointly gated, and has not landed yet"; writing it early
  would make this repository's docs contradict the producing side's own contract.
- **Do not** wire `lake exe check_certificate` into the live per-run path in `semantic/model.py`.
  That is a separate, already-named row in `TRUST_PIPELINE.md`'s "What remains" ("Make the Lean
  check a gate on reported output") and is out of scope (report F4).
- **Do not** rename or extend `back`, `mid`, `fwd`, `bx`, `lassos` or `target`. Every change on
  both sides is output-side and additive; no input-schema change is needed or permitted here.
- **Do not** edit anything in the BimodalLogic checkout. It has an agent actively working in it
  (M2); this repository is the consuming side only.
- **Do not** change `semantic/model.py`'s live re-check semantics or its fail-fast behavior.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The implementer writes the joint "fast pre-filter" doc claim because the task description bundles both axes | H | M | Phase 4's tasks name the prohibition inline and Phase 6 is the only phase permitted to write it, gated on Phase 5 executing. The report's F3 quotes BimodalLogic's README verbatim; cite it rather than re-deriving |
| BimodalLogic commits phase 9 mid-implementation, so the axis-2 gate flips between phases | M | H | Phase 5's gate is a **measurement taken at Phase 5's own start**, not a fact inherited from this plan. Whichever branch it takes is recorded with the measurement that chose it |
| BimodalLogic's in-flight tree changes the wire again (e.g. phase 9 lands `\uXXXX` rejection, which the tree currently accepts) and this side breaks a second time | M | M | Phase 2's loud-failure discipline is exactly the guard: the next such change fails a test instead of silently skipping. Phase 1's serializer is the single place a canonical-form change has to be made |
| Pinning `BIMODAL_LOGIC_COMMIT` to a commit while that checkout is dirty records a provenance claim that was never actually exercised | M | H | Phase 3 requires `git status --porcelain` in that checkout to be empty before pinning; if it is not, record HEAD **and** state in the docstring that uncommitted work was present |
| A sibling task (207, 208) edits the same bimodal test files this cycle | L | L | Territory discipline: re-read every file immediately before editing, stage only this task's own hunks with an explicit file list, never `git add -A` or a directory pathspec, and never `git-snapshot.sh` in reverting default mode |
| Canonical key order holds for the four corpus fixtures but not for some formula shape they do not cover | M | L | Phase 1's unit test asserts canonical-form properties on a constructed payload covering every `to_json` tag, not only on the corpus; Phase 5's echo comparison is the mechanical catch for the rest |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4, 5 | 2, 3 |
| 4 | 6 | 5 |

Phases within the same wave can execute in parallel.

### Phase 1: Canonical wire bytes, in the protocol module [COMPLETED]

**Goal**: this repository emits canonical wire bytes, so `lake exe check_certificate` at
BimodalLogic's committed HEAD accepts what it is sent, and the differential tier stops skipping.
The serializer lives with the protocol, not in a test helper, because axis 2's comparison ("the
bytes this repository sent") needs exactly one authoritative answer to what those bytes are.

**Tasks**:
- [x] Add `canonical_wire_bytes(payload: Mapping[str, object]) -> str` to
      `semantic/certificate.py`, next to the wire writer: `json.dumps(payload, separators=(",", ":"),
      ensure_ascii=False)`. Document in its docstring *why* each argument is load-bearing — the
      consuming parser rejects interior whitespace (trailing whitespace only is skipped), and
      `ensure_ascii=False` is the producing-side hand-off BimodalLogic's phase 9 names — and that
      key order is already canonical by construction of `WitnessFamily.to_json` and
      `formula.to_json`, not by sorting.
- [x] Do **not** sort keys. Canonical order is insertion order here; `sort_keys=True` would
      actively break it (`target` before `bx` before `lassos` is not alphabetical).
- [x] Change `_lean_check.py`'s `run_check_certificate` to send `canonical_wire_bytes(payload)`
      instead of `json.dumps(payload)`. Export nothing new from `_lean_check.py`; it imports the
      serializer.
- [x] Add a unit test in `tests/unit/` asserting the canonical-form properties directly: no
      `", "` or `": "` substring in the output; a non-ASCII atom name survives unescaped; and the
      emitted key order for a payload exercising **every** `formula.to_json` tag (`atom`, `bot`,
      `imp`, `box`, `untl`, `snce`) matches the canonical order the consuming printer uses.

**Timing**: 1.25 hours

**Depends on**: none

**Verification Tier**: interface

**Scope Hypothesis**: this phase asserts that exactly one call site serializes a payload for the
Lean binary (`_lean_check.py:78`'s `json.dumps(payload)`). Confirm at implementation time with
`grep -rn "json.dumps" code/src/model_checker/theory_lib/bimodal/` and fix every site the grep
finds that feeds the binary; if it finds more than one, say so rather than fixing only the named
one.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py` - add
  `canonical_wire_bytes`, with the canonical-form rationale in its docstring
- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py` - use it in
  `run_check_certificate`
- `code/src/model_checker/theory_lib/bimodal/tests/unit/` - new or extended unit test for the
  canonical-form properties

**Verification**:
- `PYTHONPATH=code/src python3 -c "from model_checker.theory_lib.bimodal.tests import _lean_check
  as lc; print(repr(lc.SKIP_REASON))"` prints `None` (it currently prints the `expected a decimal
  numeral` protocol error quoted in M1). This is the phase's decisive check: the tier is alive.
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py -v`
  runs its fixtures rather than reporting them skipped, and passes.
- `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q` green.

---

### Phase 2: A protocol failure is loud, never a clean skip [NOT STARTED]

**Goal**: the skip path covers *environment absence* only. A present checkout whose binary
responds with `"error"` on a well-formed probe certificate is a protocol disagreement and must fail
loudly — which is the same error-versus-rejected discipline the wire contract states, applied to
this side of it. This is the guard that would have surfaced M1 the day it appeared instead of
silently deleting the tier.

**Tasks**:
- [ ] Split `probe()`'s failure vocabulary in `_lean_check.py`: an unresponsive, unbuildable, or
      absent binary (and an absent checkout, and `lake` missing) remain clean skip reasons; a
      binary that *answers* with `status == "error"` on the trivial well-formed probe becomes a
      distinct, non-skip condition.
- [ ] Surface that condition as a hard failure rather than a skip. Prefer a module-level
      `PROTOCOL_FAILURE: Optional[str]` alongside `SKIP_REASON`, and a single test in the
      differential module asserting `PROTOCOL_FAILURE is None` with the verdict quoted in the
      message, so the failure names the payload shape and the verdict — not merely "a test failed".
      Keep `SKIP_REASON`'s existing meaning and spelling intact so the three consuming modules'
      `skipif` markers keep working unchanged.
- [ ] Add the new name to `__all__` and record the distinction in the module docstring: which
      outcomes are environment (skip) and which are protocol (fail), and why conflating them cost
      the tier its liveness.
- [ ] Verify the three consumers still skip cleanly with the checkout absent:
      `BIMODAL_LOGIC_PATH=/nonexistent` must skip, not fail.

**Timing**: 0.75 hours

**Depends on**: 1

**Verification Tier**: interface

**Scope Hypothesis**: three modules consume `_lean_check`'s skip machinery
(`test_certificate_lean_agreement.py`, `test_certificate_a2_triangle.py`,
`tests/unit/test_semantics_core.py`). Confirm with
`grep -rn "_lean_check" code/src/model_checker/theory_lib/bimodal/` before editing; every consumer
the grep finds must still skip cleanly under an absent checkout.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py` - split the probe's failure
  vocabulary; add `PROTOCOL_FAILURE`; docstring
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py` -
  the one assertion that `PROTOCOL_FAILURE is None`

**Verification**:
- `BIMODAL_LOGIC_PATH=/nonexistent PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q`
  reports skips, zero failures.
- With the real checkout present, the same suite runs the tier and is green.
- Temporarily reverting Phase 1's serializer change locally makes the new assertion **fail**
  (not skip); restore it afterwards. Record the observed failure message in the phase's commit
  body — this is the phase's whole point, so it is verified by observation, not by inspection.

---

### Phase 3: Consume the `"acceptance"` key (axis 1) [NOT STARTED]

**Goal**: an accepting verdict's `"acceptance"` is read, asserted, and its absent-field rule
encoded, so a `countermodel` from the binary is recorded as "Lean constructed the entailment term"
where it says so — and as the weaker "four `Decidable` instances returned true" where the field is
absent.

**Tasks**:
- [ ] In `test_certificate_lean_agreement.py`'s `TestLeanAgreement`, on fixtures whose expected
      status is `countermodel`, read `verdict.get("acceptance", "decided")`, assert it is one of
      `{"entailment", "decided"}`, and assert it is `"entailment"` against the current binary.
      Write the absent-reads-as-`"decided"` rule into the assertion message, not only a comment,
      so a future older-binary run explains itself.
- [ ] Extend `test_semantics_core.py`'s `TestExportedCertificateAgreesWithLeanBinary` the same
      way, on the live-extracted certificate rather than a fixture: this is the one place a
      certificate this repository actually *built* gets an entailment-grade verdict.
- [ ] Record in both modules' docstrings what the two values mean and that `"acceptance"` appears
      on `countermodel` only — never on `rejected` or `error` — so no one asserts it on a
      rejection path.
- [ ] Refresh `BIMODAL_LOGIC_COMMIT` in `_lean_check.py`, and the matching provenance line in
      `test_certificate_lean_agreement.py`'s docstring ("**Agreement observed against BimodalLogic
      commit**"), to the commit actually exercised. Before pinning, confirm
      `git -C ~/Projects/BimodalLogic status --porcelain` is empty; if it is not (M2 says it
      currently is not), pin HEAD **and** state in the docstring that uncommitted work was present
      in that checkout when agreement was observed.

**Timing**: 1.25 hours

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: two test modules assert on a Lean verdict's shape today
(`test_certificate_lean_agreement.py`, `tests/unit/test_semantics_core.py`), plus
`test_certificate_a2_triangle.py` which consumes the helper for a different leg. Confirm with
`grep -rn "run_check_certificate\|lean_verdict" code/src/model_checker/theory_lib/bimodal/tests/`;
add the `acceptance` assertion wherever an accepting verdict is already inspected, and say which
sites were left alone and why.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py` -
  the `acceptance` assertion; provenance docstring
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantics_core.py` - the same on the
  live-extracted certificate
- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py` - `BIMODAL_LOGIC_COMMIT`

**Verification**:
- Run `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantics_core.py -v`
  and confirm the new assertions ran (not skipped) and passed.
- The pinned commit matches `git -C ~/Projects/BimodalLogic rev-parse HEAD` at the time the suite
  was run, and the dirty-tree caveat is present or provably unnecessary.

---

### Phase 4: Doc corrections — the narrower true claim only [NOT STARTED]

**Goal**: the three doc sites state what is now true (a `countermodel` from the current binary
carries a constructed entailment; the wire is canonical-bytes-only) without asserting the joint
trust-base demotion that has not landed.

**Tasks**:
- [ ] `docs/ADEQUACY.md` §6.1: add the canonical-bytes requirement to the wire contract — the
      consuming parser accepts canonical bytes only (compact separators, no interior whitespace;
      trailing whitespace skipped), key order is fixed, `ensure_ascii=False`, and this repository's
      single serializer is `certificate.canonical_wire_bytes`. Add `"acceptance"` to the documented
      output shapes, on `countermodel` only, with the absent-reads-as-`"decided"` rule.
- [ ] `docs/ADEQUACY.md` §6.2: **add to**, do not replace, the existing sentence. The "four
      `Decidable` instances returned true" reading remains exactly right for the Python re-checker
      and for a `"decided"` verdict; the new sentence says that where the binary reports
      `"acceptance":"entailment"`, Lean constructed the paper-countermodel existence term for that
      certificate rather than printing a verdict. Keep the never-a-validity-claim and
      error-versus-rejected language untouched.
- [ ] `docs/TRUST_PIPELINE.md` "What remains" → split the single row **"Consume a proof-producing
      checker; verify the parse"** into two rows, one per axis, and mark the proof-producing half
      done in the test tier with the echo half still open. Leave "The **re-checker
      implementation**" in the "In it" trust-base list, with a one-clause note that the test tier
      now observes entailment-grade acceptance but the live path (`semantic/model.py`) still
      depends on the Python re-checker alone.
- [ ] `docs/A2_GAP.md` route (f): update the "Cost / status" cell — the first half of (f) has
      landed and is consumed in the differential tier; the echo half remains. Do not change what
      route (f) *buys*; that is unchanged.
- [ ] **Prohibition, enforced by this phase's verification**: do not write "fast pre-filter", "no
      longer in the trust base", or any equivalent demotion of the Python re-checker. That
      sentence belongs to Phase 6 alone.

**Timing**: 1.25 hours

**Depends on**: 3

**Verification Tier**: prose

**Scope Hypothesis**: four doc sites need correction (report F5): `ADEQUACY.md` §6.1 and §6.2,
`TRUST_PIPELINE.md`'s trust-base list plus its "What remains" row, `A2_GAP.md` route (f). F5 also
names `semantic/model.py`'s module docstring as *accurate as written* and deliberately unchanged —
confirm that judgment still holds by reading lines ~16-25 before closing the phase, and say so.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` - §6.1 canonical bytes and
  `"acceptance"`; §6.2 the added sentence
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` - the split row; the
  trust-base note
- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` - route (f) status cell

**Verification**:
- `grep -rni "pre-filter\|no longer in the trust base" code/src/model_checker/theory_lib/bimodal/docs/`
  returns nothing. This is the phase's prohibition check, run as a command rather than trusted to
  review.
- Diff read-through confirming every changed hunk is prose, and that §6.2's original sentence
  survives rather than being replaced.
- Every cross-reference added (section numbers, file paths, the `canonical_wire_bytes` symbol
  name) resolves.

---

### Phase 5: Parse-echo verification (axis 2) — gated [NOT STARTED]

**Goal**: the Lean side's echo of what it parsed is compared bytewise against the bytes this
repository sent, with a mismatch reported as a **protocol error**, not a rejection. This phase
opens with an admission gate because its interface is uncommitted upstream as of this plan (M2).

**Tasks**:
- [ ] **Admission gate, first task, recorded before any edit.** Run
      `git -C ~/Projects/BimodalLogic log --oneline -1` and
      `git -C ~/Projects/BimodalLogic status --porcelain`, then send one canonical fixture through
      the binary and inspect the verdict. The gate **passes** when both hold: (a) an `"echo"` key
      is present on a `countermodel` verdict, and (b) the echo interface is **committed** —
      `git -C ~/Projects/BimodalLogic log -1 --format=%s -- BimodalTools/CertificateImport.lean`
      names the phase-9 work and `BimodalTools/README.md` no longer carries the "jointly gated, and
      has not landed yet" paragraph (`grep -n "jointly gated"` on the committed file returns
      nothing).
- [ ] **On gate failure**: close this phase as `[COMPLETED WITH EXCLUSIONS]` with a
      `#### Reasoned Exclusions` record whose Evidence column quotes the gate commands' actual
      output, and stop. Do not implement against an uncommitted upstream interface, and do not
      proceed to Phase 6.
- [ ] **On gate pass**: capture the exact bytes sent. `run_check_certificate` currently discards
      them; have it return, or expose, the canonical string it wrote to stdin so a caller can
      compare. Keep the existing return shape working for the three current consumers.
- [ ] Add the comparison: on every verdict carrying an `"echo"`, assert `echo == sent` bytewise.
      Per M3 the echo is a canonical **reprint** of the parsed certificate, so this holds only
      because this repository already emits canonical key order — state that in the assertion
      message, so a future key-order regression explains itself instead of looking like a Lean
      defect. Compare modulo surrounding whitespace only (the producer's trailing newline), never
      modulo interior whitespace.
- [ ] Classify a mismatch as a **protocol error**: a distinct, loudly-named failure in the same
      vocabulary Phase 2 established (`PROTOCOL_FAILURE`-grade), explicitly not a `rejected`-shaped
      outcome and explicitly not a fixture-corpus disagreement. The task description's discipline
      is the contract here: a mismatch means the two sides are talking about different
      certificates, which is a protocol failure by definition.
- [ ] Assert the negative half too: an `error` verdict carries **no** `"echo"` (M3), so the
      comparison is correctly skipped rather than silently passing on a missing field. A missing
      `"echo"` on a `countermodel` or `rejected` verdict is itself a protocol failure, not a pass.
- [ ] Run the comparison across the whole fixture corpus and the live-extracted certificate in
      `test_semantics_core.py`, not the corpus alone — the live path is where a key-order or
      escaping defect in this repository's own exporter would actually appear.

**Timing**: 1.5 hours

**Depends on**: 2, 3

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: this phase asserts that `echo == canonical_wire_bytes(payload)` holds on all
four corpus fixtures (measured: it does, M3) and on the live-extracted certificate (**not**
measured — the live exporter's `bx` iteration order and atom-name escaping are untested against the
canonical printer). Confirm the live case explicitly; if it diverges, that is a finding about this
repository's exporter, not a reason to weaken the comparison to a structural one.

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py` - expose the bytes sent;
  protocol-error classification for a mismatch
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py` -
  the corpus-wide echo comparison and the negative (`error` has no echo) assertion
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantics_core.py` - the
  live-extracted-certificate echo comparison

**Verification**:
- The complete gate set: `PYTHONPATH=code/src pytest code/tests/ -q` and
  `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` both green.
- The echo comparison ran on all four fixtures plus the live certificate (assert-count or `-v`
  output confirms it, not inference).
- Perturbing the sent bytes locally (e.g. a reordered `bx` entry) makes the comparison fail with
  the protocol-error message, and the message says "protocol" rather than "rejected"; restore
  afterwards.

---

### Phase 6: The joint trust-base claim — gated on Phase 5 executing [NOT STARTED]

**Goal**: once, and only once, both axes are consumed, record in the docs that the Python
re-checker's role in the test tier has become a fast pre-filter rather than part of what the
verdict rests on.

**Tasks**:
- [ ] **Admission check**: proceed only if Phase 5 closed `[COMPLETED]`. If Phase 5 closed
      `[COMPLETED WITH EXCLUSIONS]`, close this phase the same way, citing Phase 5's own gate
      evidence, and write nothing.
- [ ] `docs/TRUST_PIPELINE.md`: state the demotion precisely and with its scope attached — the
      **differential test tier**'s verdict no longer rests on the Python re-checker (Lean
      constructs the entailment, and the echo pins that it did so for the certificate actually
      sent), while the **live path** (`semantic/model.py`) still does, because it never calls the
      binary. Do not write an unqualified demotion; the qualification is the honest part.
- [ ] `docs/ADEQUACY.md` §6.2: add the corresponding sentence, and name the theorem the guarantee
      rests on (`print_parse_canonical`, per BimodalLogic's committed `CertificateImport.lean`
      header) rather than asserting the guarantee bare.
- [ ] `docs/A2_GAP.md` route (f): mark both halves landed and consumed, leaving "removes the
      re-checker — not the encoder — from the trust base" scoped to the tier that actually calls
      the binary.
- [ ] Re-read BimodalLogic's committed `BimodalTools/README.md` certificate-protocol section
      first and quote its post-phase-9 wording rather than this plan's paraphrase — the producing
      side's contract prose is authoritative for what the joint claim licenses.

**Timing**: 0.75 hours

**Depends on**: 5

**Verification Tier**: prose

**Files to modify**:
- `code/src/model_checker/theory_lib/bimodal/docs/TRUST_PIPELINE.md` - the scoped demotion
- `code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md` - §6.2's joint sentence
- `code/src/model_checker/theory_lib/bimodal/docs/A2_GAP.md` - route (f), both halves

**Verification**:
- Every demotion sentence carries its scope (test tier versus live path) — checked by reading each
  hunk, since an unqualified sentence is the specific defect this phase risks.
- `grep -n "print_parse_canonical" code/src/model_checker/theory_lib/bimodal/docs/ADEQUACY.md`
  finds the named theorem.
- Diff read-through confirming prose-only changes.

## Testing & Validation

- [ ] `PYTHONPATH=code/src python3 -c "from model_checker.theory_lib.bimodal.tests import _lean_check as lc; print(repr(lc.SKIP_REASON))"`
      prints `None` with the checkout present — the differential tier is alive, not skipping.
- [ ] `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` green, with
      the differential tests **run** rather than skipped.
- [ ] `BIMODAL_LOGIC_PATH=/nonexistent PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -q`
      skips cleanly with zero failures (environment absence must still be a skip).
- [ ] `PYTHONPATH=code/src pytest code/tests/ -q` green (no regression outside the theory).
- [ ] `grep -rni "pre-filter\|no longer in the trust base" code/src/model_checker/theory_lib/bimodal/docs/`
      returns nothing unless Phase 6 executed.
- [ ] `grep -rn "json.dumps" code/src/model_checker/theory_lib/bimodal/` shows no remaining site
      that serializes a payload for the Lean binary without `canonical_wire_bytes`.
- [ ] No change to `back`, `mid`, `fwd`, `bx`, `lassos` or `target` as input-schema keys —
      confirmed by reading the diff of `semantic/certificate.py` and `semantic/formula.py`.

## Artifacts & Outputs

- `code/src/model_checker/theory_lib/bimodal/semantic/certificate.py` — `canonical_wire_bytes`
- `code/src/model_checker/theory_lib/bimodal/tests/_lean_check.py` — canonical serialization,
  environment-versus-protocol failure split, refreshed provenance pin, (Phase 5) exposed sent bytes
- `code/src/model_checker/theory_lib/bimodal/tests/integration/test_certificate_lean_agreement.py` —
  `acceptance` assertions, protocol-failure assertion, (Phase 5) echo comparison
- `code/src/model_checker/theory_lib/bimodal/tests/unit/test_semantics_core.py` — the same on a
  live-extracted certificate
- `code/src/model_checker/theory_lib/bimodal/tests/unit/` — canonical-form unit test
- `code/src/model_checker/theory_lib/bimodal/docs/{ADEQUACY,TRUST_PIPELINE,A2_GAP}.md` — corrected
  claims
- `specs/197_harden_certificate_wire_proof_carrying/summaries/01_*-summary.md` — implementation
  summary, recording Phase 5's gate measurement verbatim whichever branch it took

## Rollback/Contingency

Every phase is independently revertible and each closes with its own commit, so rollback is
per-phase `git revert` of that phase's commit rather than a working-tree discard. Phase 1 is the
only phase whose revert has a visible consequence — the differential tier returns to silently
skipping — so if Phase 1 must be reverted, that fact goes in the summary rather than passing as a
clean revert.

If a phase must be abandoned mid-edit with uncommitted work present, take a durable, non-reverting
checkpoint first: `bash .claude/scripts/git-snapshot.sh 197 --no-revert`. A genuine reverting
rollback (discarding the working tree) follows `context/contracts/recovery.md`'s rollback rung,
including its out-of-scope override flag — and note that sibling tasks 207 and 208 may hold
uncommitted work in this same tree this cycle, so a whole-tree revert is the wrong instrument here
regardless.

Phases 5 and 6 have contingency built in as their admission gates: a failed gate is a recorded
`[COMPLETED WITH EXCLUSIONS]` outcome with evidence, not a rollback.
