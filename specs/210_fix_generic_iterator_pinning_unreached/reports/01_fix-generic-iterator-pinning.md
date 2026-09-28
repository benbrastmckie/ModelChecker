# Research Report: Fix generic iterator pinning never reaching the rebuilt model's solve

- **Task**: 210 - Fix generic iterator pinning never reaching the rebuilt model's solve for logos, exclusion and imposition
- **Started**: 2026-09-28T00:00:00Z
- **Completed**: 2026-09-28T00:00:00Z
- **Effort**: ~2 hours
- **Dependencies**: None (follow-up to finding F4 in a prior task's `all_constraints` report)
- **Sources/Inputs**:
  - `code/src/model_checker/iterate/models.py` (`ModelBuilder.build_new_model_structure`)
  - `code/src/model_checker/models/constraints.py` (`ModelConstraints.all_constraints` property)
  - `code/src/model_checker/models/structure.py` (`_setup_solver`)
  - `code/src/model_checker/iterate/core.py` (`BaseModelIterator._pin_theory_specific_values`, main loop)
  - `code/src/model_checker/theory_lib/bimodal/iterate.py` (`_pin_theory_specific_values`, `_ensure_frame_constraints_in_search_solver`)
  - `code/src/model_checker/theory_lib/bimodal/tests/integration/test_iterate.py` (`TestAllConstraintsReflectsCertificateAfterSolve`, `TestPinTheorySpecificValues`, `_real_build_example`)
  - `code/src/model_checker/theory_lib/{logos,exclusion,imposition}/examples.py` and `tests/integration/test_iterate.py`
  - `code/src/model_checker/iterate/tests/integration/test_models.py`, `iterate/tests/unit/test_models_edge_cases.py`
  - `specs/207_fix_stale_all_constraints_snapshot/reports/01_fix-stale-all-constraints.md` (finding F4)
  - Three live, non-mocked probe scripts written for this task (logos, exclusion, imposition), executed directly against a real `BuildExample`/`iterate_example`/Z3 solve
- **Artifacts**: `specs/210_fix_generic_iterator_pinning_unreached/reports/01_fix-generic-iterator-pinning.md`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- The upstream task's own fix (`ModelConstraints.all_constraints` becoming a read-only computed
  property) landed exactly as described: `iterate/models.py` no longer assigns to
  `all_constraints`, and the dead-write symptom that originally surfaced this bug is gone. The
  *underlying* pin-propagation gap it uncovered (finding F4) is untouched and still live.
- **Confirmed empirically for all three affected theories** (logos, exclusion, imposition), using
  a decisive live-probe method (not the now-obsolete `all_constraints`-length heuristic F4 used):
  every rebuilt model's actual solved `is_world`/`possible`/`verify`/`falsify` values diverge from
  the specific candidate Z3 model the generic pinning loop computed pins for. This is not
  occasional — it reproduced on essentially every intercepted rebuild across all three theories.
- **Root cause, precisely located**: `iterate/models.py`'s generic pinning loop
  (`build_new_model_structure`, lines ~90-141) asserts every pin only into a local `temp_solver`
  that nothing ever calls `.check()`/reads assertions from again. `models/structure.py`'s
  `_setup_solver` — the code that actually builds the solver used for the real solve — reads
  `model_constraints.frame_constraints`/`.model_constraints`/`.premise_constraints`/
  `.conclusion_constraints` directly, never `temp_solver` and never `all_constraints`. Bimodal is
  unaffected only because its `_pin_theory_specific_values` override independently appends its own
  pins directly into `semantics.frame_constraints` (a live list `_setup_solver` reads); logos,
  exclusion, and imposition have no such override, so their generic-loop pins have no path into
  the solve at all.
- **Decision**: a `_pin_theory_specific_values` *default* that replays `temp_solver`'s assertions
  is the wrong mechanism — by the time that hook runs, `temp_solver` already contains a *copy* of
  every base constraint (added at line 93) in addition to the pins, so replaying it would silently
  duplicate every existing frame/model/premise/conclusion constraint. The correct, minimal-diff
  fix is to append each pin literal directly into `model_constraints.frame_constraints` inline in
  the generic loop, at the exact point each pin is computed and added to `temp_solver` — the same
  pattern bimodal's own hook already establishes, applied one call site up. No change to
  `_pin_theory_specific_values`'s signature or call site is required.
- **Regression coverage recommendation**: add a shared-engine, live (non-mocked) regression test
  in `iterate/tests/integration/test_models.py`, parametrized over logos/exclusion/imposition,
  asserting that every rebuild's actual solved predicate values equal the candidate model's
  intended values (the same invariant this report's probes checked) — not theory-by-theory
  duplication of `TestAllConstraintsReflectsCertificateAfterSolve`, since that test's own subject
  (`all_constraints`) is not where this defect lives and checking it would not catch a regression
  here.
- A second, small and unrelated docstring fix is confirmed necessary (named in the dispatch): the
  bimodal `_ensure_frame_constraints_in_search_solver` docstring asserts, in the present tense,
  that `all_constraints` "permanently misses" the certificate encoding — no longer accurate now
  that `all_constraints` is a live computed property. The method's own defensive design (reading
  the four component lists directly, for the separate `stored_solver` timing bug) remains correct
  and is not affected by this wording fix.

## Context & Scope

This task is the named follow-up to finding F4 in a prior report on the `all_constraints`
snapshot bug: that task's fix (turning `all_constraints` into a read-only computed property)
closed the display/read-side staleness bug for all four theories, but explicitly left generic
iterator pinning for logos/exclusion/imposition unfixed, since fixing it changes iteration
*results* for those three theories and needed its own reproduction and scope. This report:

1. Confirms the same live-probe defect independently for exclusion and imposition (not just
   assumed from the logos case).
2. Decides the fix mechanism (a `_pin_theory_specific_values` default vs. a different mechanism).
3. Recommends regression coverage for iteration correctness.
4. Confirms and specifies the small, separately-named bimodal docstring fix.

This is research only — no code changes are made here; recommendations below are for the planning
phase, which must also schedule the full four-theory CI gate since this changes iteration results
for logos, exclusion, and imposition.

## Findings

### F1 — The write-side symptom is gone; the pin-propagation gap is not

`code/src/model_checker/iterate/models.py:150-159` now contains an explicit comment (added by the
prior task's fix) documenting exactly this state: `all_constraints` cannot be assigned to anymore
(no setter), the old `model_constraints.all_constraints = list(temp_solver.assertions())` line
has been removed outright, and the comment states plainly that this is a pre-existing, *not
fixed here* consequence tracked for its own follow-up — i.e. this task. Nothing about the pinning
mechanism itself changed.

### F2 — Root cause confirmed by direct code reading

- `build_new_model_structure` (`iterate/models.py:41`) builds `temp_solver = z3.Solver()`
  (line 90), copies `model_constraints.all_constraints` into it (line 93), then asserts every
  `is_world`/`possible`/`verify`/`falsify` pin into it (lines 100-141), then calls
  `self.iterator._pin_theory_specific_values(temp_solver, z3_model, model_constraints)` (line 149,
  only when an iterator was injected) — and never calls `.check()` or reads any assertion back out
  of `temp_solver` again. `temp_solver` is entirely write-only from that point on.
- The actual solve happens later, when `model_structure_class(model_constraints, settings)` is
  constructed (line ~166), which eventually calls `models/structure.py`'s `_setup_solver`
  (`structure.py:162`). That method builds its own solver from
  `model_constraints.frame_constraints`, `.model_constraints`, `.premise_constraints`,
  `.conclusion_constraints` — four plain lists read directly, never `temp_solver`, never
  `all_constraints`.
- Bimodal is the only theory with a `_pin_theory_specific_values` override
  (`theory_lib/bimodal/iterate.py:190`), and its own docstring already documents, as a defensive
  fix for itself, that `temp_solver.add(pinned)` alone is not enough: it *also* appends every pin
  directly to `semantics.frame_constraints` (aliased to `model_constraints.frame_constraints`),
  because that is one of the four lists `_setup_solver` actually reads. Logos, exclusion, and
  imposition have no such override — their generic-loop pins reach only the dead `temp_solver`.

### F3 — Live confirmation for exclusion and imposition (not just logos)

Using a decisive method — not F4's `all_constraints`-length heuristic, which is now moot because
`all_constraints` is a live computed property that trivially equals the true four-list total for
every theory, by construction, whether or not pins reached the solve — this task ran three live,
non-mocked probes (real `BuildExample`, real `iterate_example`, real Z3 solves, no theory-internal
mocking). Method: monkeypatch `ModelBuilder.build_new_model_structure` to intercept its own
`(z3_model, returned_structure)` pair on every call, then independently evaluate
`is_world`/`possible`/`verify`/`falsify` at every state (and every sentence-letter atom) against
both the candidate `z3_model` the generic loop was asked to pin and the *actual* Z3 model the
rebuilt structure's own solve produced. If pinning worked, these must be identical at every state
— that is the definition of "pinned". Results:

- **logos** (`N=2`, `[] |- \neg A`, `iterate: 3`): 1876 intercepted rebuilds during the search;
  every single one showed at least one `is_world`/`verify` mismatch between the intended pin and
  the actual solved value (representative: `('verify', 0, False, True)`,
  `('is_world', 1, True, False)`). Consistent with, and a strictly stronger confirmation than,
  F4's original logos evidence.
- **exclusion** (`EX_CM_6`: `\neg\neg A \vdash A`, `N=3`, `iterate: 3`, `max_time=40`): 30
  intercepted rebuilds; every one showed 6-15 mismatches across `is_world`/`possible`/`verify`
  (e.g. `('is_world', 1, True, False)`, `('possible', 6, False, True)`).
- **imposition** (`IM_CM_0`: counterfactual antecedent strengthening, `N=4`, `iterate: 3`,
  `max_time=40`): 30 intercepted rebuilds; every one showed 31-44 mismatches across
  `is_world`/`possible` (e.g. `('possible', 0, False, True)`, `('is_world', 3, False, True)`).

This directly answers SCOPE item 1: the defect generalizes to exclusion and imposition, with the
same mechanism and comparable severity (dozens of unconstrained bits per rebuild, not an edge
case) — it is not an artifact specific to logos's example or settings.

Caveat: in this run, both exclusion and imposition ultimately settled on only 1-2 *accepted*
models within the probe's bounded `max_time` (many candidate rebuilds were tried and rejected as
isomorphic or re-tried by the search loop before a genuinely new one was accepted, or the search
simply timed out first) — this does not weaken the finding, since the defect is demonstrated at
the `build_new_model_structure` call level (every rebuild attempt, accepted or not, solves
unpinned), independent of how many final models the outer search loop happens to accept in a
bounded time.

### F4 — No downstream consistency check would catch a divergent rebuild

Confirmed by reading `iterate/core.py`'s main loop (`iterate_generator`, both the initial-search
and subsequent-search variants, ~lines 259-350 and ~561-620): after
`build_new_model_structure` returns, the only checks are `new_structure is None` and
`len(new_structure.z3_world_states) == 0`. Nothing compares the rebuilt structure's actual
`is_world`/`verify`/`falsify` values against the candidate `z3_model` the differencing search
found before accepting it as "model N". A divergent, silently unpinned rebuild is therefore never
detected or rejected today.

### F5 — Why a `_pin_theory_specific_values` default over `temp_solver` is the wrong mechanism

By the time any `_pin_theory_specific_values`-style hook is invoked, `temp_solver` already holds:
(a) a full copy of `model_constraints.all_constraints` (the base frame/model/premise/conclusion
constraints, added at `models.py:93`), plus (b) the generic loop's own pins. A default
implementation that iterates `temp_solver.assertions()` and appends them all into
`frame_constraints` would therefore **also re-append every base constraint a second time** —
harmless for satisfiability (duplicate ground literals are logically redundant) but doubles solver
size for every rebuild, and corrupts `_setup_solver`'s per-constraint tracking labels
(`constraint_dict`'s `"frame17"`-style IDs would silently alias content that already has a
different, earlier label under `"model3"` etc.), degrading unsat-core readability for no benefit.
This mechanism is confirmed unsound and should not be adopted.

### F6 — bimodal's own `_pin_theory_specific_values` already validates the correct mechanism

Bimodal's override (`theory_lib/bimodal/iterate.py:190-280`) does exactly the alternative
mechanism recommended below, and its own docstring documents having discovered and fixed this
identical class of bug for itself ("**Third discovered bug, fixed here defensively**" — pins
computed but discarded before reaching `_setup_solver`'s four lists) by appending each pin
directly to `semantics.frame_constraints` in addition to `temp_solver.add(...)` (kept only "for
interface parity with the existing unit tests ... which assert against `temp_solver` directly").
This is strong precedent that the fix belongs at the same conceptual layer — append into a live
component list at pin-computation time — just one call site earlier (the *generic* loop itself,
since logos/exclusion/imposition never reach a theory-specific hook for this content at all).

### F7 — The bimodal docstring correction named in the dispatch is confirmed necessary and narrow

`theory_lib/bimodal/iterate.py:113-157` (`_ensure_frame_constraints_in_search_solver`'s
docstring) states, in the present tense: `"ModelConstraints.__init__` computes `all_constraints =
frame_constraints + model_constraints + ...` via list concatenation (a *snapshot*, ...) ... so
`all_constraints` permanently misses every coherence/fulfilment/box-faithfulness/target
constraint"`. This was accurate when `all_constraints` was an eager, construction-time snapshot;
it is no longer accurate now that `all_constraints` is a read-only *computed* property
(`models/constraints.py`) recomputed on every access from the same four live lists — reading it
today, after `finalize_certificate()` has run, would in fact include the certificate encoding.
The method's underlying defensive design remains correct and necessary for an entirely separate,
still-live reason documented in the same docstring's earlier root-cause section (lines 113-134):
`models/structure.py`'s `solve()` leaves `stored_solver` pointing at a pristine, always-empty
solver (the `stored_solver`/`_setup_solver` reassignment timing bug), so
`ConstraintGenerator._create_persistent_solver`'s fallback path reads an empty solver regardless
of what `all_constraints` would return. Reading the four component lists directly is required to
populate `self.constraint_generator.solver` (a different, persistent solver object entirely) —
not a workaround for `all_constraints`'s former staleness. The fix is a wording correction only:
replace the present-tense "permanently misses" claim with an accurate past/updated statement, and
clarify (as this report's F7 does) that the four-list read is defensive for the `stored_solver`
bug, not for `all_constraints`'s now-resolved staleness. No behavior change.

## Decisions

1. **Fix mechanism**: append each pin literal into `model_constraints.frame_constraints` (the
   same live list `_setup_solver` reads, aliased from `semantics.frame_constraints`) inline in
   `iterate/models.py`'s existing generic loop, immediately alongside each existing
   `temp_solver.add(...)` call — for `is_world`, `possible`, `verify`, and `falsify` pins alike.
   Keep every existing `temp_solver.add(...)` call unchanged (parity with bimodal's own precedent
   and with any test asserting against `temp_solver` directly). This requires **no change** to
   `_pin_theory_specific_values`'s signature, call site, or contract — that hook remains exactly
   what it is today (a no-op default, overridden only by theories whose model content the generic
   loop cannot reach at all).
2. **Not adopted**: a `_pin_theory_specific_values` default that replays `temp_solver.assertions()`
   — rejected per F5 (would duplicate every base constraint a second time).
3. **List choice**: `frame_constraints`, not a new fifth list, for consistency with bimodal's own
   established precedent (which lumps its certificate/`sel` pins into the same list without
   splitting by predicate kind) and to avoid touching `_setup_solver`, display/print routines, or
   any of the several places in the codebase (including bimodal's own
   `_ensure_frame_constraints_in_search_solver`) that assume exactly four constraint-group lists.
   **Flagged for the planning phase to confirm**: this means a rebuilt model's printed "frame
   constraints" section (`print_constraints`/`--save`, `models/structure.py`'s
   `_get_relevant_constraints`) will, for model 2+ of logos/exclusion/imposition, additionally
   list these concrete pin literals under the "frame" label rather than under "model" — a
   display-only side effect, same severity class as the prior task's F6 finding, not a soundness
   concern, but worth an explicit call-out in the plan rather than an implicit consequence.
4. **Required companion edit**: the comment at `iterate/models.py:150-159` describing this as a
   "Consequence, NOT fixed here" gap must be updated (or removed) once the fix lands, to avoid
   leaving a stale claim in the code — the same class of documentation staleness the dispatch's
   "ALSO FIX" item names for the bimodal docstring.
5. **Bimodal docstring wording fix** (dispatch's "ALSO FIX" item): confirmed necessary and scoped
   exactly as the dispatch describes — see F7. This is a pure wording correction to
   `theory_lib/bimodal/iterate.py`'s `_ensure_frame_constraints_in_search_solver` docstring; no
   behavior change, and the method's four-list-read design is retained as-is.

## Recommendations

1. **Implement the F5/Decision-1 fix** in `iterate/models.py`'s generic pinning loop (lines
   ~100-141): for each `temp_solver.add(pin)` / `temp_solver.add(z3.Not(pin))` call already
   present, add a matching `model_constraints.frame_constraints.append(pin_or_negation)`. Update
   the stale "Consequence, NOT fixed here" comment (Decision 4) in the same edit.
2. **Regression coverage** (SCOPE item 3): add a shared-engine test class in
   `iterate/tests/integration/test_models.py` (not per-theory duplication of
   `TestAllConstraintsReflectsCertificateAfterSolve`, whose subject is a different attribute and
   would not catch a regression of this defect) that, for each of logos/exclusion/imposition:
   builds a real `BuildExample` with `iterate: 2` or `3` on a small, fast example (the same
   examples this report used — `[] |- \neg A`/N=2 for logos, `EX_CM_6`/N=3 for exclusion,
   `IM_CM_0`/N=4 for imposition, all with a bounded `max_time`), monkeypatches (or otherwise
   intercepts) `ModelBuilder.build_new_model_structure` to capture each `(candidate_z3_model,
   returned_structure)` pair, and asserts — for every state and every sentence-letter atom — that
   `is_world`/`possible`/`verify`/`falsify` evaluated on `returned_structure.z3_model` equals the
   same predicate evaluated on `candidate_z3_model`. This is the exact invariant this report's
   probes checked and is implementation-mechanism-agnostic (it would catch a regression regardless
   of which live list a future refactor chooses to append pins into). Also add at least one
   assertion mirroring bimodal's own `TestPinTheorySpecificValues` shape (pins present in
   `frame_constraints`, not just `temp_solver`) once Decision 1/3 fixes the specific list, for
   symmetry with the existing bimodal coverage.
3. **Run the full four-theory CI gate** once implemented, per the dispatch's own instruction,
   since this changes iteration *results* (which specific model 2+ gets reported) for logos,
   exclusion, and imposition — not merely their display. Use the two-invocation shape already
   established by the prior task's own report (`code/` root, `PYTHONPATH=src pytest tests/
   src/model_checker -m "not packaging and not performance and not unstable and not xdist_serial"
   -n 4 -q --timeout=300 --timeout-method=thread`, plus the `xdist_serial` marker run), plus each
   theory's own directory explicitly (`PYTHONPATH=code/src pytest
   code/src/model_checker/theory_lib/{logos,exclusion,imposition,bimodal}/ -v`).
4. **Apply the bimodal docstring wording fix** (F7/Decision 5) in the same implementation pass,
   since it is in the same file area and was explicitly named in this dispatch — a small, isolated
   text change with no functional impact, separable from Recommendation 1 if the planning phase
   prefers to sequence them as distinct commits.
5. **Expect iteration results to change** for existing passing examples with `iterate > 1` in
   logos/exclusion/imposition's `examples.py` files: some may now report different model 2+
   content (properly pinned, self-consistent with the difference/isomorphism search's own
   intent), and a few may newly detect models that were previously accepted as "isomorphic" or
   "different" based on an unpinned, coincidentally-satisfiable rebuild. The plan should treat any
   changed printed output in `examples.py`-driven tests as expected fallout to review, not
   necessarily a regression — but should not blanket-suppress such diffs without inspection.

## Risks & Mitigations

- **Risk**: appending pins into `frame_constraints` changes displayed constraint listings for
  rebuilt models (Decision 3's flagged side effect).
  **Mitigation**: named explicitly above; the planning phase should confirm this is acceptable
  (it is display-only, same class as a previously-accepted finding) or choose a separate list if
  display purity is a stated requirement, at a modestly larger diff.
- **Risk**: the four-theory CI gate surfaces genuine result changes in `examples.py`'s
  `expectation`-asserting tests once pinning is fixed.
  **Mitigation**: Recommendation 5 above; treat as expected, review each diff rather than
  reverting the fix or loosening the regression test.
- **Risk**: a reviewer conflates this task's fix with the prior task's `all_constraints` property
  change, since both live in the same file area and were surfaced by the same original
  investigation.
  **Mitigation**: F1 states plainly that the write-side symptom is already resolved and this task
  addresses a distinct, still-live gap; Decision 1 confirms no further change to `all_constraints`
  or its property is needed.

## Appendix

- Probe scripts (not part of the deliverable, written to the session scratchpad and run directly
  against `PYTHONPATH=code/src python <script>`): one per theory, using
  `unittest.mock.patch`-style monkeypatching of `ModelBuilder.build_new_model_structure` to
  intercept `(z3_model, returned_structure)` pairs, then comparing `is_world`/`possible`/
  `verify`/`falsify` predicate evaluations between the candidate and the actual rebuild's solve.
  Representative mismatch counts: logos 100% of 1876 rebuilds mismatched; exclusion 100% of 30
  rebuilds mismatched (6-15 mismatches each); imposition 100% of 30 rebuilds mismatched (31-44
  mismatches each).
- Every production site reading or writing the four constraint-group lists that a fix here must
  not disturb, by grep: `models/constraints.py` (definition + `all_constraints` property),
  `models/structure.py:162` (`_setup_solver`, the sole solve-determining reader),
  `iterate/models.py:93,100-141` (the generic pinning loop, this task's fix site),
  `theory_lib/bimodal/iterate.py:190-280` (`_pin_theory_specific_values`, the working precedent)
  and `:105-181` (`_ensure_frame_constraints_in_search_solver`, this task's docstring-fix site).
