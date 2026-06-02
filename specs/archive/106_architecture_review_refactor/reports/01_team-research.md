# Research Report: Task #106

**Task**: Architecture review of bimodal refactor plan (tasks 99-105)
**Date**: 2026-05-30
**Mode**: Team Research (4 teammates)

## Summary

The team research identified significant architectural issues in the original 7-task plan that require restructuring. The revised plan drops task 99 (absorbed by this review), tightens scoping on all remaining tasks, and resolves critical blind spots: hard logos imports that crash on deletion, no existing programmatic pipeline path, a G/H operator mismatch between ModelChecker and BimodalLogic, and the package name being constrained to `bmlogic-oracle` by BimodalHarness.

## Key Findings

### Primary Approach (from Teammate A)

**Task decomposition issues:**
1. **Merge tasks 99 and 100** — the audit is just the research phase of the strip task. A separate handoff creates unnecessary overhead since task 100's implementer must re-verify everything anyway.
2. **Task 103 conflates two concerns** — countermodel serialization (data transformation) and OracleProvider protocol (pipeline orchestration) are architecturally distinct.
3. **Task 104 has a dangerous dependency** — cleaning up builder/output internals while OracleProvider is being built against them risks rework. Task 104 must come AFTER OracleProvider is working.
4. **Formula translation harder than scoped** — `Sentence.__init__()` only accepts infix strings. A programmatic `Sentence.from_prefix()` constructor must be built. The `→` operator is defined (not primitive) via `DefinedOperator`, but this is handled naturally by `derive_type()`.

### Alternative Approaches (from Teammate B)

**Interface design analysis:**
1. **Operator mapping is clean** — all 6 JSON tags map directly to existing operators. Use canonical internal names and let `derive_type` handle defined operators.
2. **Formula translation should bypass infix parsing** — build `json_to_prefix()` → `Sentence.from_prefix()` to avoid fragile string round-trips.
3. **trueAtoms/falseAtoms not directly exposed** by `extract_model_elements()` — requires evaluating atoms at the evaluation point after solving, similar to what `print_evaluation()` does.
4. **Only "Base" frame class exists** — protocol confirms this is expected ("Only Base is implementable today").
5. **Package must be `bmlogic-oracle`** — BimodalHarness pyproject.toml declares `bmlogic-oracle>=0.1.0`.
6. **Drop reverse formula translation** — OracleProvider only receives JSON, returns the original formula_json in output. No internal→JSON needed.
7. **MockOracleProvider in BimodalHarness** is a complete reference showing properties can be plain class attributes.

### Gaps and Shortcomings (from Critic)

**Critical gaps in the plan:**
1. **Hard logos imports will crash** — `theory_lib/__init__.py:52` has unconditional `from model_checker.theory_lib import logos`, `builder/example.py:34` has `from ..theory_lib.logos import semantic`. Deleting logos/ without fixing these crashes the entire package.
2. **Builder has logos-specific branching** — `builder/runner.py:82,206` checks `if 'Logos' in semantics_class.__name__` for different init signatures.
3. **No test migration task** — bimodal tests are inside source tree (`theory_lib/bimodal/tests/`), top-level `code/tests/` has logos-specific tests that will break.
4. **iterate/ module likely unnecessary** — OracleProvider needs one countermodel, not iteration. NetworkX dependency can be dropped.
5. **pyproject.toml needs major overhaul** — name, description, dependencies, entry points, classifiers, testpaths all need changing.
6. **No existing programmatic pipeline** — current code starts from files on disk. No code path takes a formula object and returns a result programmatically.
7. **Z3 context isolation** — designed for CLI batch execution, not repeated API calls.
8. **Missing version pinning** against BimodalHarness/BimodalLogic semantics_version.

### Strategic Horizons (from Horizons)

**Long-term alignment:**
1. **G/H operator mismatch** — BimodalLogic derives G/H from U/S (`G(φ) = ¬F(¬φ)` where `F(φ) = U(φ,⊤)`), but ModelChecker has them as independent primitive operators. The 6-tag JSON has no G/H tags. Task 102 must verify semantic equivalence.
2. **StructuredCountermodel from the start** — the mapping from `extract_model_elements()` is natural. Deferring means rework later. Richer countermodels provide better training signal.
3. **Go fully bimodal-only** — no theory registry, no extensibility. Simplicity increases correctness confidence.
4. **Keep thin CLI** — useful for standalone countermodel checking during development without requiring the full harness.
5. **Cross-signal consistency** — the harness's `CrossSignalConsistencyChecker` catches oracle/verifier conflicts, making correctness paramount.
6. **semantics_version pinning** — tracks which BimodalLogic semantics version the oracle was validated against.

## Synthesis

### Conflicts Resolved

1. **Split vs. merge task 103**: Teammate A recommends splitting (serialization vs protocol). Teammate B recommends keeping merged since they're tightly coupled in `find_countermodel()`. **Resolution**: Keep merged — the serialization is 20 lines of code embedded in the pipeline, not an independent module. But ensure the OracleProvider task explicitly scopes the programmatic pipeline (Teammate C's concern).

2. **Task 104 ordering**: Teammate A says after 103, Teammate B says shrink scope. **Resolution**: Both — shrink scope AND make it depend on 103. The public API IS the OracleProvider; task 104 is just dead-code cleanup and thin CLI.

3. **Formula translation approach**: Teammate C lists 3 options (JSON→infix, JSON→Sentence-direct, JSON→Z3-direct). Teammate B recommends JSON→prefix→Sentence.from_prefix(). **Resolution**: Teammate B's approach — it reuses the existing operator machinery (derive_type, update_types) while bypassing the fragile infix parser.

### Gaps Identified

1. **G/H semantic equivalence verification** — must be explicitly verified in task 102, not assumed
2. **Z3 context isolation** — must be part of task 103's scope
3. **Test cleanup** — must be part of task 100, not deferred to 105
4. **semantics_version contract** — fold into task 103 (OracleProvider properties)

### Revised Task Plan

**Drop task 99** (absorbed by this review). Revise tasks 100-105:

---

#### Task 100: Strip non-bimodal code and fix coupling (medium)
**Dependencies**: none

Strip all non-bimodal theories and fix hard coupling points. Research phase: trace all import chains and identify breakpoints. Implementation:
- Fix hard logos imports: `theory_lib/__init__.py:52`, `builder/example.py:34`
- Remove logos-specific branching: `builder/runner.py:82,206`
- Delete: `theory_lib/logos/` (and subtheories exclusion, imposition), `jupyter/`, notebook output templates
- Collapse `theory_lib/__init__.py` to direct bimodal-only export (no registry, no lazy loading)
- Remove `iterate/` module and `networkx` dependency (OracleProvider needs one countermodel, not iteration)
- Clean top-level `code/tests/` of logos-specific tests; ensure bimodal tests at `theory_lib/bimodal/tests/` still pass
- Gate: `PYTHONPATH=code/src pytest code/src/model_checker/theory_lib/bimodal/tests/ -v` passes (43 examples)

---

#### Task 101: Restructure as bmlogic-oracle pip package (medium)
**Dependencies**: 100

Restructure the codebase as pip-installable `bmlogic-oracle` package. Major pyproject.toml overhaul:
- Package name: `bmlogic-oracle` (import as `bmlogic_oracle`). BimodalHarness already declares `bmlogic-oracle>=0.1.0` as optional dependency.
- Description, classifiers, keywords updated for bimodal-only oracle
- Dependencies: `z3-solver>=4.8.0` as core dep. Remove networkx, jupyter, cvc5, matplotlib.
- Python version: `>=3.10` (protocol uses modern type syntax)
- Entry point stub: `[project.entry-points.'bimodal_harness.oracle_providers'] z3_base = "bmlogic_oracle.provider:Z3OracleProvider"` (class created in task 103)
- Update package directory mapping if renaming the import path
- Fix testpaths in pytest config
- Verify: `pip install -e .` succeeds in fresh venv

---

#### Task 102: Formula JSON translation layer (medium)
**Dependencies**: 100

Implement one-directional JSON→internal formula translation with semantic equivalence verification.
- Create `json_to_prefix(formula_json)` function mapping 6 JSON tags to internal prefix-list format: atom→variable, bot→`\bot`, imp→`\rightarrow`, box→`\Box`, untl→`U`, snce→`S`
- Create `Sentence.from_prefix(prefix_list, operators)` classmethod that constructs Sentence objects programmatically, bypassing the infix parser entirely. Must call `update_types()` / `update_objects()` so defined operators (→, ◇, etc.) expand via `derive_type()`.
- **Critical: G/H equivalence verification** — BimodalLogic derives G from U and H from S. The 6-tag JSON has no G/H tags. Verify that `G(φ) ≡ ¬U(¬φ,⊤)` and `H(φ) ≡ ¬S(¬φ,⊤)` produce identical Z3 constraints as the direct `FutureOperator`/`PastOperator` implementations. This is a soundness requirement — divergence means false training signals.
- Drop reverse direction (sentence→JSON) — OracleProvider only receives JSON; countermodel output echoes the original formula_json.
- Tests: round-trip prefix construction, all 6 tag types, nested formulas, G/H equivalence check.

---

#### Task 103: OracleProvider implementation with programmatic pipeline (large)
**Dependencies**: 101, 102

Implement the OracleProvider protocol class with a new programmatic solving pipeline (current code starts from files on disk — no programmatic path exists).
- **New pipeline**: `formula_json → json_to_prefix() → Sentence.from_prefix() → BimodalSemantics(N,M) → Syntax(operators, [sentence]) → ModelConstraints → BimodalStructure → Z3 solve → extract model → serialize`
- **OracleProvider properties**: `provider_id="bmlogic_z3_base_v1"`, `provider_version` (semver), `semantics_version` (pinned to BimodalLogic), `supported_frame_classes=frozenset({"Base"})`, `capabilities` dict (encoding, max bounds, timeout, backend)
- **find_countermodel(formula_json, frame_class, timeout_ms)**: Implements the full pipeline. Returns `None` on UNSAT/timeout/unsupported frame_class.
- **Countermodel serialization**: Both `SimpleCountermodel` (trueAtoms/falseAtoms from evaluating atoms at eval point) and `StructuredCountermodel` (world_histories, task_relation, truth_valuation from `extract_model_elements()`). Implement structured from the start — the mapping is natural and provides richer training signal.
- **validate_self(spot_check_formulas)**: Must find countermodels for all provided known-invalid formulas.
- **Z3 context isolation**: Clean Z3 state between `find_countermodel()` calls. Use `_reset_global_state()` or fresh solver instances per call. Address memory management for repeated instantiation.
- **semantics_version contract**: Pin to specific BimodalLogic semantics version, document what constitutes a breaking change.
- Finalize entry point in pyproject.toml pointing to the implemented class.

---

#### Task 104: Dead-code cleanup and thin CLI (small)
**Dependencies**: 103

With OracleProvider working as the primary public interface, remove dead code and add a thin CLI.
- Remove unused builder components: project scaffolding, multi-theory comparison, theory template generation
- Simplify output/: remove interactive prompts, notebook templates, progress bars (OracleProvider returns dicts, not formatted output)
- Simplify settings/: remove file-based settings parsing not used by programmatic pipeline
- Remove logos-specific branching remnants in builder/runner.py
- Add thin CLI: `bmlogic-oracle check '<formula_json>'` for standalone countermodel checking
- Do NOT change any code that OracleProvider depends on — only remove unreachable code.

---

#### Task 105: Integration testing and validation (medium)
**Dependencies**: 103, 104

End-to-end testing against the OracleProvider protocol and BimodalHarness compatibility.
- **Protocol compliance**: Verify all 5 properties, both methods, return format matches SimpleCountermodel/StructuredCountermodel schemas
- **Countermodel correctness**: Regression test against the existing 43-example bimodal test suite — refactored package must produce identical valid/invalid classifications
- **Cross-signal scenarios**: Use BimodalHarness's `SPOT_CHECK_FORMULAS` (10 known-invalid formulas from `_mock.py`) as ground truth for validate_self
- **Edge cases**: timeout handling (formula that exceeds timeout_ms), unsupported frame_class ("Dense"→None), malformed formula JSON, empty formula
- **Entry-point discovery**: Verify `pip install bmlogic-oracle` followed by `OracleRegistry.discover()` finds the provider
- **Z3 isolation**: Run find_countermodel() 100+ times in sequence, verify no state leakage or memory growth
- **G/H equivalence regression**: Formulas using derived G/H must produce countermodels equivalent to direct G/H encoding

---

### Revised Dependency Graph

```
100 (strip + fix coupling)
 ├── 101 (bmlogic-oracle package) ──┐
 └── 102 (JSON translation + G/H) ─┼── 103 (OracleProvider + pipeline) → 104 (cleanup + CLI) → 105 (testing)
                                    │
                                    └── (101 provides package structure, 102 provides formula adapter)
```

Tasks 101 and 102 can run in parallel after 100. Task 103 is the convergence point. Task 104 is now small (just dead-code removal + thin CLI). Task 105 is the final gate.

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Task Decomposition | completed | high |
| B | Interface Design | completed | high |
| C | Gaps & Blind Spots | completed | high |
| D | Strategic Horizons | completed | high |

## References

- BimodalHarness OracleProvider protocol: `/home/benjamin/Projects/BimodalHarness/src/bimodal_harness/oracle/protocol.py`
- BimodalHarness mock oracle: `/home/benjamin/Projects/BimodalHarness/src/bimodal_harness/oracle/_mock.py`
- BimodalHarness pyproject.toml: declares `bmlogic-oracle>=0.1.0`
- ModelChecker bimodal theory: `code/src/model_checker/theory_lib/bimodal/`
- ModelChecker hard logos imports: `theory_lib/__init__.py:52`, `builder/example.py:34`
- BimodalLogic G/H derivation: `G(φ) = ¬U(¬φ,⊤)`, `H(φ) = ¬S(¬φ,⊤)`
- Technical memo: `/home/benjamin/Projects/Logos/Vision/shared/strategy/01-overview/03-technical_memo.typ`
