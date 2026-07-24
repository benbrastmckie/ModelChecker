# Preserved TODO Items from Deleted Per-Theory TODO.md Files

Phase 5 (Cruft Sweep) deletes `theory_lib/exclusion/TODO.md` and `theory_lib/logos/TODO.md`
from the package tree — both shipped in the wheel, which per-theory scratch TODO files should
not. This note preserves their live (unchecked) items for Phase 26 (`Update ROADMAP.md`) to fold
into `specs/ROADMAP.md` content, per Phase 5's task list.

## From `theory_lib/exclusion/TODO.md` (research-adjacent, mostly paper-writing scope)

- Computational complexity of Fine's imposition relation: compare model sizes across theories
  for varying `N`, find where the model_checker taps out for each, demo running both theories in
  parallel.
- Manicure examples: go through `examples.py` finding best/worst models per example, compare
  with bilateral semantics.
- `model_checker` tooling: `model_lib` item still open (iterator and parallel-theory comparison
  are already checked off `[x]`).
- Paper draft: outline and draft sections (ideological simplicity motivating unilateral
  negation, negation-semantics complexity, logic weakness, computability as a further objective
  measure, arity/primitive-order bottlenecks).

## From `theory_lib/logos/TODO.md`

- **Version tracking**: add `__version__` and `__model_checker_version__` (via
  `get_model_checker_version()`) to `logos/__init__.py`, matching other theories' convention.
- **Jupyter notebooks**: logos currently has none; consider adding theory-level and
  per-subtheory notebooks (optional per THEORY_ARCHITECTURE.md's `notebooks/` policy).
- **Clean up**: review all `logos/` documentation for redundancy and clarity.
- A "Buffer Diagnostics" section in the original file was stale linter output pasted from an
  editor buffer (referencing `code/run_update.py` and `code/tests/test_package.py`, both already
  removed or out of scope) — not a real TODO item, not carried forward.

Full original content is recoverable from git history (`git log --all --full-history -- 'code/src/model_checker/theory_lib/exclusion/TODO.md' 'code/src/model_checker/theory_lib/logos/TODO.md'`) if more context is needed.
