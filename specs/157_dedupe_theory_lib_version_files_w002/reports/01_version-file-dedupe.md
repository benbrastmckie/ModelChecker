# Research: Deduplicating the four theory_lib VERSION files (W002)

## Summary

Four files — `code/src/model_checker/theory_lib/{bimodal,exclusion,imposition,logos}/VERSION` —
are byte-identical (`1.0.0\n`, md5 `47cd76e43f74bbc2e1baaf194d07e1fa` for all four), and
`check-wheel-contents` flags them as `W002: Wheel contains duplicate files` on a fresh
`python -m build`. This reproduces today, exactly as task 155 recorded, and the archived
rehearsal's "clean" claim (`specs/archive/125_release_engineering_and_pypi_rehearsal/`) no
longer holds — see "Verification: fresh build" below.

The four files are **structurally required** by the packaging contract test suite, the
theory-conformance suite, and project scaffolding (all three assert/require the file's mere
*presence*), and are **documented as required** by `THEORY_ARCHITECTURE.md`'s Theory Contract.
But they are **not read by any runtime code anywhere in the tree** — every version-reporting
code path (`theory_lib/__init__.py`'s `get_theory_version_registry()`,
`theory_lib/meta_data.py`'s `get_theory_version()` / `check_theory_compatibility()` /
`update_all_theory_versions()`) reads and writes `__version__` in each theory's `__init__.py`,
never the `VERSION` file. Git history shows the four files have never had their content changed
since creation (2025-08-01) despite two major theory rewrites (exclusion/imposition restoration)
touching their containing directories. Recommendation: **(b) keep the files but exclude them
from the wheel** — see "Recommendation" below.

## 1. What reads `theory_lib/*/VERSION` at runtime

A whole-tree grep (`code/`, `.github/`, docs, excluding `.git` and `oracle/`) for anything that
opens or reads the four `VERSION` files' *content* returns **zero hits**. Every occurrence of the
literal string `VERSION` in the repository is one of:

| Site | What it does with `VERSION` |
|------|------------------------------|
| `code/src/model_checker/theory_lib/tests/test_theory_conformance.py:44` | Lists `'VERSION'` in `REQUIRED_ROOT_ITEMS`; asserts `os.path.exists(...)` only — never reads content (`test_required_root_items_exist`, lines ~139-146) |
| `code/tests/packaging/test_inclusions.py:25` | Lists `"VERSION"` in `REQUIRED_ROOT_FILES`; asserts membership of `model_checker/theory_lib/{theory}/VERSION` in the wheel/sdist member-path set (`test_root_metadata_file_present`) — never reads content |
| `code/tests/packaging/test_parity.py:66` | `_is_data_path()` classifies any file named `VERSION` (anywhere in the tree) as a "packaged data path"; used only for wheel/sdist *path*-set equality — never reads content |
| `code/src/model_checker/builder/project.py:52` | `REQUIRED_COPY_ITEMS` — scaffolding's explicit copy manifest; `shutil.copy`'s the file byte-for-byte into a new project when generating a theory from a template — never parses/reads it as a version string |
| `code/MANIFEST.in:17` | `recursive-include src VERSION` — sdist packaging rule, path-only |
| `code/pyproject.toml:76` | `"VERSION"` in `[tool.setuptools.package-data]`'s `"*"` allowlist — wheel packaging rule, path-only |
| `.github/workflows/release.yml:40-204` | An unrelated shell variable `VERSION=${GITHUB_REF#refs/tags/v}` derived from the git tag — nothing to do with the theory files |

Runtime version-reporting is a **separate, parallel mechanism** that never touches these files:

- `code/src/model_checker/theory_lib/__init__.py:229-247` — `get_theory_version_registry()`
  imports each theory module and reads `getattr(theory_module, "__version__", "unknown")`.
- `code/src/model_checker/theory_lib/meta_data.py:30-49` — `get_theory_version(theory_name)`
  imports the theory module and reads `getattr(theory_module, '__version__', '0.0.0')`.
- `code/src/model_checker/theory_lib/meta_data.py:52-88` — `check_theory_compatibility()` reads
  `theory_module.__model_checker_version__`.
- `code/src/model_checker/theory_lib/meta_data.py:91-225` — `update_all_theory_versions()`
  regex-edits the `__version__ = "..."` literal *inside `__init__.py`* — it never touches the
  `VERSION` file.
- Each theory's `__init__.py` independently hardcodes `__version__ = "1.0.0"`:
  `bimodal/__init__.py:53`, `logos/__init__.py:26`, `exclusion/__init__.py:17`,
  `imposition/__init__.py:50`.

`meta_data.py` itself has no production consumer — the only importer in the tree is its own test
module (`theory_lib/tests/test_meta_data.py`), which asserts against `__version__`/`__init__.py`
and never references the `VERSION` file (`grep -n "VERSION\b" test_meta_data.py` → no matches).
So the entire theory-versioning *API surface* that exists is exercised only by its own tests, and
that API surface is already anchored on `__init__.py`'s `__version__`, not on the file this task
is about.

**Conclusion on load-bearing-ness**: the `VERSION` files' *content* is not load-bearing anywhere
— no packaging metadata, no theory-version reporting API, and no test assertion ever inspects
what the file says (`1.0.0`); every consumer only checks that a file named `VERSION` *exists* at
that path (conformance test, packaging inclusion/parity tests) or copies it byte-for-byte
(scaffolding). The files' *existence* and *path*, however, is asserted in three separate places
across two independent contracts (theory conformance and packaging).

## 2. Intended convention vs. vestigial: the discriminating evidence

The task description notes all four being `1.0.0` is consistent with both readings. Three pieces
of evidence discriminate:

1. **`THEORY_ARCHITECTURE.md` names `VERSION` explicitly as required, intentional metadata.**
   `code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md:44`: "`README.md`,
   `CITATION.md`, `LICENSE.md`, `VERSION` — theory-level metadata, documentation entry point,
   and citation/licensing files," listed alongside the rest of the mandatory "Required Theory
   File Set." This is not incidental — it is the canonical contract document, and
   `test_theory_conformance.py`'s module docstring says it "[e]ncodes the canonical theory
   contract from `theory_lib/docs/THEORY_ARCHITECTURE.md`... as an executable, parametrized
   test." So per-theory versioning-as-a-file is a *documented, intentional* convention, not an
   accident of copy-paste.

2. **A dedicated runtime API exists for per-theory versioning** (`get_theory_version`,
   `check_theory_compatibility`, `update_all_theory_versions`, `verify_metadata_consistency` in
   `meta_data.py`) — this is further evidence the *concept* of per-theory versions independent of
   the top-level package version was deliberately designed, not vestigial. But (per Section 1)
   this API was built against `__init__.py`'s `__version__`, not the `VERSION` file — i.e. the
   *file* itself was **not chosen as the source of truth** for the one piece of machinery that
   was built to consume per-theory versions. The `VERSION` file and `__version__` are two
   parallel, redundant encodings of the same intended concept, and only one of them was ever
   wired up.

3. **Git history shows the file's content has never been touched, through two major theory
   rewrites.** Each `VERSION` file's `git log --follow` history shows only the same 5-word diff
   (`+1.0.0`, added at file creation) repeated across renames/relocations — the content itself
   was never modified:
   - `bimodal/VERSION`: created 2025-08-01 (`b28e1986`), later touched only by a supplementary
     research commit (`000fc4e3`, 2026-03-02) that did not change content.
   - `exclusion/VERSION` and `imposition/VERSION`: created 2025-08-01, touched by `abb3bf7d`
     (2026-03-03, task 30 research) and `000fc4e3`, then again in **task 120's exclusion/
     imposition restoration** (`71da2978` 2026-07-24 "restore exclusion and port the solver
     abstraction"; `36d4997d` 2026-07-24 "restore imposition and apply the porting recipe") — a
     substantial rewrite of both theories' semantics that did not bump either `VERSION` file.
   - `logos/VERSION`: created 2025-08-01, touched most recently by `feff3cbe` (2026-07-18,
     "removed claude") — again, content unchanged.

   No commit across this history ever changed the string `1.0.0` in any of the four files, even
   when the theory it names underwent a full rewrite. This is direct evidence the *value* is
   vestigial-in-practice, even though the *concept* (per-theory versioning as a documented,
   API-backed feature) is intentional. The two readings are not actually in tension: per-theory
   versioning is an intended, designed convention that is exercised through `__version__` in
   `__init__.py` (which is likewise still `1.0.0` everywhere, but is at least the value the
   runtime API reads), while the `VERSION` file is a second, unconsumed encoding of the same
   never-bumped number.

## 3. How the files reach the wheel

Both the wheel and the sdist ship `theory_lib/*/VERSION` via the same declared mechanism, kept in
parity by explicit cross-reference comments:

- **Wheel**: `code/pyproject.toml:66-79`, `[tool.setuptools.package-data]`, a blanket
  `"*" = [..., "VERSION", ...]` allowlist applied under `include-package-data = true`
  (`pyproject.toml:61`) — this is a *per-package-directory* rule, so it matches
  `theory_lib/{theory}/VERSION` once for every one of the four theory packages, independently.
  The comment at `pyproject.toml:67-71` explicitly says this list "mirrors...
  theory_lib/docs/THEORY_ARCHITECTURE.md's Theory Contract."
- **Sdist**: `code/MANIFEST.in:17`, `recursive-include src VERSION` — a separate, manually
  maintained rule that the file's own comment (`MANIFEST.in:9-13`) says is kept "in sync with the
  wheel's `[tool.setuptools.package-data]` allowlist in pyproject.toml."

**What excluding them from the wheel would take**: remove `"VERSION"` from
`pyproject.toml`'s `[tool.setuptools.package-data]` `"*"` list (or replace the blanket `"*"`
form with a per-package form that omits `VERSION`). The sdist rule (`MANIFEST.in`) is
independent and would be **unaffected** unless the sdist is also meant to drop the files — the
task's Section 5 packaging tests (`test_parity.py`) currently assert wheel/sdist *parity* on the
`VERSION` path class, so an exclude-from-wheel-only remedy requires updating that parity
assertion (see Section 5) or excluding from both artifacts to preserve parity without a special
case.

## 4. What the packaging contract suite asserts (must be checked against any change)

`code/tests/packaging/` (`pytest.mark.packaging`, builds a fresh wheel+sdist per session via
`conftest.py`, never reads stale `code/dist/`):

- **`test_inclusions.py::test_root_metadata_file_present`** — parametrized over
  `AVAILABLE_THEORIES` (4) × `REQUIRED_ROOT_FILES` (`README.md`, `CITATION.md`, `LICENSE.md`,
  `VERSION`) × `artifact` (`wheel`, `sdist`) = **8 assertions specifically about `VERSION`**
  (4 theories × 2 artifacts), each asserting
  `f"{prefix}/theory_lib/{theory}/VERSION"` is a member of that artifact. **Any remedy that
  removes `VERSION` from a theory directory on disk, or excludes it from an artifact, must
  update this test** (either drop `VERSION` from `REQUIRED_ROOT_FILES`, or special-case which
  artifact(s) it's required in).
- **`test_parity.py::test_data_path_parity`** — `_is_data_path()` classifies any file literally
  named `VERSION` as a "packaged data path," then asserts the *set* of such paths under
  `model_checker/` is identical between the wheel and the (normalized) sdist view. **This test
  will fail if `VERSION` is excluded from one artifact but not the other** (e.g. exclude from
  wheel, keep in sdist) — it must be updated in lockstep with any asymmetric exclusion decision.
- **`test_exclusions.py`** does **not** currently reference `VERSION` at all — its
  `EXCLUSION_CLASSES` table covers `oracle`, `TODO.md`, `theory_lib/*/history`,
  `theory_lib/*/reports`, `theory_lib/*/examples_refactored`, and `__pycache__/*.pyc`. No
  existing assertion blocks adding `VERSION` (or a subset of the four) to a future exclusion
  class; conversely, no existing assertion currently *requires* it be excluded either — this
  file would need a new entry added under remedy (b).
- Outside the declared `file_scope` but directly implicated by remedy (a) ("remove"):
  `code/src/model_checker/theory_lib/tests/test_theory_conformance.py:35-46` (`REQUIRED_ROOT_ITEMS`,
  asserts on-disk existence per theory — `theory_lib/tests/`, not `code/tests/packaging/`),
  `code/src/model_checker/builder/project.py:43-52` (`REQUIRED_COPY_ITEMS`, scaffolding
  fail-fasts if `VERSION` is missing from a source theory when generating a new project), and
  `code/src/model_checker/theory_lib/docs/THEORY_ARCHITECTURE.md:44` (the contract text itself).
  None of these three files is inside this task's declared `file_scope`
  (`code/src/model_checker/theory_lib/{bimodal,exclusion,imposition,logos}/VERSION`,
  `theory_lib/__init__.py`, `code/tests/packaging/`, `code/pyproject.toml`) — a "remove" remedy
  cannot be executed within scope as declared; it would require expanding `file_scope` at
  planning time.

## 5. Confirming W002 on a fresh build

Ran directly, not from stale artifacts. `code/dist` is gitignored (`.gitignore:13`, `**/dist`),
so a local build does not perturb the tree, and `code/build/` /
`src/model_checker.egg-info/` were removed first to avoid the incremental-build staleness trap
`conftest.py` itself documents.

```
$ cd code && rm -rf dist build src/model_checker.egg-info
$ python3 -m build --no-isolation --outdir dist
...
Successfully built model_checker-1.3.0.tar.gz and model_checker-1.3.0-py3-none-any.whl

$ check-wheel-contents dist/*.whl
dist/model_checker-1.3.0-py3-none-any.whl: W002: Wheel contains duplicate files:
  model_checker/theory_lib/bimodal/VERSION
  model_checker/theory_lib/exclusion/VERSION
  model_checker/theory_lib/imposition/VERSION
  model_checker/theory_lib/logos/VERSION
(exit 1)

$ check-wheel-contents --ignore W002 dist/*.whl
dist/model_checker-1.3.0-py3-none-any.whl: OK
(exit 0)
```

`check-wheel-contents 0.6.3` (via `/home/benjamin/.nix-profile/bin/check-wheel-contents`), same
version task 155 and task 156 recorded. This matches task 155's finding exactly and confirms it
is not an artifact of a stale `code/dist/` — it reproduces from a from-scratch build.

**Stale-claim correction**: `specs/archive/125_release_engineering_and_pypi_rehearsal/` (e.g.
`summaries/01_release-engineering-summary.md:89`, `PUBLISH-CHECKLIST.md:43`,
`rehearsal/parity-diff.md:20`, `.return-meta.json:15`) records `check-wheel-contents dist/*.whl`
→ `OK` (clean). That rehearsal predates the four `VERSION` files becoming byte-identical
duplicates and **does not reproduce today** — the plain run now exits 1 with the W002 finding
shown above, confirmed independently in this task, in task 155, and in task 156's report
(`specs/156_portable_pinned_release_verification_runner/reports/01_portable-release-verification.md:104-106`,
which explicitly notes "the archived rehearsal predates the VERSION-file duplication that now
triggers W002"). `specs/TODO.md:161`'s existing note that the rehearsal evidence is stale is
correct and this task's finding is additional, independent confirmation of the same staleness —
not a new discovery requiring `PUBLISH-CHECKLIST.md` itself be edited under this task's scope
(it is outside `file_scope`).

Also worth noting: no CI workflow currently invokes `check-wheel-contents` at all
(`grep -rn "check-wheel-contents" .github/workflows/` → no matches). It exists today only as a
manual/local verification step (task 155's summary, task 156's runner-in-progress), not a CI
gate — so W002 is not currently blocking anything mechanically; it is a documented, recorded
finding.

## Evaluation of the three candidate remedies

### (a) Remove the four `VERSION` files, single source of truth = `__init__.py`'s `__version__`

**For**: `__version__` is already the *actual* single source of truth for every runtime
consumer (Section 1) — the `VERSION` file's content is never read, so deleting it changes no
runtime behavior. Consistent with CLAUDE.md's "No Backwards Compatibility" clean-break
philosophy.

**Against**: requires editing at least three files **outside the declared `file_scope`**
(`theory_lib/tests/test_theory_conformance.py`'s `REQUIRED_ROOT_ITEMS`,
`builder/project.py`'s `REQUIRED_COPY_ITEMS`, and `THEORY_ARCHITECTURE.md`'s Theory Contract
text), plus `MANIFEST.in` (also out of scope) and the in-scope `pyproject.toml` and
`code/tests/packaging/` files. It also contradicts the *documented* intent
(`THEORY_ARCHITECTURE.md:44` names `VERSION` as required theory-level metadata) — removing it
is a legitimate "we no longer want this convention" decision, but it is a bigger, cross-cutting
contract change than the task's `file_scope` supports without expansion, and it discards a
theory-level-versioning surface (the file, distinct from `__version__`) that a future feature
(e.g. per-theory PyPI-independent releases, or exposing `VERSION` to non-Python consumers who
can't `import` the package) could plausibly still want.

### (b) Keep the files, exclude them from the wheel

**For**: fully achievable within the declared `file_scope`. Only `pyproject.toml` (drop
`"VERSION"` from the wheel's `[tool.setuptools.package-data]` allowlist, or restructure it to a
non-blanket per-file form) and `code/tests/packaging/` (update `test_inclusions.py`'s
`REQUIRED_ROOT_FILES`/`artifact` parametrization so `VERSION` is only asserted for `sdist`, and
`test_parity.py`'s `_is_data_path()` classification so `VERSION` is no longer expected to appear
in the wheel-side parity set, or add it to `test_exclusions.py`'s `EXCLUSION_CLASSES`) need to
change. `theory_lib/tests/test_theory_conformance.py` (on-disk existence), `builder/project.py`
(scaffolding copy), and `THEORY_ARCHITECTURE.md` (contract text) are **all unaffected**, because
the files still exist on disk in the source tree and in the sdist — only the wheel's copy is
dropped. This preserves the documented per-theory-metadata contract for source/sdist consumers
(anyone unpacking the sdist, or reading the repo) while eliminating the wheel-installed
duplicate that `check-wheel-contents` actually flags (W002 is specifically a *wheel* contents
check). Directly resolves the reported symptom: a plain `check-wheel-contents` run against the
resulting wheel would no longer have any `VERSION` member to flag as duplicated, reaching exit 0
without `--ignore W002`.

**Against**: introduces an asymmetry between wheel and sdist (something present in one packaged
artifact and not the other) that the parity suite currently treats as invariant by design — this
must be a deliberate, documented exception, not a silent test edit. A user who `pip install`s the
wheel loses filesystem access to a theory's `VERSION` file (though, per Section 1, nothing in the
package ever read it that way — `importlib.metadata` / `__version__` remain available regardless
of wheel packaging).

### (c) Keep the files, pin `--ignore W002` permanently

**For**: zero code change to `VERSION`, `pyproject.toml`, or `code/tests/packaging/` — the
change is confined to wherever `check-wheel-contents` is invoked (today: nowhere in CI, only in
manual/local verification runs and task 156's in-progress portable release-verification runner).
Matches the posture task 155 already established: `check-wheel-contents` is documented as
"non-blocking... a strengthening of local verification, not a gate," and its plan explicitly
forbade touching the `VERSION` files to silence W002 (scoped as future work — this task).

**Against**: does not actually resolve anything — it formalizes accepting a known lint finding
forever rather than making a decision about it, which is precisely what this task exists to
avoid doing by default (the task description explicitly forbids assuming any remedy, including
implicitly defaulting to "leave it be"). It leaves genuinely duplicate, byte-identical files
shipping in every wheel indefinitely with no plan to ever differentiate or remove them. Since no
CI gate currently runs `check-wheel-contents` at all, "pinning `--ignore W002` permanently" has
no concrete artifact to attach the pin to within this task's `file_scope` — the pin would need
to live in task 156's runner or a future CI wiring, both outside `code/pyproject.toml` and
`code/tests/packaging/`.

## Recommendation

**Remedy (b): keep the four `VERSION` files, exclude them from the wheel only.**

Reasons:

1. It is the only remedy fully executable within the declared `file_scope`
   (`code/pyproject.toml` + `code/tests/packaging/`) — remedy (a) requires touching at least
   three files outside scope (`test_theory_conformance.py`, `builder/project.py`,
   `THEORY_ARCHITECTURE.md`), and remedy (c) has no in-scope artifact to pin against (no CI gate
   currently runs `check-wheel-contents`).
2. It directly resolves the reported symptom — a plain (non-`--ignore`) `check-wheel-contents`
   run against a fresh wheel reaches exit 0, satisfying the task's own verification bar ("a
   plain run should reach exit 0 without needing `--ignore W002` if the remedy was
   deduplication") — without requiring the broader architectural decision of removing per-theory
   versioning-as-a-file, which Section 2 shows is a documented, intentional (if
   never-yet-exercised) convention that this task should not unilaterally retire.
3. It is consistent with the evidence in Section 1: nothing needs `VERSION` accessible from an
   *installed* package (every runtime consumer reads `__version__` from `__init__.py` instead),
   so excluding it from the wheel changes no behavior for any `pip install`ed consumer, while
   still satisfying `theory_lib/tests/test_theory_conformance.py`'s on-disk-presence contract and
   `builder/project.py`'s scaffolding requirement (both check the source tree / sdist-derived
   checkout, not the wheel).

**What would overturn this recommendation**:

- If a future feature needs `VERSION` readable from an *installed* (wheel) package at runtime
  (e.g. `importlib.resources` lookup of a theory's on-disk version string, bypassing
  `__version__`) — that would argue for keeping it in the wheel and instead pursuing remedy (a)
  by consolidating onto a single real source of truth wired to genuinely-per-theory version
  bumps (which would also stop the files being byte-identical, independently resolving W002
  without exclusion).
- If a maintainer decides the per-theory-versioning convention itself (both the file and
  `__version__`) is not worth preserving — since it has never been exercised in over a year of
  history even through two theory rewrites — that would argue for remedy (a) as a genuine
  cleanup, accepting the larger, out-of-scope-touching change.
- If the packaging contract suite's wheel/sdist parity invariant (`test_parity.py`) is judged too
  important to carry a documented exception, and the team prefers symmetry over the specific
  wheel-only fix — that would argue for excluding `VERSION` from **both** wheel and sdist
  (a symmetric variant of (b) requiring `MANIFEST.in`, out of scope) rather than the wheel-only
  form recommended here.
