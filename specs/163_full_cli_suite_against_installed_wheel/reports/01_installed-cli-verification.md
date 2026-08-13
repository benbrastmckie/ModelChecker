# Verifying the CLI Against a Real pip Install

**Task**: 163 — Run the full CLI suite against a pip-installed wheel.
- **Started**: 2026-08-13
- **Completed**: 2026-08-13
- **Effort**: ~1 session (conversational investigation; no source changes made)
- **Dependencies**: none blocking. Adjacent: `harden_release_ci_testpypi_gate` (owns
  `release.yml`), `fix_testpypi_trusted_publisher` (blocks that one, not this one).
- **Sources/Inputs**: live inspection of `code/tests/cli/`, `code/tests/utils/helpers.py`,
  `code/tests/packaging/conftest.py`, `.github/workflows/release.yml`, `flake.nix`,
  `code/pyproject.toml`; a local run of the packaging contract suite; GitHub Actions run
  31654864134.
- **Artifacts**: this report.
- **Standards**: `.claude/context/formats/report-format.md`; `code/docs/core/TESTING_GUIDE.md`
  (TDD); `.claude/rules/pr-prohibition.md` (push/tag/upload remain user-only).

---

## Executive Summary

The goal is to prove that `pip install model-checker` yields a CLI that works in every
documented respect, on a machine that is not this one. The obstacle is that this is a NixOS
host, where a pip-installed binary wheel cannot resolve its own bundled shared libraries
without help.

The central finding is that **this is one function away, not a new test suite away**. Every CLI
test in `code/tests/cli/` funnels through a single helper, `run_cli_command`
(`code/tests/utils/helpers.py:14`), which hardcodes both the interpreter invocation and the
`PYTHONPATH` injection that points at the working tree. Parametrising that one helper over an
invocation mode lets the entire existing suite — including its parser-derived completeness
gate — execute against a pip-installed wheel unchanged.

Three supporting findings shape the recommendation:

1. The local packaging suite passes on this host **only because** `conftest.py` repairs the
   dynamic linker via `LD_LIBRARY_PATH`. Local green therefore cannot distinguish "works
   everywhere" from "works because we patched it".
2. This host's glibc is **2.42** — newer than any mainstream distro. It is the most permissive
   possible target, so it cannot detect breakage at the low end where breakage actually occurs.
3. A container, not a VM, is the correct instrument: the requirement is a different *userland*,
   not a different kernel.

A fourth finding is a **correction to an existing task's design**. `harden_release_ci_testpypi_gate`
proposes a `verify-testpypi` job that installs from TestPyPI. Gating on the **`dist` build
artifact** instead is both more robust and, critically, **not blocked** by
`fix_testpypi_trusted_publisher` — whereas the TestPyPI design cannot be exercised at all until
that user-only OIDC registration is fixed.

---

## Context & Scope

### What already exists

| Asset | Location | What it covers |
|---|---|---|
| CLI test suite | `code/tests/cli/` | Flag matrix, parse-file-flags, doc-flag guard |
| Invocation helper | `code/tests/utils/helpers.py:14` | Single chokepoint for all CLI subprocess calls |
| Completeness gate | `test_flag_matrix.py` | Parser-derived; fails if any flag is untested and unexcluded |
| Packaging contract suite | `code/tests/packaging/` | Builds sdist+wheel, installs into venv, runs console script |
| Release matrix | `.github/workflows/release.yml` | ubuntu/macos/windows × Python 3.10–3.12 |
| TestPyPI rehearsal | `release.yml` `publish-testpypi` | Uploads only; `continue-on-error: true` |

Measured on this host during investigation: `pytest tests/packaging/ -m packaging` →
**106 passed, 4 skipped, 111s**.

### Scope boundary against existing tasks

This task owns the **test harness**. It deliberately does **not** own
`.github/workflows/release.yml`.

- `harden_release_ci_testpypi_gate` already declares `release.yml` in its `file_scope` and
  already owns item (1)(b), "add a `verify-testpypi` job". Claiming the same file here would
  auto-serialise this task behind it.
- That task is in turn blocked on `fix_testpypi_trusted_publisher`, which is user-only web-UI
  work. Inheriting that block would strand an improvement that has no dependency of its own.

The CI wiring is therefore carried in this report as a **handoff** (Recommendation R4), with the
exact YAML, so the owning task can adopt it without re-derivation.

### Non-goals

- Fixing the TestPyPI trusted-publisher registration.
- Making project generation non-interactive — already owned as item (4) of
  `harden_release_ci_testpypi_gate`, where it is correctly framed as a user-facing usability fix.
- Any `git push`, tag, or upload operation (user-only per `.claude/rules/pr-prohibition.md`).

---

## Findings

### F1 — The suite has a single invocation chokepoint

`run_cli_command` hardcodes exactly two environment decisions:

```python
env['PYTHONPATH'] = str(src_dir) + os.pathsep + env.get('PYTHONPATH', '')
cmd = [sys.executable, '-m', 'model_checker'] + args
```

Every CLI test reaches the binary through this function, exposed to test files as the `run_cli`
fixture (`code/tests/cli/conftest.py:49`). Nothing else in the suite constructs a CLI
invocation. This is the seam that makes installed-package testing a configuration change rather
than a rewrite.

### F2 — A parser-derived completeness gate already exists

`test_every_registered_flag_is_covered_or_excluded` enumerates `ParseFileFlags().parser._actions`
and asserts every registered flag is either dispatch-tested or on an explicit, commented
exclusion list. The list holds exactly one entry, `load_theory`, with a stated reason.

This is the hard part of "test the CLI in all aspects", and it is already built and already
enforced. It also means the coverage guarantee **transfers for free** to whatever environment
the suite runs in — there is no second inventory to maintain.

### F3 — Local green depends on a repair no user applies

`code/tests/packaging/conftest.py` documents the mechanism precisely: the pip-installed
`z3-solver` wheel installs cleanly but fails at import with `libz3.so not found`, because the
wheel's bundled libraries expect FHS-standard search paths that Nix does not provide outside
`nix-ld`-patched binaries. The fixture prepends the Nix C++ runtime directory to
`LD_LIBRARY_PATH`, which resolves it, with `handle_known_venv_libz3_link_failure` retained as a
loud-skip backstop.

This is well-engineered and honestly documented. But it has a consequence worth stating plainly:
**a local pass is evidence about a repaired environment, not about a user's environment.** It
protects against false negatives; it does not protect against false positives.

### F4 — glibc 2.42 is the most permissive target available

Measured on this host: `ldd (GNU libc) 2.42`.

| Environment | glibc |
|---|---|
| This host / any Nix FHS sandbox built from it | **2.42** |
| Debian 12 | 2.36 |
| Ubuntu 22.04 LTS | 2.35 |
| Ubuntu 20.04 LTS | 2.31 |

manylinux wheels pin an old baseline specifically so they run at the bottom of that range.
Testing at the top of it yields no information about the bottom, which is where linkage
breakage manifests.

### F5 — The Nix FHS sandbox is not a viable substitute for a container

Evaluated as the daemon-free local option and rejected. Concrete downsides:

1. **`targetPkgs` is a list you write**, so a missing library surfaces as "I forgot to add it",
   not as "a user would lack it". It tests dependency enumeration, not wheel self-sufficiency.
2. **Serves glibc 2.42** (F4).
3. **Nix-store libraries, not distro libraries** — including the `libstdc++` whose Nix-ness is
   the original problem.
4. **No `EXTERNALLY-MANAGED` marker**, so it cannot test the documented install command (F10).
5. **Host leakage** — `buildFHSEnv` inherits the environment and bind-mounts real `/home` and
   `/tmp`, putting `~/.cache/pip` (possibly holding a locally built wheel), `PYTHONPATH`, and
   `NIX_*` in scope. Containers start clean.
6. **A present toolchain masks sdist failures** — adding `stdenv.cc` (tempting, for libstdc++)
   gives pip a working compiler, so an sdist fallback succeeds where a slim image would fail.
7. **Not portable to CI** — it runs only on Nix hosts and is pinned to the local nixpkgs
   revision, so nothing built with it can become the release gate.

Neither `docker` nor `podman` is currently installed on this host; `nix` is.

### F6 — Gating on the build artifact beats gating on TestPyPI

`harden_release_ci_testpypi_gate` item (1)(b) specifies installing from TestPyPI with
`--extra-index-url https://pypi.org/simple/` plus a bounded retry for index propagation lag.
That design is sound but carries avoidable cost:

- `publish-testpypi` is deliberately `continue-on-error: true`, so it cannot itself be a gate
  without also removing that tolerance (item 1(a)).
- TestPyPI does not mirror `z3-solver` or `networkx`, so `--extra-index-url` is mandatory, and
  pip's index priority across two indexes is not deterministic.
- Index propagation lag requires retry logic that can flake.
- **It cannot be built or exercised at all until `fix_testpypi_trusted_publisher` completes** —
  a user-only web-UI change.

Installing the **`dist` artifact** produced by the existing `build` job avoids all four. It is
the byte-identical wheel that will be published, so fidelity is equal or better, and the job can
land today with no dependency.

The two are complementary rather than exclusive: artifact-gating proves the wheel works;
TestPyPI verification additionally proves the *upload and index metadata* work. The finding is
about **ordering** — artifact-gating is unblocked and should not wait behind the other.

### F7 — The `load_theory` exclusion is probably retirable

`load_theory` is excluded because it dispatches to `BuildProject.ask_generate()` and blocks on
`input()`. But `run_cli_command` already accepts an `input=` parameter, so piping `"y\n"` may
close the matrix without any source change. Its behavioural coverage already exists in
`test_generate_then_execute.py`, which exercises generate-then-execute per theory.

The deeper fix — a real `--yes`/non-interactive path — is item (4) of
`harden_release_ci_testpypi_gate` and must not be duplicated here. Only the *test-side*
exclusion is in scope.

### F8 — A vacuous pass is the main hazard of this change

If `code/src` reaches `sys.path` in the verification environment, `import model_checker`
silently resolves to the working tree and the whole suite passes without touching the wheel —
reporting success for a test that never ran against its subject. This failure is silent by
construction and must be asserted against explicitly, not assumed away.

### F9 — `nix flake check` is red on master, in a z3-sensitive test

At the released commit, the `Tests` workflow failed while `Release` succeeded:

```
FAILED src/model_checker/builder/tests/unit/test_example.py::
  TestBuildExampleIntegration::test_iteration_via_iterate_api
  - AssertionError: False is not true : Should find initial model for A
1 failed, 2012 passed, 254 skipped
```

This is directly relevant rather than incidental. `flake.nix` builds against **nixpkgs-native
z3** and strips the PyPI dependency (`pythonRemoveDeps = [ "z3-solver" ]`), while users receive
the **PyPI `z3-solver` wheel**. A solver-result assertion failing only under the Nix build is
exactly the divergence class this task exists to detect. It may be a divergent-draw flake — the
codebase documents that class elsewhere — but it should be diagnosed, not assumed.

### F10 — The documented install command may fail on current distros

The headline instruction is bare `pip install model-checker` (`README.md`,
`docs/installation/README.md:114`). On Debian 12, Ubuntu 23.04+, and Fedora 38+, PEP 668 makes
that error with `externally-managed-environment`.

`VIRTUAL_ENVIRONMENTS.md` and `BASIC_INSTALLATION.md` both exist and discuss venvs, so the
routing may well be adequate. The point is that **no current test can settle the question**, and
a container-based check settles it mechanically.

---

## Decisions

| ID | Decision | Rationale |
|---|---|---|
| D1 | Container, not VM | The requirement is a different userland, not a different kernel. A VM is warranted only for OS integration or non-Linux targets; the release matrix already covers macOS/Windows. |
| D2 | podman locally, not a Nix FHS sandbox | F5. The FHS sandbox is strictly worse on every axis once podman exists, and cannot move to CI. |
| D3 | Extend the existing suite via an invocation mode; do not write a second suite | F1 + F2. A parallel installed-CLI suite would immediately begin drifting from the source-tree one, and would need its own completeness gate. |
| D4 | Gate on the `dist` artifact; treat TestPyPI verification as complementary | F6. Equal fidelity, no cross-index nondeterminism, no retry flake, and no dependency on user-only OIDC work. |
| D5 | This task owns `code/tests/**`; `release.yml` stays with `harden_release_ci_testpypi_gate` | Avoids a `file_scope` collision that would serialise this task behind a blocked one. |
| D6 | The vacuous-pass guard is mandatory, not optional | F8. Without it the entire change can silently self-defeat, which is worse than not making it. |

---

## Recommendations

Ordered by value per unit of effort.

### R1 — Diagnose the `nix flake check` failure first

**Before** any new verification work. It is already red on `master` at the released commit, and
it sits precisely on the nixpkgs-z3 / PyPI-z3-solver seam this task is about. Determine whether
it is a divergent draw or a genuine version sensitivity. Owned separately; noted here because it
should precede the rest.

### R2 — Parametrise `run_cli_command` over an invocation mode

Roughly 15 lines in one file, plus `import shutil`:

```python
env = os.environ.copy()
mode = os.environ.get('MODELCHECKER_CLI_TEST_MODE', 'source')

if mode == 'source':
    env['PYTHONPATH'] = str(current_dir / 'src') + os.pathsep + env.get('PYTHONPATH', '')
    cmd = [sys.executable, '-m', 'model_checker'] + args
elif mode == 'installed':
    # Console script from a pip-installed wheel. No PYTHONPATH injection --
    # any reliance on the source tree must fail here; that is the point.
    env.pop('PYTHONPATH', None)
    script = shutil.which('model-checker')
    if script is None:
        raise RuntimeError("CLI_TEST_MODE=installed but 'model-checker' is not on PATH")
    cmd = [script] + args
elif mode == 'installed-module':
    env.pop('PYTHONPATH', None)
    cmd = [sys.executable, '-m', 'model_checker'] + args
else:
    raise ValueError(f"Unknown MODELCHECKER_CLI_TEST_MODE: {mode!r}")
```

Default stays `source`, so the existing developer loop is unchanged. `installed-module`
additionally yields console-script vs `python -m` parity across the *whole* suite, where the
packaging tests currently check it for `--version` and `--help` only.

### R3 — Add the vacuous-pass guard

```python
def test_installed_mode_uses_the_installed_package():
    if os.environ.get('MODELCHECKER_CLI_TEST_MODE', 'source') == 'source':
        pytest.skip('source mode: this assertion applies to installed modes only')
    import model_checker
    assert 'site-packages' in model_checker.__file__, (
        f'installed mode is resolving to {model_checker.__file__} -- '
        'the source tree is shadowing the wheel; the suite would pass vacuously'
    )
```

### R4 — Handoff: `verify-install` job (for `harden_release_ci_testpypi_gate`)

Not to be implemented under this task (D5). Recorded here so it needs no re-derivation:

```yaml
  verify-install:
    name: Verify wheel installs (${{ matrix.image }})
    needs: build
    runs-on: ubuntu-latest
    container: ${{ matrix.image }}
    strategy:
      fail-fast: false
      matrix:
        image: ['python:3.10-slim', 'python:3.11-slim', 'python:3.12-slim']

    steps:
    - uses: actions/checkout@v4
    - uses: actions/download-artifact@v4
      with: { name: dist, path: dist/ }

    - name: Install the wheel and run the full CLI suite against it
      run: |
        set -eux
        python -m venv /tmp/v && . /tmp/v/bin/activate
        pip install --upgrade pip
        pip install dist/*.whl pytest
        cd code
        MODELCHECKER_CLI_TEST_MODE=installed        pytest tests/cli/ -v
        MODELCHECKER_CLI_TEST_MODE=installed-module pytest tests/cli/ -v
```

With `publish-pypi` changed to `needs: [build, publish-testpypi, verify-install]`. That single
edit converts the pipeline from "publish, then discover" to "cannot publish a wheel that does
not install".

### R5 — Local runner script for the debug loop

A small `code/scripts/verify-installed-cli.sh` wrapping the podman invocation, so the CI
behaviour is reproducible locally in seconds rather than five-minute pipeline cycles:

```bash
podman run --rm -v "$PWD:/w:ro" -w /w python:3.11-slim bash -lc '
  python -m venv /v && . /v/bin/activate
  pip install --quiet /w/code/dist/*.whl pytest
  cd /w/code && MODELCHECKER_CLI_TEST_MODE=installed pytest tests/cli/ -q'
```

Requires `virtualisation.podman.enable = true;` in the host NixOS configuration — user action,
one line plus a rebuild.

### R6 — Retire the `load_theory` exclusion if piping stdin suffices

Attempt `input="y\n"` through the existing helper parameter. If it works, remove the entry from
`_EXCLUDED_FLAGS` so the completeness gate covers the full registered set with no exclusions. If
it does not, leave the exclusion and its comment intact — the real fix is owned elsewhere (F7).

### R7 — Deferred: executable documentation

The largest remaining gap, recorded but not scoped here. The doc-flag guard proves documented
flags *exist on the parser*; it does not prove documented commands *do what the prose claims*.
The same `MODELCHECKER_CLI_TEST_MODE=installed` seam plus the existing extractor from the
doc-flag guard would allow extracted invocations to be **executed** against an installed package
and asserted on. Worth its own task once R2–R4 have landed.

---

## Open Questions

1. Is F9's failure a divergent draw or a genuine nixpkgs-z3 version sensitivity? Determines
   whether the Nix build and the PyPI wheel need separate expectation sets.
2. Does any CLI path branch on `isatty()`? If so, subprocess tests cannot observe it and a pty
   harness would be needed. No evidence either way was gathered.
3. Should `ubuntu:20.04` (glibc 2.31) join the R4 matrix? It is the strongest available signal
   at the low end (F4), at the cost of an apt-based Python setup step.

## References

- `code/tests/utils/helpers.py:14` — `run_cli_command`, the invocation seam
- `code/tests/cli/conftest.py:49` — `run_cli` fixture
- `code/tests/cli/test_flag_matrix.py` — parser-derived completeness gate and exclusion list
- `code/tests/packaging/conftest.py:115` — `handle_known_venv_libz3_link_failure`, the NixOS repair
- `.github/workflows/release.yml` — `build`, `publish-testpypi`, `publish-pypi` job chain
- `flake.nix:29,47` — nixpkgs-native z3, `pythonRemoveDeps = [ "z3-solver" ]`
- Task `harden_release_ci_testpypi_gate` — owns `release.yml` and the TestPyPI gate
- Task `fix_testpypi_trusted_publisher` — blocking prerequisite for the above
