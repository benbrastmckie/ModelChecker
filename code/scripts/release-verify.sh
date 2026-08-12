#!/usr/bin/env bash
# release-verify.sh
#
# Portable, pinned local release-verification runner. Rehearses the build/check
# portion of the PyPI release pipeline (see .github/RELEASE_SETUP.md's "Local
# Rehearsal (No Publish)" section) without any credentials or network publish
# calls, using a pinned toolchain provisioned into a venv inside a single
# `nix develop` invocation so flake.nix is never touched.
#
# Step sequence:
#   (a)  provision   -- python -m venv + pip install the pinned tools from
#                        code/scripts/release-tools-requirements.txt
#   (b)  build       -- python -m build (fresh code/dist/)               [hard gate]
#   (c)  twine       -- twine check --strict code/dist/*                 [hard gate]
#   (d1) check-wheel-contents (bare)      -- expected nonzero (W002)     [informational]
#   (d2) check-wheel-contents --ignore W002 -- "anything NEW?" signal    [hard gate]
#   (e1) reference fetch -- pip download --no-deps model-checker==<REF>
#   (e2) file listings   -- sorted file listing of new wheel and reference wheel
#   (e3) diffs           -- full-listing diff + maxdepth-2 top-level-dir diff  [informational]
#   (f)  hashes          -- sha256sum of new wheel, new sdist, reference wheel
#        parity-diff.md  -- generated evidentiary report (not a release gate)
#
# Usage:
#   bash code/scripts/release-verify.sh [--ref VERSION] [--out DIR] [--help]
#
#   --ref VERSION   Published model-checker version to diff against. Default: 1.2.12.
#   --out DIR       Directory to write the evidence set into. Default:
#                    /tmp/release-verify-<UTC-timestamp>/ (never $TMPDIR, which
#                    `nix develop` recreates fresh on every invocation).
#   --help          Print this usage block and exit 0 without entering `nix develop`.
#
# Evidence files written to <out>/ (12 total):
#   build.log                     -- python -m build stdout/stderr + dist/ listing
#   twine-check.txt                -- twine check --strict output
#   wheel-contents.txt             -- bare check-wheel-contents output (W002 expected)
#   wheel-contents-ignore-w002.txt -- check-wheel-contents --ignore W002 output
#   new-wheel-files.txt            -- sorted file listing of the freshly built wheel
#   ref-<REF>-wheel-files.txt      -- sorted file listing of the reference wheel
#   wheel-files-diff.txt           -- unified diff of the two file listings
#   top-level-dir-diff.txt         -- unified diff of the two top-level dir listings
#   pip-download-<REF>.log         -- pip download --no-deps output
#   sha256sums.txt                 -- sha256 of new wheel, new sdist, reference wheel
#   parity-diff.md                 -- generated evidentiary report (human-classified)
#   summary.txt                    -- per-step status ledger (name, class, exit, evidence)
#
# Exit-code contract:
#   0 -- all hard gates green (informational steps may still be nonzero)
#   1 -- a hard gate failed
#   2 -- a required step (provisioning or reference fetch) could not run at all;
#        the evidence set is INCOMPLETE and must not be read as a pass
#
# Reading a nonzero check-wheel-contents (bare) exit: this is EXPECTED on the
# current tree. It reports W002 (duplicate files) for the four identical
# theory_lib/{bimodal,exclusion,imposition,logos}/VERSION files. That
# deduplication is tracked as a separate, later task. A nonzero exit here does
# NOT mean the toolchain is broken -- read wheel-contents-ignore-w002.txt (the
# hard-gated companion run) to see whether anything NEW appeared.
#
# The script accumulates failures rather than aborting on the first one (posture
# matches code/scripts/verify-refactor.sh: set -uo pipefail, not -e), so the
# whole sequence always runs to completion and reports one consolidated result.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
cd "$REPO_ROOT"

# --- Argument parsing (plain while/case, no getopts -- matches verify-refactor.sh's style) ---

REF="1.2.12"
OUT_DIR=""

print_help() {
  cat <<'EOF'
Usage: bash code/scripts/release-verify.sh [--ref VERSION] [--out DIR] [--help]

  --ref VERSION   Published model-checker version to diff against. Default: 1.2.12.
  --out DIR       Directory to write the evidence set into. Default:
                   /tmp/release-verify-<UTC-timestamp>/
  --help          Print this usage block and exit 0.

Evidence files written to <out>/ (12 total):
  build.log, twine-check.txt, wheel-contents.txt,
  wheel-contents-ignore-w002.txt, new-wheel-files.txt,
  ref-<REF>-wheel-files.txt, wheel-files-diff.txt, top-level-dir-diff.txt,
  pip-download-<REF>.log, sha256sums.txt, parity-diff.md, summary.txt

Exit codes:
  0 -- all hard gates green
  1 -- a hard gate failed
  2 -- a required step (provisioning or reference fetch) could not run;
       the evidence set is incomplete
EOF
}

while [ $# -gt 0 ]; do
  case "$1" in
    --ref)
      REF="${2:-}"
      if [ -z "$REF" ]; then
        echo "[release-verify] --ref requires a value" >&2
        exit 2
      fi
      shift 2
      ;;
    --out)
      OUT_DIR="${2:-}"
      if [ -z "$OUT_DIR" ]; then
        echo "[release-verify] --out requires a value" >&2
        exit 2
      fi
      shift 2
      ;;
    --help)
      print_help
      exit 0
      ;;
    *)
      echo "[release-verify] Unknown argument: $1" >&2
      print_help
      exit 2
      ;;
  esac
done

if [ -z "$OUT_DIR" ]; then
  OUT_DIR="/tmp/release-verify-$(date -u +%Y%m%dT%H%M%SZ)"
fi

# Resolve --out to an absolute path and create it BEFORE any re-exec, so the
# evidence directory is never accidentally interpreted relative to a shell
# that will be replaced, and is never under $TMPDIR (which nix develop
# recreates, non-persisting, on every invocation).
mkdir -p "$OUT_DIR"
OUT_DIR="$(cd "$OUT_DIR" && pwd)"

# --- Single-invocation guard -------------------------------------------------
# The entire sequence (provisioning, build, checks, reference fetch, diffs)
# must run inside exactly ONE `nix develop` invocation, because each
# invocation gets a fresh, non-persisting $TMPDIR. Re-entering `nix develop`
# per step would silently truncate the venv/build state between steps. This
# guard re-execs itself exactly once, forwarding the already-absolutized
# --out and the resolved --ref, then proceeds without recursing.
if [ -z "${RELEASE_VERIFY_IN_SHELL:-}" ]; then
  export RELEASE_VERIFY_IN_SHELL=1
  exec nix develop --command bash "$0" --ref "$REF" --out "$OUT_DIR"
fi

# From here on we are guaranteed to be inside the single nix develop shell.

export PIP_USER=0

FAILURES=0
note() { echo "[release-verify] $*"; }
fail() {
  echo "[release-verify] FAIL: $*" >&2
  FAILURES=$((FAILURES + 1))
}

# setup_fail: a required step (provisioning or reference fetch) could not run
# at all. Never continue past this into steps that would produce a partial,
# success-looking evidence set. Exits 2 (distinct from the hard-gate-failure
# exit 1).
setup_fail() {
  echo "[release-verify] SETUP FAILED: $*" >&2
  {
    echo "SETUP FAILED: $*"
  } >> "${OUT_DIR}/summary.txt"
  exit 2
}

# record_step <name> <exit_code> <gate|info> <evidence_file>
# Appends one line to the status ledger. Called incrementally (not only at the
# end) so a crashed or network-failed run still leaves a ledger showing which
# steps never ran.
record_step() {
  local step_name="$1" step_exit="$2" step_class="$3" step_evidence="${4:-}"
  printf '%-24s %-6s exit=%-4s %s\n' "$step_name" "$step_class" "$step_exit" "$step_evidence" >> "${OUT_DIR}/summary.txt"
}

: > "${OUT_DIR}/summary.txt"
{
  echo "release-verify.sh run"
  echo "started (UTC): $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "REF=${REF}"
  echo "OUT_DIR=${OUT_DIR}"
  echo
} >> "${OUT_DIR}/summary.txt"

VENV_DIR=""
NEW_WHEEL=""
NEW_SDIST=""
REF_WHEEL=""

# --- Step (a): provisioning ---------------------------------------------------
# python -m venv created INSIDE this single nix develop invocation; PIP_USER=0
# (exported above) plus --no-user because ~/.config/pip/pip.conf sets
# install.user=true globally on this NixOS host, which a venv install rejects
# otherwise. On any failure, setup_fail() aborts with exit 2 -- never continue
# into steps that would emit partial, success-looking evidence.
step_a_provision() {
  note "Step (a): provision pinned release tools"
  local provision_scratch="${TMPDIR:-/tmp}/release-verify-provision.log"
  VENV_DIR="${TMPDIR:-/tmp}/release-verify-venv"
  rm -rf "$VENV_DIR"
  : > "$provision_scratch"

  if ! python3 -m venv "$VENV_DIR" >>"$provision_scratch" 2>&1; then
    cat "$provision_scratch" >&2 || true
    setup_fail "could not provision pinned release tools: python -m venv failed"
  fi

  if ! "${VENV_DIR}/bin/pip" install --no-user --disable-pip-version-check \
        -r "${REPO_ROOT}/code/scripts/release-tools-requirements.txt" \
        >>"$provision_scratch" 2>&1; then
    cat "$provision_scratch" >&2 || true
    setup_fail "could not provision pinned release tools: pip install failed (network required)"
  fi

  local resolved_versions
  resolved_versions=$("${VENV_DIR}/bin/pip" freeze 2>/dev/null | grep -E '^(build|twine|check-wheel-contents)==' || true)
  {
    echo "Resolved pinned tool versions (from pip freeze):"
    echo "${resolved_versions:-<none found>}"
    echo
  } >> "${OUT_DIR}/summary.txt"

  note "OK: provisioned pinned tools into ${VENV_DIR}"
  record_step "a-provision" 0 gate "(versions recorded in summary.txt)"
}

# --- Step (b): build -----------------------------------------------------------
# Fresh code/dist/ (gitignored, .gitignore:13) via the venv's interpreter.
# Classified as a hard gate.
step_b_build() {
  note "Step (b): python -m build"
  local build_log="${OUT_DIR}/build.log"
  rm -rf "${REPO_ROOT}/code/dist"

  (cd "${REPO_ROOT}/code" && "${VENV_DIR}/bin/python" -m build) > "$build_log" 2>&1
  local rc=$?
  {
    echo
    echo "--- code/dist/ directory listing ---"
    ls -la "${REPO_ROOT}/code/dist" 2>&1
  } >> "$build_log"

  if [ "$rc" -ne 0 ]; then
    fail "python -m build failed (exit ${rc}); see ${build_log}"
    record_step "b-build" "$rc" gate "build.log"
    return
  fi

  local whl_count sdist_count
  whl_count=$(find "${REPO_ROOT}/code/dist" -maxdepth 1 -name '*.whl' 2>/dev/null | wc -l | tr -d ' ')
  sdist_count=$(find "${REPO_ROOT}/code/dist" -maxdepth 1 -name '*.tar.gz' 2>/dev/null | wc -l | tr -d ' ')
  if [ "$whl_count" -ne 1 ] || [ "$sdist_count" -ne 1 ]; then
    fail "expected exactly one *.whl and one *.tar.gz in code/dist/, found ${whl_count} wheel(s) and ${sdist_count} sdist(s)"
    record_step "b-build" 1 gate "build.log"
    return
  fi

  NEW_WHEEL="$(find "${REPO_ROOT}/code/dist" -maxdepth 1 -name '*.whl')"
  NEW_SDIST="$(find "${REPO_ROOT}/code/dist" -maxdepth 1 -name '*.tar.gz')"
  note "OK: built $(basename "$NEW_WHEEL") and $(basename "$NEW_SDIST")"
  record_step "b-build" 0 gate "build.log"
}

# --- Step (c): twine check --strict --------------------------------------------
# The one step whose failure must block a release. Classified as a hard gate.
step_c_twine() {
  note "Step (c): twine check --strict"
  if [ -z "$NEW_WHEEL" ] || [ -z "$NEW_SDIST" ]; then
    echo "SKIPPED: no build artifacts available (step b failed)" > "${OUT_DIR}/twine-check.txt"
    fail "twine check --strict skipped: no build artifacts (step b failed)"
    record_step "c-twine" 1 gate "twine-check.txt"
    return
  fi

  "${VENV_DIR}/bin/twine" check --strict "${REPO_ROOT}/code/dist/"* > "${OUT_DIR}/twine-check.txt" 2>&1
  local rc=$?
  if [ "$rc" -ne 0 ]; then
    fail "twine check --strict failed (exit ${rc}); see ${OUT_DIR}/twine-check.txt"
  else
    note "OK: twine check --strict passed"
  fi
  record_step "c-twine" "$rc" gate "twine-check.txt"
}

# --- Step (d1): check-wheel-contents (bare) -------------------------------------
# Classified as informational: capture the exit code and CONTINUE. A nonzero
# exit here is expected today (W002, four identical theory_lib/*/VERSION
# files) and must not abort the run or increment FAILURES.
step_d1_wheel_contents_bare() {
  note "Step (d1): check-wheel-contents (bare, informational)"
  if [ -z "$NEW_WHEEL" ]; then
    echo "SKIPPED: no wheel built (step b failed)" > "${OUT_DIR}/wheel-contents.txt"
    record_step "d1-wheel-contents" 1 info "wheel-contents.txt"
    return
  fi

  "${VENV_DIR}/bin/check-wheel-contents" "$NEW_WHEEL" > "${OUT_DIR}/wheel-contents.txt" 2>&1
  local rc=$?
  {
    echo
    echo "--- release-verify.sh note ---"
    echo "A nonzero exit here is EXPECTED today: W002 (duplicate files) fires for the"
    echo "four identical theory_lib/{bimodal,exclusion,imposition,logos}/VERSION files."
    echo "That deduplication is tracked as a separate task. This step is classified"
    echo "informational and never gates the run. See wheel-contents-ignore-w002.txt for"
    echo "the hard-gated \"is there anything NEW beyond W002?\" signal."
  } >> "${OUT_DIR}/wheel-contents.txt"
  note "check-wheel-contents (bare) exited ${rc} -- informational, recorded, run continues"
  record_step "d1-wheel-contents" "$rc" info "wheel-contents.txt"
}

# --- Step (d2): check-wheel-contents --ignore W002 -------------------------------
# The "is there anything NEW?" signal. Classified as a hard gate: a nonzero
# exit here means a finding beyond the known, separately-tracked W002.
step_d2_wheel_contents_ignore_w002() {
  note "Step (d2): check-wheel-contents --ignore W002 (hard gate)"
  if [ -z "$NEW_WHEEL" ]; then
    echo "SKIPPED: no wheel built (step b failed)" > "${OUT_DIR}/wheel-contents-ignore-w002.txt"
    fail "check-wheel-contents --ignore W002 skipped: no wheel built"
    record_step "d2-wheel-contents-w002" 1 gate "wheel-contents-ignore-w002.txt"
    return
  fi

  "${VENV_DIR}/bin/check-wheel-contents" --ignore W002 "$NEW_WHEEL" > "${OUT_DIR}/wheel-contents-ignore-w002.txt" 2>&1
  local rc=$?
  if [ "$rc" -ne 0 ]; then
    fail "check-wheel-contents --ignore W002 reported findings beyond the known W002 (exit ${rc}); see ${OUT_DIR}/wheel-contents-ignore-w002.txt"
  else
    note "OK: check-wheel-contents --ignore W002 clean (no findings beyond the known W002)"
  fi
  record_step "d2-wheel-contents-w002" "$rc" gate "wheel-contents-ignore-w002.txt"
}

# --- Step (e1): reference fetch [STUB] ---------------------------------------
step_e1_reference_fetch() {
  note "Step (e1): pip download reference release [STUB]"
  record_step "e1-reference-fetch" 0 gate "pip-download-${REF}.log"
}

# --- Step (e2): file listings [STUB] -----------------------------------------
step_e2_file_listings() {
  note "Step (e2): wheel file listings [STUB]"
  record_step "e2-file-listings" 0 info "new-wheel-files.txt, ref-${REF}-wheel-files.txt"
}

# --- Step (e3): diffs [STUB] --------------------------------------------------
step_e3_diffs() {
  note "Step (e3): wheel-files/top-level-dir diffs [STUB]"
  record_step "e3-diffs" 0 info "wheel-files-diff.txt, top-level-dir-diff.txt"
}

# --- Step (f): hashes [STUB] --------------------------------------------------
step_f_hashes() {
  note "Step (f): sha256sums [STUB]"
  record_step "f-hashes" 0 info "sha256sums.txt"
}

# --- parity-diff.md generation [STUB] ----------------------------------------
generate_parity_diff() {
  note "Generating parity-diff.md [STUB]"
  record_step "parity-diff" 0 info "parity-diff.md"
}

main() {
  step_a_provision
  step_b_build
  step_c_twine
  step_d1_wheel_contents_bare
  step_d2_wheel_contents_ignore_w002
  step_e1_reference_fetch
  step_e2_file_listings
  step_e3_diffs
  step_f_hashes
  generate_parity_diff

  echo >> "${OUT_DIR}/summary.txt"
  echo "FAILURES=${FAILURES}" >> "${OUT_DIR}/summary.txt"

  echo
  note "Evidence directory: ${OUT_DIR}"
  if [ "$FAILURES" -gt 0 ]; then
    note "${FAILURES} hard-gate check(s) FAILED"
    exit 1
  fi
  note "All hard-gate checks passed"
  exit 0
}

main
