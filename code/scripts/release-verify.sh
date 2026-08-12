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

# setup_fail <message> [label]: a required step (provisioning or reference
# fetch) could not run at all. Never continue past this into steps that would
# produce a partial, success-looking evidence set. Exits 2 (distinct from the
# hard-gate-failure exit 1). label defaults to "SETUP FAILED" (provisioning);
# pass "REFERENCE FETCH FAILED" for the step (e1) reference-download path.
setup_fail() {
  local msg="$1"
  local label="${2:-SETUP FAILED}"
  echo "[release-verify] ${label}: ${msg}" >&2
  {
    echo "${label}: ${msg}"
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
TOOL_VERSIONS=""

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
  TOOL_VERSIONS="$resolved_versions"
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

# --- Step (e1): reference fetch -------------------------------------------------
# A missing reference must not silently degrade into a diff-free evidence set:
# on failure this is a setup_fail (exit 2), same class as provisioning.
step_e1_reference_fetch() {
  note "Step (e1): pip download reference release model-checker==${REF}"
  local ref_dir="${TMPDIR:-/tmp}/release-verify-ref-download"
  rm -rf "$ref_dir"
  mkdir -p "$ref_dir"

  if ! "${VENV_DIR}/bin/pip" download --no-deps "model-checker==${REF}" -d "$ref_dir" \
        > "${OUT_DIR}/pip-download-${REF}.log" 2>&1; then
    cat "${OUT_DIR}/pip-download-${REF}.log" >&2 || true
    setup_fail "could not download model-checker==${REF} (network required)" "REFERENCE FETCH FAILED"
  fi

  REF_WHEEL="$(find "$ref_dir" -maxdepth 1 -name '*.whl' | head -1)"
  if [ -z "$REF_WHEEL" ]; then
    setup_fail "reference download for model-checker==${REF} produced no wheel file" "REFERENCE FETCH FAILED"
  fi

  note "OK: downloaded reference $(basename "$REF_WHEEL")"
  record_step "e1-reference-fetch" 0 gate "pip-download-${REF}.log"
}

# --- Step (e2): file listings -----------------------------------------------------
# Sorted full file listing of each wheel via the venv interpreter's zipfile
# module -- avoids depending on unzip/`check-wheel-contents`-adjacent tools
# that may be absent from the devShell.
step_e2_file_listings() {
  note "Step (e2): wheel file listings"
  if [ -z "$NEW_WHEEL" ] || [ -z "$REF_WHEEL" ]; then
    echo "SKIPPED: missing wheel(s)" > "${OUT_DIR}/new-wheel-files.txt"
    echo "SKIPPED: missing wheel(s)" > "${OUT_DIR}/ref-${REF}-wheel-files.txt"
    fail "wheel file listings skipped: missing new or reference wheel"
    record_step "e2-file-listings" 1 info "new-wheel-files.txt, ref-${REF}-wheel-files.txt"
    return
  fi

  "${VENV_DIR}/bin/python" -c '
import sys, zipfile
zf = zipfile.ZipFile(sys.argv[1])
for name in sorted(zf.namelist()):
    print("./" + name)
' "$NEW_WHEEL" > "${OUT_DIR}/new-wheel-files.txt"
  "${VENV_DIR}/bin/python" -c '
import sys, zipfile
zf = zipfile.ZipFile(sys.argv[1])
for name in sorted(zf.namelist()):
    print("./" + name)
' "$REF_WHEEL" > "${OUT_DIR}/ref-${REF}-wheel-files.txt"

  note "OK: wrote new-wheel-files.txt and ref-${REF}-wheel-files.txt"
  record_step "e2-file-listings" 0 info "new-wheel-files.txt, ref-${REF}-wheel-files.txt"
}

# --- Step (e3): diffs -----------------------------------------------------------
# Unified diff of the two full file listings, and of the two maxdepth-2
# top-level directory sets. Both classified informational: a nonempty diff
# between a 1.3.0 build and a 1.2.12 release is expected and must never gate.
step_e3_diffs() {
  note "Step (e3): wheel-files/top-level-dir diffs"
  if [ -z "$NEW_WHEEL" ] || [ -z "$REF_WHEEL" ]; then
    echo "SKIPPED: missing wheel(s)" > "${OUT_DIR}/wheel-files-diff.txt"
    echo "SKIPPED: missing wheel(s)" > "${OUT_DIR}/top-level-dir-diff.txt"
    fail "diffs skipped: missing new or reference wheel"
    record_step "e3-diffs" 1 info "wheel-files-diff.txt, top-level-dir-diff.txt"
    return
  fi

  diff -u "${OUT_DIR}/ref-${REF}-wheel-files.txt" "${OUT_DIR}/new-wheel-files.txt" \
    > "${OUT_DIR}/wheel-files-diff.txt"
  # diff exits 1 when inputs differ -- expected and informational; never fail here.

  local extract_new="${TMPDIR:-/tmp}/release-verify-extract-new"
  local extract_ref="${TMPDIR:-/tmp}/release-verify-extract-ref"
  local ref_dirs="${TMPDIR:-/tmp}/release-verify-ref-dirs.txt"
  local new_dirs="${TMPDIR:-/tmp}/release-verify-new-dirs.txt"
  rm -rf "$extract_new" "$extract_ref"
  mkdir -p "$extract_new" "$extract_ref"
  "${VENV_DIR}/bin/python" -m zipfile -e "$NEW_WHEEL" "$extract_new" >/dev/null 2>&1
  "${VENV_DIR}/bin/python" -m zipfile -e "$REF_WHEEL" "$extract_ref" >/dev/null 2>&1

  (cd "$extract_ref" && find . -maxdepth 2 -type d | sort) > "$ref_dirs"
  (cd "$extract_new" && find . -maxdepth 2 -type d | sort) > "$new_dirs"
  diff -u "$ref_dirs" "$new_dirs" > "${OUT_DIR}/top-level-dir-diff.txt"

  note "OK: wrote wheel-files-diff.txt and top-level-dir-diff.txt (nonempty diff expected, informational)"
  record_step "e3-diffs" 0 info "wheel-files-diff.txt, top-level-dir-diff.txt"
}

# --- Step (f): hashes -------------------------------------------------------------
step_f_hashes() {
  note "Step (f): sha256sums"
  {
    [ -n "$NEW_WHEEL" ] && sha256sum "$NEW_WHEEL"
    [ -n "$NEW_SDIST" ] && sha256sum "$NEW_SDIST"
    [ -n "$REF_WHEEL" ] && sha256sum "$REF_WHEEL"
  } > "${OUT_DIR}/sha256sums.txt"

  local line_count
  line_count=$(wc -l < "${OUT_DIR}/sha256sums.txt" | tr -d ' ')
  if [ "$line_count" -ne 3 ]; then
    fail "sha256sums.txt has ${line_count} line(s), expected exactly 3 (new wheel, new sdist, reference wheel)"
    record_step "f-hashes" 1 info "sha256sums.txt"
    return
  fi

  note "OK: wrote sha256sums.txt (3 lines)"
  record_step "f-hashes" 0 info "sha256sums.txt"
}

# --- parity-diff.md generation -----------------------------------------------------
# Evidentiary report: artifact identity, file-count summary, and a reviewer
# prompt for the Classified Differences section. Never fabricates a
# classification verdict the script cannot compute; never presents this diff
# as a release gate.
generate_parity_diff() {
  note "Generating parity-diff.md"
  local parity_file="${OUT_DIR}/parity-diff.md"
  local new_version="unknown"
  local sha_new_wheel="" sha_new_sdist="" sha_ref_wheel=""
  local new_count="0" ref_count="0"

  if [ -n "$NEW_WHEEL" ]; then
    new_version="$(basename "$NEW_WHEEL" | sed -E 's/^model_checker-([^-]+)-.*/\1/')"
  fi
  if [ -f "${OUT_DIR}/sha256sums.txt" ]; then
    [ -n "$NEW_WHEEL" ] && sha_new_wheel=$(grep -F "$(basename "$NEW_WHEEL")" "${OUT_DIR}/sha256sums.txt" | awk '{print $1}')
    [ -n "$NEW_SDIST" ] && sha_new_sdist=$(grep -F "$(basename "$NEW_SDIST")" "${OUT_DIR}/sha256sums.txt" | awk '{print $1}')
    [ -n "$REF_WHEEL" ] && sha_ref_wheel=$(grep -F "$(basename "$REF_WHEEL")" "${OUT_DIR}/sha256sums.txt" | awk '{print $1}')
  fi
  [ -f "${OUT_DIR}/new-wheel-files.txt" ] && new_count=$(wc -l < "${OUT_DIR}/new-wheel-files.txt" | tr -d ' ')
  [ -f "${OUT_DIR}/ref-${REF}-wheel-files.txt" ] && ref_count=$(wc -l < "${OUT_DIR}/ref-${REF}-wheel-files.txt" | tr -d ' ')

  {
    echo "# Wheel Parity Diff: model_checker ${new_version} vs. published model-checker ${REF}"
    echo
    echo "**Run date (UTC)**: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
    echo "**Environment**: \`nix develop\` (flake devShell) with an isolated venv created in"
    echo "\`\$TMPDIR\`, provisioned from \`code/scripts/release-tools-requirements.txt\`;"
    echo "\`flake.nix\` was not modified."
    echo
    echo "**Pinned tool versions**:"
    echo '```'
    echo "${TOOL_VERSIONS:-<unavailable>}"
    echo '```'
    echo
    echo "## Artifact Identity"
    echo
    echo "| Artifact | Name | SHA256 |"
    echo "|----------|------|--------|"
    echo "| New wheel | \`$(basename "${NEW_WHEEL:-<not built>}")\` | \`${sha_new_wheel:-<unavailable>}\` |"
    echo "| New sdist | \`$(basename "${NEW_SDIST:-<not built>}")\` | \`${sha_new_sdist:-<unavailable>}\` |"
    echo "| Reference wheel | \`$(basename "${REF_WHEEL:-<not downloaded>}")\` (from \`pip download --no-deps model-checker==${REF}\`) | \`${sha_ref_wheel:-<unavailable>}\` |"
    echo
    echo "Full hash listing: \`sha256sums.txt\` in this directory."
    echo
    echo "## File Count Summary"
    echo
    echo "| | Files |"
    echo "|---|---|"
    echo "| Reference wheel (${REF}) | ${ref_count} |"
    echo "| New wheel (${new_version}) | ${new_count} |"
    echo
    echo "## Classified Differences"
    echo
    echo "This script computes the raw file-listing and top-level-directory diffs"
    echo "(\`wheel-files-diff.txt\`, \`top-level-dir-diff.txt\`) but does NOT classify them --"
    echo "classification of each grouping (intended addition/removal vs. an unexpected"
    echo "regression) is a **human** step the reviewer performs by reading those two files"
    echo "against the repository's git history."
    echo
    echo "## Conclusion"
    echo
    echo "This diff is **evidentiary, not a release gate**. Byte-identity against a prior"
    echo "published release is never a pass condition -- \`twine check --strict\` (see"
    echo "\`twine-check.txt\`) and \`check-wheel-contents --ignore W002\` (see"
    echo "\`wheel-contents-ignore-w002.txt\`) are this run's actual hard gates."
    echo
    echo "## Evidence Files (this directory)"
    echo
    echo "- \`build.log\` -- full \`python -m build\` output plus \`code/dist/\` listing."
    echo "- \`twine-check.txt\` -- \`twine check --strict code/dist/*\` output."
    echo "- \`wheel-contents.txt\` -- bare \`check-wheel-contents\` output (W002 expected)."
    echo "- \`wheel-contents-ignore-w002.txt\` -- \`check-wheel-contents --ignore W002\` output."
    echo "- \`pip-download-${REF}.log\` -- \`pip download --no-deps model-checker==${REF}\` output."
    echo "- \`sha256sums.txt\` -- SHA256 of the new wheel, new sdist, and reference wheel."
    echo "- \`new-wheel-files.txt\` / \`ref-${REF}-wheel-files.txt\` -- sorted full file listings."
    echo "- \`top-level-dir-diff.txt\` -- \`diff\` of maxdepth-2 directory listings."
    echo "- \`wheel-files-diff.txt\` -- full \`diff\` of the sorted file listings."
    echo "- \`summary.txt\` -- per-step status ledger."
  } > "$parity_file"

  note "OK: wrote parity-diff.md"
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
