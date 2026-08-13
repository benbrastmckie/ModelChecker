#!/usr/bin/env bash
# verify-installed-cli.sh
#
# Local podman debug loop reproducing CI's installed-wheel CLI verification (see the R4 handoff
# in specs/163_full_cli_suite_against_installed_wheel/reports/01_installed-cli-verification.md
# for the exact `verify-install` GitHub Actions job this mirrors -- not implemented here, since
# .github/workflows/release.yml is owned by a separate task).
#
# Mounts the repo read-only into a slim distro image, creates a venv, pip-installs the built
# wheel plus pytest, and runs the full `tests/cli/` suite under both MODELCHECKER_CLI_TEST_MODE
# values that require a real installed package (`installed` and `installed-module`).
#
# A NixOS host with only `nix` on PATH is a deliberately unsupported fallback: a Nix FHS sandbox
# was evaluated and rejected as a substitute for this script (see the research report's F5/D2) --
# it shares this host's glibc, leaks host state, and cannot move to CI. This script requires
# podman and fails fast, loudly, and non-zero when it is absent, naming the exact host change
# rather than silently degrading to a weaker check.
#
# Usage:
#   bash code/scripts/verify-installed-cli.sh [IMAGE]
#
#   IMAGE   Container image to run the suite in. Default: python:3.11-slim.
#           Examples: python:3.10-slim, python:3.12-slim, ubuntu:20.04 (apt-based Python setup
#           not handled by this script for non-python:*-slim images).
#
# Exit codes:
#   0  both modes passed
#   1  podman is not on PATH (prints the required NixOS config change)
#   2  no wheel found in code/dist/ (prints the build command to run)
#   3  the containerized pytest run itself failed (podman propagates the container's exit code)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CODE_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
IMAGE="${1:-python:3.11-slim}"

if ! command -v podman >/dev/null 2>&1; then
    echo "ERROR: podman is not on PATH." >&2
    echo "" >&2
    echo "This script requires podman for the local container debug loop (a Nix FHS sandbox is" >&2
    echo "not an acceptable substitute -- see the research report's F5/D2)." >&2
    echo "" >&2
    echo "Required host action (NixOS):" >&2
    echo "  Add to your NixOS configuration:" >&2
    echo "    virtualisation.podman.enable = true;" >&2
    echo "  Then rebuild: sudo nixos-rebuild switch" >&2
    exit 1
fi

WHEEL="$(find "${CODE_DIR}/dist" -maxdepth 1 -name '*.whl' -newer "${CODE_DIR}/pyproject.toml" 2>/dev/null | sort | tail -n1 || true)"
if [ -z "${WHEEL}" ]; then
    echo "ERROR: no wheel newer than code/pyproject.toml found in code/dist/." >&2
    echo "" >&2
    echo "Build one first:" >&2
    echo "  cd ${CODE_DIR} && rm -rf dist build *.egg-info && python -m build" >&2
    exit 2
fi

echo "Using wheel: $(basename "${WHEEL}")"
echo "Using image: ${IMAGE}"
echo ""

STATUS=0
for MODE in installed installed-module; do
    echo "=== MODELCHECKER_CLI_TEST_MODE=${MODE} (${IMAGE}) ==="
    if ! podman run --rm -v "${CODE_DIR}:/w/code:ro" -w /w/code "${IMAGE}" bash -lc "
        set -euo pipefail
        python -m venv /v
        . /v/bin/activate
        pip install --quiet --upgrade pip
        pip install --quiet /w/code/dist/$(basename "${WHEEL}") pytest
        MODELCHECKER_CLI_TEST_MODE=${MODE} pytest tests/cli/ -v
    "; then
        echo "FAILED: MODELCHECKER_CLI_TEST_MODE=${MODE} did not pass in ${IMAGE}" >&2
        STATUS=3
    fi
    echo ""
done

exit "${STATUS}"
