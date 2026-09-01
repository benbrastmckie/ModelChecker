#!/usr/bin/env python3
"""Peak-RSS-per-xdist-worker telemetry sampler for the Python 3.12 `general-tests` matrix leg
(see `.github/workflows/tests.yml`'s 3.12-gated telemetry step and
`code/docs/core/TESTING_GUIDE.md` section 8.11 for the incident this instruments).

**This is instrumentation only. It does not fix, diagnose, or claim a root cause for the D
incident** (two occurrences of a Python-3.12-only xdist worker crash, `[gwN] node down: Not
properly terminated`, both with a ~2-17 minute silent gap before detection and no
`Fatal Python error`/segfault/faulthandler stack dump in the captured log). Three hypotheses
remain live and unconfirmed: (1) memory exhaustion on the runner (this sampler's target),
(2) a Python-3.12-specific Z3/`z3-solver` ABI incompatibility unrelated to memory, (3) an
xdist/execnet worker-communication fault under load. This module makes hypothesis (1)
falsifiable with data instead of log archaeology; it does not favor it. It is removable once
the hypothesis resolves either way -- delete this file, its test module, and the workflow step
that invokes it.

**Implementation choice, stated per the plan's requirement**: `/proc/<pid>/status` is read
directly rather than via `psutil`. The Python 3.12 leg (like every leg) targets
`ubuntu-latest`, where `/proc` is always present, so a `/proc`-only implementation gets full
functionality without adding a new CI dependency (`psutil` is not currently installed in either
CI toolchain's dependency list) -- this mirrors `unstable_watch_classify.py`'s stdlib-only
constraint. If a future non-Linux leg needs this, that is the point to reconsider `psutil`, not
before.

**What the sampler records, and what it deliberately does not**: absolute peak resident-set
size in KB, per worker pid and in aggregate (the max of each sample's per-worker total), plus
the effective `-n` worker count the step passed in and the sample count/interval actually used.
Each pid is additionally attributed, best-effort, to its `PYTEST_XDIST_WORKER` id (e.g. `gw2`)
read from `/proc/<pid>/environ` -- the summary carries this as `pid_to_worker` (pid -> `gwN` or
`null`) and `per_worker_id_peak_kb` (max peak RSS across every pid that ever carried a given
`gwN`, so a worker that dies and is replaced mid-run still attributes both pids' peaks to the
same worker id). Attribution is best-effort and never fatal: a pid whose environ is unreadable
(process raced away, permission-restricted) or that is not running under xdist at all simply
carries `null` in `pid_to_worker` rather than raising or being dropped from the record. It never
applies a threshold (there is no encoded "16GB" or any other ceiling anywhere in this module) --
a reading with no ceiling to compare it against is not evidence, so any ceiling judgement is left
to whoever reads the emitted JSON later, informed by the actual runner spec at the time.

Stdlib only. Importing this module has no side effects (no polling loop, no file writes, no
`sys.exit`) -- all of that happens only under `if __name__ == "__main__":`, via `main()`. This
mirrors `.github/scripts/unstable_watch_classify.py`'s import-is-inert contract, which
`code/tests/ci/test_unstable_watch_classifier.py` established as the in-repo precedent for a
testable CI helper script.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import time
from pathlib import Path

DEFAULT_PROC_ROOT = Path("/proc")
DEFAULT_INTERVAL_S = 2.0

_VM_RSS_RE = re.compile(r"^VmRSS:\s*(\d+)\s*kB", re.MULTILINE)
_PPID_RE = re.compile(r"^PPid:\s*(\d+)", re.MULTILINE)


def parse_vm_rss_kb(status_text: str) -> int | None:
    """Extract the `VmRSS:` value (in KB) from `/proc/<pid>/status`-shaped text. Returns
    `None` when no `VmRSS:` line is present (e.g. a kernel thread or a process that exited
    between two reads of the same file -- the file can go stale mid-read on a real /proc)."""
    m = _VM_RSS_RE.search(status_text)
    return int(m.group(1)) if m else None


def _parse_ppid(status_text: str) -> int | None:
    m = _PPID_RE.search(status_text)
    return int(m.group(1)) if m else None


def read_vm_rss_kb(proc_root: Path, pid: int) -> int | None:
    """Read `VmRSS` for `pid` under `proc_root` (normally `/proc`, a synthetic directory in
    tests). Returns `None` if the process has no status file (already exited -- a normal race,
    not an error) or has no `VmRSS` line."""
    status_path = proc_root / str(pid) / "status"
    try:
        text = status_path.read_text()
    except (FileNotFoundError, ProcessLookupError, PermissionError):
        return None
    return parse_vm_rss_kb(text)


def parse_xdist_worker_id(environ_bytes: bytes) -> str | None:
    """Extract the `PYTEST_XDIST_WORKER` value (e.g. `"gw2"`) from `/proc/<pid>/environ`-shaped
    NUL-separated `KEY=VALUE\\0` byte content. `xdist/remote.py` sets this variable inside each
    worker subprocess's own environment before it starts executing tests, alongside a sibling
    `PYTEST_XDIST_WORKER_COUNT` variable -- the split-on-`\\0` then exact-key-match (not
    `startswith`) here is deliberate so `PYTEST_XDIST_WORKER_COUNT` can never satisfy a match
    intended for `PYTEST_XDIST_WORKER`. Returns `None` when the key is absent. Decodes with
    `errors="replace"` so non-UTF8 bytes elsewhere in the environ blob cannot raise."""
    for entry in environ_bytes.split(b"\0"):
        if not entry:
            continue
        key, sep, value = entry.partition(b"=")
        if sep and key == b"PYTEST_XDIST_WORKER":
            return value.decode("utf-8", errors="replace")
    return None


def read_xdist_worker_id(proc_root: Path, pid: int) -> str | None:
    """Read `pid`'s `PYTEST_XDIST_WORKER` id under `proc_root` (normally `/proc`). Mirrors
    `read_vm_rss_kb`'s tolerance exactly: a missing pid directory, an already-exited process, or
    a permission-restricted environ file all return `None` rather than raising -- these are the
    normal shape of reading a live `/proc`, not error conditions. Best-effort attribution: a
    `None` result means the caller degrades to an untagged pid, never a crash."""
    environ_path = proc_root / str(pid) / "environ"
    try:
        data = environ_path.read_bytes()
    except (FileNotFoundError, ProcessLookupError, PermissionError):
        return None
    return parse_xdist_worker_id(data)


def _all_pids(proc_root: Path) -> list[int]:
    if not proc_root.is_dir():
        return []
    pids = []
    for entry in proc_root.iterdir():
        if entry.is_dir() and entry.name.isdigit():
            pids.append(int(entry.name))
    return pids


def discover_descendant_pids(proc_root: Path, root_pid: int) -> set[int]:
    """Return every pid under `proc_root` that is a descendant (child, grandchild, ...) of
    `root_pid`, by reading each candidate's `PPid:` line. `root_pid` itself is excluded --
    callers want the *worker* processes, not the pytest controller that spawned them."""
    child_map: dict[int, list[int]] = {}
    for pid in _all_pids(proc_root):
        status_path = proc_root / str(pid) / "status"
        try:
            text = status_path.read_text()
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            continue
        ppid = _parse_ppid(text)
        if ppid is None:
            continue
        child_map.setdefault(ppid, []).append(pid)

    descendants: set[int] = set()
    frontier = [root_pid]
    while frontier:
        current = frontier.pop()
        for child in child_map.get(current, []):
            if child not in descendants:
                descendants.add(child)
                frontier.append(child)
    return descendants


def sample_once(proc_root: Path, root_pid: int) -> dict[int, int]:
    """Discover `root_pid`'s current descendants and read each one's VmRSS. A descendant that
    raced away between discovery and read is silently omitted from the returned sample rather
    than recorded as 0 (a dead worker has no RSS to report, not zero RSS)."""
    sample: dict[int, int] = {}
    for pid in discover_descendant_pids(proc_root, root_pid):
        rss = read_vm_rss_kb(proc_root, pid)
        if rss is not None:
            sample[pid] = rss
    return sample


class PeakTracker:
    """Accumulates `sample_once()` results over time, tracking both the peak RSS any single
    worker pid ever reached and the peak *aggregate* (summed-across-currently-alive-workers)
    RSS at any single sample instant. A worker that dies and is replaced mid-run (exactly the
    D scenario) contributes its own peak under its own pid -- pids are never conflated or
    overwritten by a later, unrelated pid.

    `record()`'s optional `worker_ids` parameter (pid -> `gwN`/`None`) attributes each pid to
    the xdist worker id it belongs to (see `parse_xdist_worker_id`/`read_xdist_worker_id`
    above). Attribution is best-effort and additive: the first non-`None` id seen for a pid is
    kept permanently and never overwritten by a later `None` (an environ read that later races
    away must not blank out an id already established), and a pid with no id information at all
    degrades to an untagged (`None`) entry rather than being dropped from the record."""

    def __init__(self) -> None:
        self.per_pid_peak_kb: dict[int, int] = {}
        self.pid_to_worker: dict[int, str | None] = {}
        self.aggregate_peak_kb: int = 0
        self.sample_count: int = 0

    def record(self, sample: dict[int, int], worker_ids: dict[int, str | None] | None = None) -> None:
        self.sample_count += 1
        worker_ids = worker_ids or {}
        for pid, rss in sample.items():
            if rss > self.per_pid_peak_kb.get(pid, 0):
                self.per_pid_peak_kb[pid] = rss
            worker_id = worker_ids.get(pid)
            if pid not in self.pid_to_worker:
                self.pid_to_worker[pid] = worker_id
            elif self.pid_to_worker[pid] is None and worker_id is not None:
                self.pid_to_worker[pid] = worker_id
        total = sum(sample.values())
        if total > self.aggregate_peak_kb:
            self.aggregate_peak_kb = total

    def summary(self, workers: int, interval_s: float) -> dict:
        """Compact, JSON-serializable summary. Deliberately carries no threshold, ratio, or
        ceiling of any kind (see this module's docstring) -- only absolute KB figures, the
        worker count the caller supplied, and sampling metadata."""
        per_worker_peak_kb = max(self.per_pid_peak_kb.values(), default=0)
        per_worker_id_peak_kb: dict[str, int] = {}
        for pid, worker_id in self.pid_to_worker.items():
            if worker_id is None:
                continue
            pid_peak = self.per_pid_peak_kb.get(pid, 0)
            if pid_peak > per_worker_id_peak_kb.get(worker_id, 0):
                per_worker_id_peak_kb[worker_id] = pid_peak
        return {
            "workers": workers,
            "interval_s": interval_s,
            "sample_count": self.sample_count,
            "distinct_worker_pids_observed": len(self.per_pid_peak_kb),
            "per_worker_peak_kb": per_worker_peak_kb,
            "aggregate_peak_kb": self.aggregate_peak_kb,
            "per_pid_peak_kb": {str(pid): rss for pid, rss in self.per_pid_peak_kb.items()},
            "pid_to_worker": {str(pid): worker_id for pid, worker_id in self.pid_to_worker.items()},
            "per_worker_id_peak_kb": per_worker_id_peak_kb,
        }


def _process_alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def _sample_worker_ids(proc_root: Path, pids) -> dict[int, str | None]:
    """Read `PYTEST_XDIST_WORKER` for each pid in `pids` via `read_xdist_worker_id`. Best
    effort: a pid without a readable/tagged environ contributes `None`, never an exception."""
    return {pid: read_xdist_worker_id(proc_root, pid) for pid in pids}


def run(root_pid: int, workers: int, interval_s: float = DEFAULT_INTERVAL_S,
        proc_root: Path = DEFAULT_PROC_ROOT) -> dict:
    """Poll until `root_pid` exits, sampling its descendants' VmRSS (and, best-effort, each
    descendant's `PYTEST_XDIST_WORKER` id) every `interval_s` seconds, then return the
    tracker's summary. Never raises on a worker dying mid-poll -- that is the normal xdist
    worker-replacement path, not an error condition here."""
    tracker = PeakTracker()
    while _process_alive(root_pid):
        sample = sample_once(proc_root, root_pid)
        tracker.record(sample, worker_ids=_sample_worker_ids(proc_root, sample.keys()))
        time.sleep(interval_s)
    # One final sample in case the root died between the last sleep and this check, but a
    # descendant snapshot is still readable (best-effort; sample_once already tolerates a
    # fully-gone process by omitting it).
    sample = sample_once(proc_root, root_pid)
    tracker.record(sample, worker_ids=_sample_worker_ids(proc_root, sample.keys()))
    return tracker.summary(workers=workers, interval_s=interval_s)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root-pid", type=int, required=True,
                         help="PID of the pytest controller process to sample descendants of.")
    parser.add_argument("--workers", type=int, required=True,
                         help="The -n worker count this run was launched with (recorded "
                              "verbatim in the summary; not inferred from live process count, "
                              "which is transiently unstable during worker replacement).")
    parser.add_argument("--interval", type=float, default=DEFAULT_INTERVAL_S,
                         help=f"Sampling interval in seconds (default {DEFAULT_INTERVAL_S}).")
    parser.add_argument("--output", type=Path, default=None,
                         help="Path to write the JSON summary to. If omitted, prints to stdout "
                              "only.")
    args = parser.parse_args(argv)

    summary = run(args.root_pid, args.workers, args.interval)

    text = json.dumps(summary, indent=2)
    if args.output is not None:
        args.output.write_text(text + "\n")
    print(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
