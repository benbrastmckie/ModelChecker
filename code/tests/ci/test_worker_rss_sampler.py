"""Unit tests for `.github/scripts/worker_rss_sample.py`, the peak-RSS-per-xdist-worker
telemetry sampler (see `code/docs/core/TESTING_GUIDE.md` section 8.11 for the D incident this
instruments, and this module's own docstring for the instrumentation-only, root-cause-open
framing).

All tests here are hermetic: they drive the module's pure parsing/discovery/tracking logic
against synthetic `/proc/<pid>/status`-shaped fixture files written under `tmp_path`, never
against live processes -- so this suite runs identically on any host, including one where no
process happens to be named the way a live-process test would need. Mirrors the extraction
precedent in `.github/scripts/unstable_watch_classify.py` +
`code/tests/ci/test_unstable_watch_classifier.py`: importing the sampler module has no side
effects (no polling loop, no file writes, no `sys.exit`) until `main()` runs it under
`if __name__ == "__main__":`.

Skip guard mirrors `test_workflow_parity.py`'s `_MISSING_REPO_ROOT_FILES` block: under
`nix flake check`'s `checks.default` derivation, `src = ./code` means the sandboxed build has no
repo root at all, so `.github/` is structurally absent there.
"""

from __future__ import annotations

import importlib.util
import json
import re
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
TESTS_YML = REPO_ROOT / ".github" / "workflows" / "tests.yml"
FLAKE_NIX = REPO_ROOT / "flake.nix"
SAMPLER_SCRIPT = REPO_ROOT / ".github" / "scripts" / "worker_rss_sample.py"

_MISSING_REPO_ROOT_FILES = [p for p in (TESTS_YML, FLAKE_NIX) if not p.exists()]
if _MISSING_REPO_ROOT_FILES:
    pytest.skip(
        "Repo-root files not present in this sandbox (expected under `nix flake check`'s "
        "checks.default, whose `src = ./code` excludes the repo root): "
        + ", ".join(str(p) for p in _MISSING_REPO_ROOT_FILES)
        + ". This guard runs in .github/workflows/tests.yml's general-tests job instead, where "
        "actions/checkout@v4 provides the full repository.",
        allow_module_level=True,
    )


def _load_sampler():
    """Load `.github/scripts/worker_rss_sample.py` by absolute path. Before the GREEN step
    lands the script, this raises a clear FileNotFoundError naming the missing path at
    collection time -- the correctly-named RED failure."""
    spec = importlib.util.spec_from_file_location("worker_rss_sample", SAMPLER_SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


sampler = _load_sampler()


def _write_proc_entry(proc_root: Path, pid: int, ppid: int, vm_rss_kb: int | None):
    """Write a synthetic `/proc/<pid>/status` file. `vm_rss_kb=None` omits the VmRSS line
    entirely (mirrors a zombie/kernel-thread process that has no resident memory line)."""
    d = proc_root / str(pid)
    d.mkdir(parents=True, exist_ok=True)
    lines = [
        f"Name:\tpytest\n",
        f"Pid:\t{pid}\n",
        f"PPid:\t{ppid}\n",
    ]
    if vm_rss_kb is not None:
        lines.append(f"VmRSS:\t{vm_rss_kb} kB\n")
    (d / "status").write_text("".join(lines))


def _write_proc_environ(proc_root: Path, pid: int, pairs: list[tuple[bytes, bytes]]):
    """Write a synthetic `/proc/<pid>/environ` file: NUL-separated `KEY=VALUE\\0` byte content,
    mirroring the real kernel-exposed format. `xdist/remote.py:416-418` sets
    `PYTEST_XDIST_WORKER` (e.g. `gw2`) and `PYTEST_XDIST_WORKER_COUNT` (e.g. `4`) inside each
    worker subprocess's own environment before it begins executing tests -- this fixture mirrors
    that shape byte-for-byte, including the exact-key collision risk between the two variable
    names (see `TestParseXdistWorkerId.test_not_confused_by_worker_count_prefix` below)."""
    d = proc_root / str(pid)
    d.mkdir(parents=True, exist_ok=True)
    content = b"".join(key + b"=" + value + b"\0" for key, value in pairs)
    (d / "environ").write_bytes(content)


class TestParseVmRss:
    def test_parses_standard_status_text(self):
        text = "Name:\tpytest\nVmPeak:\t 200000 kB\nVmRSS:\t   123456 kB\nVmHWM:\t 130000 kB\n"
        assert sampler.parse_vm_rss_kb(text) == 123456

    def test_returns_none_when_no_vmrss_line(self):
        text = "Name:\tpytest\nPid:\t42\n"
        assert sampler.parse_vm_rss_kb(text) is None

    def test_tolerates_extra_whitespace(self):
        text = "VmRSS:      42   kB\n"
        assert sampler.parse_vm_rss_kb(text) == 42


class TestReadVmRssKb:
    def test_reads_existing_pid(self, tmp_path):
        _write_proc_entry(tmp_path, pid=100, ppid=1, vm_rss_kb=5000)
        assert sampler.read_vm_rss_kb(tmp_path, 100) == 5000

    def test_missing_pid_returns_none(self, tmp_path):
        # No entry written for pid 999 -- simulates a worker that exited between discovery
        # and read, a normal race this function must not raise on.
        assert sampler.read_vm_rss_kb(tmp_path, 999) is None

    def test_pid_with_no_vmrss_line_returns_none(self, tmp_path):
        _write_proc_entry(tmp_path, pid=101, ppid=1, vm_rss_kb=None)
        assert sampler.read_vm_rss_kb(tmp_path, 101) is None


class TestDiscoverDescendantPids:
    def test_finds_direct_children(self, tmp_path):
        _write_proc_entry(tmp_path, pid=1, ppid=0, vm_rss_kb=1000)
        _write_proc_entry(tmp_path, pid=2, ppid=1, vm_rss_kb=2000)
        _write_proc_entry(tmp_path, pid=3, ppid=1, vm_rss_kb=3000)
        found = sampler.discover_descendant_pids(tmp_path, root_pid=1)
        assert found == {2, 3}

    def test_finds_grandchildren(self, tmp_path):
        _write_proc_entry(tmp_path, pid=1, ppid=0, vm_rss_kb=1000)
        _write_proc_entry(tmp_path, pid=2, ppid=1, vm_rss_kb=2000)
        _write_proc_entry(tmp_path, pid=4, ppid=2, vm_rss_kb=4000)
        found = sampler.discover_descendant_pids(tmp_path, root_pid=1)
        assert found == {2, 4}

    def test_unrelated_process_not_included(self, tmp_path):
        _write_proc_entry(tmp_path, pid=1, ppid=0, vm_rss_kb=1000)
        _write_proc_entry(tmp_path, pid=2, ppid=1, vm_rss_kb=2000)
        _write_proc_entry(tmp_path, pid=50, ppid=0, vm_rss_kb=9999)
        found = sampler.discover_descendant_pids(tmp_path, root_pid=1)
        assert found == {2}

    def test_no_descendants_returns_empty_set(self, tmp_path):
        _write_proc_entry(tmp_path, pid=1, ppid=0, vm_rss_kb=1000)
        assert sampler.discover_descendant_pids(tmp_path, root_pid=1) == set()


class TestSampleOnce:
    def test_reads_rss_for_every_discovered_descendant(self, tmp_path):
        _write_proc_entry(tmp_path, pid=1, ppid=0, vm_rss_kb=1000)
        _write_proc_entry(tmp_path, pid=2, ppid=1, vm_rss_kb=50000)
        _write_proc_entry(tmp_path, pid=3, ppid=1, vm_rss_kb=60000)
        sample = sampler.sample_once(tmp_path, root_pid=1)
        assert sample == {2: 50000, 3: 60000}

    def test_skips_a_descendant_that_raced_away(self, tmp_path):
        # discover_descendant_pids finds pid 2 via its status file, but sample_once's own
        # read races a process exit for pid 3 (no status file at all) -- must not raise, and
        # must simply omit pid 3 from the sample rather than recording a bogus 0.
        _write_proc_entry(tmp_path, pid=1, ppid=0, vm_rss_kb=1000)
        _write_proc_entry(tmp_path, pid=2, ppid=1, vm_rss_kb=50000)
        d = tmp_path / "3"
        d.mkdir()
        (d / "status").write_text("Name:\tpytest\nPPid:\t1\n")  # discoverable, no VmRSS
        sample = sampler.sample_once(tmp_path, root_pid=1)
        assert sample == {2: 50000}


class TestPeakTracker:
    def test_tracks_per_pid_peak_across_samples(self):
        tracker = sampler.PeakTracker()
        tracker.record({2: 1000, 3: 2000})
        tracker.record({2: 1500, 3: 1800})
        tracker.record({2: 900, 3: 2500})
        assert tracker.per_pid_peak_kb == {2: 1500, 3: 2500}

    def test_tracks_aggregate_peak_as_max_per_sample_total(self):
        tracker = sampler.PeakTracker()
        tracker.record({2: 1000, 3: 2000})  # total 3000
        tracker.record({2: 5000, 3: 100})  # total 5100 <- max
        tracker.record({2: 1000, 3: 1000})  # total 2000
        assert tracker.aggregate_peak_kb == 5100

    def test_worker_replaced_mid_run_both_pids_contribute_to_per_pid_peak(self):
        # This is exactly the D scenario: a worker dies and is replaced by a new pid. Both
        # pids' peaks must be preserved, not overwritten -- the replacement is diagnostic
        # data, not noise to discard.
        tracker = sampler.PeakTracker()
        tracker.record({10: 40000, 11: 30000})
        tracker.record({10: 45000})  # pid 11 (the replacement worker) died
        tracker.record({10: 46000, 12: 5000})  # a new worker pid 12 appeared
        assert tracker.per_pid_peak_kb == {10: 46000, 11: 30000, 12: 5000}

    def test_sample_count_increments(self):
        tracker = sampler.PeakTracker()
        assert tracker.sample_count == 0
        tracker.record({2: 100})
        tracker.record({2: 200})
        assert tracker.sample_count == 2

    def test_empty_sample_still_counts_and_does_not_crash(self):
        tracker = sampler.PeakTracker()
        tracker.record({})
        assert tracker.sample_count == 1
        assert tracker.per_pid_peak_kb == {}
        assert tracker.aggregate_peak_kb == 0

    def test_summary_records_absolute_kb_not_a_ratio_and_no_16gb_threshold(self):
        # Scope Hypothesis guard: the sampler must record absolute peak RSS (comparable
        # against any ceiling a future task supplies) and must not itself encode any
        # particular ceiling (e.g. 16GB) as a threshold or assertion.
        tracker = sampler.PeakTracker()
        tracker.record({2: 1000, 3: 2000})
        summary = tracker.summary(workers=6, interval_s=2.0)
        assert summary["aggregate_peak_kb"] == 3000
        assert summary["per_worker_peak_kb"] == 2000
        assert summary["workers"] == 6
        assert summary["interval_s"] == 2.0
        assert summary["sample_count"] == 1
        assert summary["per_pid_peak_kb"] == {"2": 1000, "3": 2000}
        # No threshold-shaped keys anywhere in the summary.
        for key in summary:
            assert "16" not in key and "ceiling" not in key.lower() and "limit" not in key.lower()

    def test_summary_with_no_samples_is_well_formed(self):
        tracker = sampler.PeakTracker()
        summary = tracker.summary(workers=4, interval_s=1.0)
        assert summary["aggregate_peak_kb"] == 0
        assert summary["per_worker_peak_kb"] == 0
        assert summary["sample_count"] == 0
        assert summary["per_pid_peak_kb"] == {}

    def test_summary_is_json_serializable(self):
        tracker = sampler.PeakTracker()
        tracker.record({2: 1000, 3: 2000})
        summary = tracker.summary(workers=6, interval_s=2.0)
        # json.dumps requires string keys; the module's own summary() must already convert
        # int pids to strings, or json.dumps must not raise here either way.
        json.dumps(summary)


class TestParseXdistWorkerId:
    """Unit tests for `parse_xdist_worker_id`, which extracts `PYTEST_XDIST_WORKER` (e.g.
    `gw2`) from NUL-separated `/proc/<pid>/environ`-shaped bytes. See Finding 1 of the research
    report backing this task: `xdist/remote.py:416-418` sets this variable inside each worker
    subprocess's own environment, verified against the installed `pytest-xdist==3.8.0` source."""

    def test_extracts_gw2_from_realistic_environ_bytes(self):
        environ = (
            b"PATH=/usr/bin\0"
            b"PYTEST_XDIST_TESTRUNUID=abc123\0"
            b"PYTEST_XDIST_WORKER=gw2\0"
            b"PYTEST_XDIST_WORKER_COUNT=4\0"
        )
        assert sampler.parse_xdist_worker_id(environ) == "gw2"

    def test_returns_none_when_absent(self):
        environ = b"PATH=/usr/bin\0HOME=/root\0"
        assert sampler.parse_xdist_worker_id(environ) is None

    def test_not_confused_by_worker_count_prefix(self):
        # PYTEST_XDIST_WORKER_COUNT is a real sibling variable xdist also sets. A naive
        # `key.startswith(b"PYTEST_XDIST_WORKER")` match would grab this one's value ("4")
        # instead of the actual worker id -- this is the exact-key-match guard the plan calls
        # out as mattering, since both keys are set by xdist/remote.py in every worker.
        environ = b"PYTEST_XDIST_WORKER_COUNT=4\0PYTEST_XDIST_WORKER=gw3\0"
        assert sampler.parse_xdist_worker_id(environ) == "gw3"

    def test_worker_count_only_without_worker_key_returns_none(self):
        environ = b"PYTEST_XDIST_WORKER_COUNT=4\0"
        assert sampler.parse_xdist_worker_id(environ) is None

    def test_tolerates_trailing_nul_and_non_utf8(self):
        environ = b"PYTEST_XDIST_WORKER=gw1\0" + b"\xff\xfe\0" + b"\0"
        assert sampler.parse_xdist_worker_id(environ) == "gw1"


class TestReadXdistWorkerId:
    """Unit tests for `read_xdist_worker_id`, mirroring `read_vm_rss_kb`'s tolerance for a
    process that raced away or a permission-restricted environ file -- both are the normal,
    expected shape of reading a live `/proc`, not error conditions."""

    def test_reads_tagged_pid(self, tmp_path):
        _write_proc_environ(tmp_path, pid=200, pairs=[(b"PYTEST_XDIST_WORKER", b"gw2")])
        assert sampler.read_xdist_worker_id(tmp_path, 200) == "gw2"

    def test_missing_pid_directory_returns_none(self, tmp_path):
        assert sampler.read_xdist_worker_id(tmp_path, 999) is None

    def test_unreadable_environ_returns_none(self, tmp_path, monkeypatch):
        _write_proc_environ(tmp_path, pid=201, pairs=[(b"PYTEST_XDIST_WORKER", b"gw1")])
        environ_path = tmp_path / "201" / "environ"
        original_read_bytes = Path.read_bytes

        def _raise_permission_error(self):
            if self == environ_path:
                raise PermissionError("simulated: unreadable environ (permission-restricted)")
            return original_read_bytes(self)

        monkeypatch.setattr(Path, "read_bytes", _raise_permission_error)
        assert sampler.read_xdist_worker_id(tmp_path, 201) is None


class TestPeakTrackerWorkerAttribution:
    """`PeakTracker.record()` gains an optional `worker_ids` parameter mapping pid -> `gwN`
    (or `None`). These tests are additive -- they never call `record()` with the old
    single-argument shape in a way that would require changing `TestPeakTracker`'s existing
    assertions, since `worker_ids` defaults to `None`/empty and an unattributed pid degrades to
    untagged rather than being dropped."""

    def test_per_pid_peak_kb_entries_gain_worker_id_association(self):
        tracker = sampler.PeakTracker()
        tracker.record({2: 1000, 3: 2000}, worker_ids={2: "gw0", 3: "gw1"})
        assert tracker.pid_to_worker == {2: "gw0", 3: "gw1"}

    def test_summary_exposes_pid_to_worker_and_per_worker_id_peak(self):
        tracker = sampler.PeakTracker()
        tracker.record({2: 1000, 3: 2000}, worker_ids={2: "gw0", 3: "gw1"})
        tracker.record({2: 1500, 3: 1800}, worker_ids={2: "gw0", 3: "gw1"})
        summary = tracker.summary(workers=2, interval_s=0.25)
        assert summary["pid_to_worker"] == {"2": "gw0", "3": "gw1"}
        assert summary["per_worker_id_peak_kb"] == {"gw0": 1500, "gw1": 2000}

    def test_untagged_pid_is_still_recorded_not_dropped(self):
        tracker = sampler.PeakTracker()
        # pid 5 carries no worker_ids entry at all (e.g. a non-xdist smoke run, or a
        # permission-restricted environ read) -- it must degrade to untagged, never vanish.
        tracker.record({5: 4000}, worker_ids={})
        summary = tracker.summary(workers=1, interval_s=0.25)
        assert summary["pid_to_worker"] == {"5": None}
        assert summary["per_pid_peak_kb"] == {"5": 4000}
        # An untagged pid contributes nothing to per_worker_id_peak_kb (no gwN to attribute to).
        assert summary["per_worker_id_peak_kb"] == {}

    def test_first_non_none_id_wins_never_overwritten_by_later_none(self):
        tracker = sampler.PeakTracker()
        tracker.record({7: 1000}, worker_ids={7: "gw2"})
        # A later sample where pid 7's environ read raced away must not blank out the id
        # already recorded for it.
        tracker.record({7: 1100}, worker_ids={7: None})
        assert tracker.pid_to_worker == {7: "gw2"}

    def test_worker_replaced_mid_run_both_pids_map_to_same_worker_id_distinct_peaks(self):
        # The exact D scenario: gw0's original pid dies and is replaced by a new pid that is
        # ALSO tagged gw0 (xdist reuses the worker id string for the replacement worker). Both
        # pids' own peaks must stay distinct in per_pid_peak_kb while both attribute to "gw0"
        # in pid_to_worker -- this must not conflate the two pids into one entry.
        tracker = sampler.PeakTracker()
        tracker.record({10: 40000}, worker_ids={10: "gw0"})
        tracker.record({}, worker_ids={})  # pid 10 (gw0) died between samples
        tracker.record({12: 5000}, worker_ids={12: "gw0"})  # replacement worker, also gw0
        assert tracker.per_pid_peak_kb == {10: 40000, 12: 5000}
        assert tracker.pid_to_worker == {10: "gw0", 12: "gw0"}
        summary = tracker.summary(workers=1, interval_s=0.25)
        # per_worker_id_peak_kb["gw0"] is the max across BOTH pids that carried that id.
        assert summary["per_worker_id_peak_kb"]["gw0"] == 40000

    def test_summary_with_worker_ids_stays_json_serializable_and_has_no_ceiling(self):
        tracker = sampler.PeakTracker()
        tracker.record({2: 1000, 3: 2000}, worker_ids={2: "gw0", 3: "gw1"})
        summary = tracker.summary(workers=2, interval_s=0.25)
        json.dumps(summary)
        for key in summary:
            assert "16" not in key and "ceiling" not in key.lower() and "limit" not in key.lower()


class TestSamplerIsNotMatrixGated:
    """The sampler must run on EVERY Python leg, not just 3.12.

    RATIONALE -- WHY THIS GUARD EXISTS. The sampler was originally wired behind
    `if [ "${{ matrix.python-version }}" = "3.12" ]`, justified in tests.yml by the claim
    that 3.12 was "the only leg the crash has been observed on". CI run 32996446859
    falsified that premise: `[gw2] node down: Not properly terminated` occurred on
    **Python 3.11**, and because the sampler was 3.12-gated it collected NOTHING for the
    one incident it exists to explain.

    Telemetry gated to a subset of legs cannot observe a failure whose leg distribution is
    the open question. The step is non-gating and cheap (a /proc poll on a 2s interval), so
    there is no cost argument for restricting it. This guard makes "sample every leg"
    executable so a future edit cannot silently re-gate it and reintroduce the blind spot.
    """

    def test_sampler_invocation_is_not_python_version_conditional(self):
        text = TESTS_YML.read_text(encoding="utf-8")
        assert "worker_rss_sample.py" in text, (
            "The sampler invocation vanished from tests.yml. If the telemetry was "
            "deliberately removed (item D resolved), delete this test class too -- see the "
            "sampler module docstring's 'removable in one piece' note."
        )
        for line in text.splitlines():
            if "matrix.python-version" in line and "=" in line and "if" in line:
                raise AssertionError(
                    "tests.yml gates a step on a specific matrix.python-version value:\n"
                    f"  {line.strip()}\n"
                    "The RSS sampler must run on every Python leg -- the crash it "
                    "instruments has been observed on both 3.11 and 3.12."
                )

    def test_sampler_runs_on_every_matrix_leg(self):
        text = TESTS_YML.read_text(encoding="utf-8")
        sampler_lines = [ln for ln in text.splitlines() if "worker_rss_sample.py" in ln and "python3" in ln]
        assert len(sampler_lines) == 1, (
            f"Expected exactly one sampler invocation line, found {len(sampler_lines)}. "
            "A per-leg duplicate would break test_workflow_parity.py's extraction regex."
        )


class TestSamplerIntervalIsSubSecond:
    """The `--interval` on `tests.yml`'s sampler invocation must be `<= 0.5` seconds.

    RATIONALE -- WHY THIS GUARD EXISTS. Both confirmed `node down` incidents' RSS traces were
    sampled at the original `--interval 2` (a 2-second poll). A worker's peak resident-set size
    can spike and be reclaimed well inside a 2-second window -- a coarse interval structurally
    cannot see a transient spike, which is exactly what made those two traces uninformative about
    whether memory pressure preceded the crash. This guard keeps the interval tightened so the
    *next* incident's telemetry is fine-grained enough to actually inform the open hypothesis
    ledger (see the sampler module's own docstring for the current ledger and the measured
    overhead behind the chosen value).
    """

    def test_interval_argument_is_at_most_half_a_second(self):
        text = TESTS_YML.read_text(encoding="utf-8")
        sampler_lines = [
            ln for ln in text.splitlines() if "worker_rss_sample.py" in ln and "--interval" in ln
        ]
        assert len(sampler_lines) == 1, (
            f"Expected exactly one sampler invocation line carrying --interval, found "
            f"{len(sampler_lines)}."
        )
        match = re.search(r"--interval\s+(\S+)", sampler_lines[0])
        assert match is not None, f"No --interval value found on: {sampler_lines[0]!r}"
        interval_value = float(match.group(1))
        assert interval_value <= 0.5, (
            f"tests.yml's sampler --interval is {interval_value}s, coarser than the 0.5s ceiling "
            "this guard enforces. A coarse interval is what made the two confirmed incidents' "
            "RSS traces uninformative -- do not widen it back without re-measuring the sampler's "
            "own CPU overhead and updating this guard deliberately."
        )
