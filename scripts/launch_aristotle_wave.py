#!/usr/bin/env python3
"""Launch and monitor independent Aristotle mirror projects with backoff."""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import tarfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_WAVE_ROOT = ROOT / "outputs" / "aristotle_mirror_waves"
DEFAULT_STATE_ROOT = ROOT / ".autonomous-orchestrator" / "aristotle"
DEFAULT_MANAGER = ROOT.parent / "aristotle-cli-rs"
UUID_RE = re.compile(r"Project created:\s*([0-9a-f-]{36})", re.IGNORECASE)
TASK_RE = re.compile(r"^\s*([0-9a-f-]{36})\s+([A-Z][A-Z_]*)\s+(\d+)%", re.MULTILINE)
ACTIVE_STATUSES = {"QUEUED", "IN_PROGRESS", "RUNNING", "PENDING"}
FAILED_STATUSES = {"FAILED", "ERROR", "CANCELLED", "CANCELED", "OUT_OF_BUDGET"}


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def write_json(path: Path, payload: object, lock: threading.Lock) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with lock:
        temporary = path.with_suffix(path.suffix + ".tmp")
        temporary.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        temporary.replace(path)


def safe_extract(archive: Path, destination: Path) -> None:
    destination.mkdir(parents=True, exist_ok=True)
    root = destination.resolve()
    with tarfile.open(archive, "r:*") as handle:
        for member in handle.getmembers():
            target = (destination / member.name).resolve()
            if target != root and root not in target.parents:
                raise RuntimeError(f"refusing archive path traversal: {member.name}")
        handle.extractall(destination)


class WaveRunner:
    def __init__(self, args: argparse.Namespace, wave: dict[str, object]) -> None:
        self.args = args
        self.wave = wave
        self.wave_id = str(wave["wave_id"])
        self.state_root = args.state_root / self.wave_id
        self.state_path = self.state_root / "state.json"
        self.workers_path = self.state_root / f"status.{self.wave_id}.workers.json"
        self.summary_path = self.state_root / f"status.{self.wave_id}.root-summary.json"
        self.log_root = self.state_root / "logs"
        self.lock = threading.Lock()
        self.state = self._load_state()

    def _load_state(self) -> dict[str, object]:
        if self.args.resume and self.state_path.exists():
            return json.loads(self.state_path.read_text(encoding="utf-8"))
        jobs = {}
        for lane in self.wave["lanes"]:  # type: ignore[union-attr]
            lane_id = str(lane["id"])
            jobs[lane_id] = {
                "id": lane_id,
                "claim": lane.get("claim", ""),
                "bundle_dir": lane["bundle_dir"],
                "prompt_file": lane["prompt_file"],
                "status": "queued",
                "attempt": 0,
                "project_id": None,
                "task_id": None,
                "percent": 0,
                "created_at": None,
                "last_poll_at": None,
                "last_error": None,
                "result_archive": None,
                "result_dir": None,
            }
        return {"schema": "dashi-aristotle-wave-run-v1", "wave_id": self.wave_id, "started_at": None, "jobs": jobs}

    def save(self) -> None:
        self.state["updated_at"] = utc_now()
        write_json(self.state_path, self.state, self.lock)
        jobs = list(self.state["jobs"].values())  # type: ignore[union-attr]
        write_json(self.workers_path, {"wave_id": self.wave_id, "workers": jobs}, self.lock)
        statuses = [str(job["status"]) for job in jobs]
        summary = {
            "wave_id": self.wave_id,
            "started_at": self.state.get("started_at"),
            "updated_at": self.state.get("updated_at"),
            "counts": {status: statuses.count(status) for status in sorted(set(statuses))},
            "jobs_total": len(jobs),
            "jobs_complete": statuses.count("completed"),
            "jobs_failed": statuses.count("failed"),
            "next_wave_ready": bool(jobs) and all(status == "completed" for status in statuses),
        }
        write_json(self.summary_path, summary, self.lock)

    def log(self, lane_id: str, message: str) -> None:
        path = self.log_root / f"{lane_id}.log"
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("a", encoding="utf-8") as handle:
            handle.write(f"[{utc_now()}] {message}\n")

    def manager_command(self, *arguments: str) -> list[str]:
        return [
            "cargo", "run", "--quiet", "--manifest-path", str(self.args.manager / "Cargo.toml"), "--",
            *arguments,
        ]

    def invoke(self, lane_id: str, arguments: list[str], timeout: int) -> str:
        self.log(lane_id, "RUN " + " ".join(arguments))
        completed = subprocess.run(
            self.manager_command(*arguments),
            cwd=self.args.manager,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
        output = ((completed.stdout or "") + (completed.stderr or "")).strip()
        self.log(lane_id, f"EXIT {completed.returncode}: {output[-4000:]}")
        if completed.returncode != 0:
            raise RuntimeError(output[-2000:] or f"manager exited {completed.returncode}")
        return output

    def set_job(self, lane_id: str, **updates: object) -> None:
        job = self.state["jobs"][lane_id]  # type: ignore[index]
        job.update(updates)
        self.save()

    def submit(self, job: dict[str, object]) -> None:
        lane_id = str(job["id"])
        prompt = Path(str(job["prompt_file"])).read_text(encoding="utf-8")
        output = self.invoke(lane_id, ["submit", prompt, "--project-dir", str(job["bundle_dir"])], 1800)
        match = UUID_RE.search(output)
        if not match:
            raise RuntimeError(f"could not parse project id from submit output: {output[-1000:]}")
        self.set_job(lane_id, status="submitted", project_id=match.group(1), attempt=int(job["attempt"]) + 1, created_at=utc_now(), last_error=None)

    def poll(self, job: dict[str, object]) -> tuple[str, str | None, int]:
        output = self.invoke(str(job["id"]), ["show", str(job["project_id"]), "--limit", "1"], 300)
        match = TASK_RE.search(output)
        if not match:
            raise RuntimeError(f"could not parse task status: {output[-1000:]}")
        task_id, status, percent = match.groups()
        return status, task_id, int(percent)

    def download(self, job: dict[str, object]) -> None:
        lane_id = str(job["id"])
        lane_dir = Path(str(job["bundle_dir"]))
        result_root = self.args.wave_root / self.wave_id / "results" / lane_id
        result_root.mkdir(parents=True, exist_ok=True)
        archive = result_root / "result.tar.gz"
        self.invoke(lane_id, ["download", str(job["project_id"]), "--destination", str(archive)], 1800)
        extract_root = result_root / "extracted"
        safe_extract(archive, extract_root)
        self.set_job(lane_id, status="completed", result_archive=str(archive), result_dir=str(extract_root), completed_at=utc_now())
        del lane_dir

    def run_job(self, lane_id: str) -> None:
        job = self.state["jobs"][lane_id]  # type: ignore[index]
        if str(job["status"]) in {"completed", "failed"}:
            return
        deadline = time.monotonic() + self.args.deadline_seconds
        schedule = list(self.args.poll_schedule)
        delay_index = 0
        while time.monotonic() < deadline:
            try:
                if not job.get("project_id"):
                    self.set_job(lane_id, status="submitting")
                    self.submit(job)
                    job = self.state["jobs"][lane_id]  # type: ignore[index]
                status, task_id, percent = self.poll(job)
                job = self.state["jobs"][lane_id]  # type: ignore[index]
                self.set_job(lane_id, status="running" if status in ACTIVE_STATUSES else status.lower(), task_id=task_id, percent=percent, last_poll_at=utc_now(), last_error=None)
                if status not in ACTIVE_STATUSES:
                    if status in FAILED_STATUSES:
                        raise RuntimeError(f"Aristotle task ended with {status}")
                    self.download(self.state["jobs"][lane_id])  # type: ignore[index]
                    return
                delay = schedule[min(delay_index, len(schedule) - 1)]
                delay_index += 1
                self.log(lane_id, f"status={status} percent={percent}; sleeping {delay}s")
                time.sleep(min(delay, max(0.0, deadline - time.monotonic())))
            except Exception as exc:  # noqa: BLE001 - persisted remote job needs retry
                message = str(exc)
                self.set_job(lane_id, status="retrying", last_error=message, last_poll_at=utc_now())
                delay = schedule[min(delay_index, len(schedule) - 1)]
                delay_index += 1
                self.log(lane_id, f"ERROR {message}; retrying in {delay}s")
                time.sleep(min(delay, max(0.0, deadline - time.monotonic())))
        self.set_job(lane_id, status="failed", last_error=f"deadline exceeded after {self.args.deadline_seconds}s", failed_at=utc_now())

    def run(self) -> int:
        self.state["started_at"] = self.state.get("started_at") or utc_now()
        self.save()
        if self.args.dry_run:
            for job in self.state["jobs"].values():  # type: ignore[union-attr]
                print(f"would submit {job['id']} from {job['bundle_dir']}")
            return 0
        with ThreadPoolExecutor(max_workers=self.args.max_parallel) as pool:
            futures = [pool.submit(self.run_job, lane_id) for lane_id in self.state["jobs"]]  # type: ignore[union-attr]
            for future in as_completed(futures):
                future.result()
        self.save()
        jobs = list(self.state["jobs"].values())  # type: ignore[union-attr]
        return 0 if all(str(job["status"]) == "completed" for job in jobs) else 1


def load_wave(path: Path) -> dict[str, object]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if "lanes" not in payload or "wave_id" not in payload:
        raise ValueError("wave manifest must be the builder's wave-manifest.json")
    for lane in payload["lanes"]:
        for key in ("bundle_dir", "prompt_file"):
            value = Path(str(lane[key]))
            if not value.is_absolute():
                lane[key] = str((path.parent / value).resolve())
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wave-manifest", type=Path, required=True)
    parser.add_argument("--manager", type=Path, default=DEFAULT_MANAGER)
    parser.add_argument("--wave-root", type=Path, default=DEFAULT_WAVE_ROOT)
    parser.add_argument("--state-root", type=Path, default=DEFAULT_STATE_ROOT)
    parser.add_argument("--max-parallel", type=int, default=4)
    parser.add_argument("--deadline-seconds", type=int, default=6 * 60 * 60)
    parser.add_argument("--poll-schedule", type=int, nargs="+", default=[30, 60, 120, 300, 600])
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    if args.max_parallel < 1 or args.deadline_seconds < 1800 or not args.poll_schedule:
        parser.error("require max-parallel >= 1, deadline >= 1800 seconds, and a non-empty poll schedule")
    args.manager = args.manager.resolve()
    args.wave_root = args.wave_root.resolve()
    args.state_root = args.state_root.resolve()
    if not (args.manager / "Cargo.toml").is_file():
        parser.error(f"Aristotle manager Cargo.toml not found under {args.manager}")
    runner = WaveRunner(args, load_wave(args.wave_manifest))
    return runner.run()


if __name__ == "__main__":
    raise SystemExit(main())
