#!/usr/bin/env bash
# Local source materialization for the existing five-theorem adapter.
# Original fork remains the default; the licensed editions are opt-in.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SIDECAR="$ROOT/proofs/alpoge-lean433"
SOURCE="${GRH_P0_SOURCE:-original}"
case "$SOURCE" in
  original) DEFAULT="$ROOT/.local/alpoge-rh-v4331" ;;
  compact|readable) DEFAULT="$ROOT/.local/alpoge-grh-v4350" ;;
  *) echo "Unknown GRH_P0_SOURCE: $SOURCE" >&2; exit 2 ;;
esac
python3 - "$SIDECAR" "$SOURCE" "${1:-$DEFAULT}" <<'PY'
import json
import os
import pathlib
import subprocess
import sys

sidecar, source, target = pathlib.Path(sys.argv[1]), sys.argv[2], pathlib.Path(sys.argv[3]).resolve()
original = json.loads((sidecar / "fork_pin.json").read_text())
if source == "original":
    pin = original
    project = ""
    tree = None
    blobs = pin["git_blobs"]
else:
    pin = json.loads((sidecar / "licensed_rewrite_pin.json").read_text())
    edition = pin["editions"][source]
    project, tree = edition["project"], edition["tree"]
    if edition["git_blobs"]["src/Statements.lean"] != original["git_blobs"]["src/Statements.lean"]:
        sys.exit("BLOCKED: original statement blob mismatch")
    blobs = {**pin["root_git_blobs"], **{f"{project}/{p}": h for p, h in edition["git_blobs"].items()}}

def git(*args):
    return subprocess.check_output(["git", "-C", str(target), *args], text=True).strip()

def require(ok, why):
    if not ok:
        sys.exit("BLOCKED: " + why)

def clean():
    require(not git("status", "--porcelain=v1", "--untracked-files=all"), "dirty source checkout")
    flags = git("ls-files", "-v").splitlines()
    require(not any(s[:1] == "S" or s[:1].islower() for s in flags),
            "skip-worktree or assume-unchanged source paths")

verify_only = os.environ.get("GRH_P0_VERIFY_ONLY") == "1"
if not target.exists():
    require(not verify_only, "source disappeared during build")
    target.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(["git", "clone", pin["url"], str(target)], check=True)
require(target.is_dir() and (target / ".git").exists(), "not a source Git checkout")
require(pathlib.Path(git("rev-parse", "--show-toplevel")).resolve() == target, "wrong checkout root")
require(git("remote", "get-url", "origin") in {pin["url"], pin["url"].removesuffix(".git")},
        "unexpected source origin")
clean()  # reject local changes BEFORE changing HEAD
revision = pin["revision"]
git("cat-file", "-e", revision + "^{commit}")
if git("rev-parse", "HEAD") != revision:
    require(not verify_only, "source HEAD changed during build")
    git("checkout", "--detach", revision)
require(git("rev-parse", "HEAD") == revision, "source revision mismatch")
clean()
if tree is not None:
    require(git("rev-parse", f"HEAD:{project}") == tree, "edition tree mismatch")
for p, digest in blobs.items():
    require(git("rev-parse", "HEAD:" + p) == digest, "committed blob mismatch: " + p)
    require(git("hash-object", "--no-filters", str(target / p)) == digest,
            "working bytes mismatch: " + p)
root = target / project
require((root / "lean-toolchain").read_text().strip() == pin["toolchain"], "toolchain mismatch")
manifest = json.loads((root / "lake-manifest.json").read_text())
require([p["rev"] for p in manifest["packages"] if p["name"] == "mathlib"] == [pin["mathlib_revision"]],
        "Mathlib revision mismatch")
print(f"PINNED SOURCE {source}: {revision}")
print(f"PROJECT: {root}")
print(f"Verified {len(blobs)} Git blob and working-byte pins; exact statement interface.")
print("SOURCE PROVENANCE ONLY: no proof replay performed.")
PY
