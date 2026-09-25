#!/usr/bin/env python3
"""Verify and materialize the Round11/Machin route-B Agda provenance replay.

This is deliberately a provenance replay, not an Agda-to-Lean proof translator.

It:
  * parses Integration/BishopRound11MachinBindingManifest.lean;
  * verifies every content-addressed Agda source blob against a checkout;
  * verifies the vendored Bishop submodule commit;
  * checks the named Agda declarations used by the Lean binding surface;
  * recursively walks imports from every load-bearing Agda root;
  * writes a machine-readable JSON receipt;
  * generates a Lean certificate whose observed hashes are checked against the
    checked-in Lean manifest by kernel elaboration.

Exit status is nonzero on any provenance mismatch.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys
from dataclasses import dataclass
from typing import Iterable


BLOB_RE = re.compile(
    r'def\s+(?P<name>[A-Za-z0-9_]+Blob)\s*:\s*SourceBlob\s*:=\s*'
    r'\s*⟨"(?P<path>[^"]+)",\s*"(?P<sha>[0-9a-f]{40})"⟩',
    re.MULTILINE,
)
AGDA_COMMIT_RE = re.compile(
    r'def\s+agdaSourceCommit\s*:\s*String\s*:=\s*"(?P<sha>[0-9a-f]{40})"'
)
BISHOP_COMMIT_RE = re.compile(
    r'def\s+bishopSubmoduleCommit\s*:\s*String\s*:=\s*"(?P<sha>[0-9a-f]{40})"'
)
BINDING_RE = re.compile(
    r'def\s+(?P<name>[A-Za-z0-9_]+Binding)\s*:\s*SourceTheoremBinding\s*:=\s*'
    r'\s*⟨(?P<owner>[A-Za-z0-9_]+Blob)\.path,\s*'
    r'"(?P<agda>[^"]+)",\s*"(?P<lean_owner>[^"]+)",\s*"(?P<lean>[^"]+)"⟩',
    re.MULTILINE,
)
IMPORT_RE = re.compile(
    r'^\s*(?:open\s+)?import\s+([A-Za-z0-9_.]+)',
    re.MULTILINE,
)


@dataclass(frozen=True)
class SourceBlob:
    name: str
    path: str
    sha: str


@dataclass(frozen=True)
class SourceBinding:
    name: str
    owner_blob: str
    agda_declaration: str
    lean_owner: str
    lean_declaration: str


def run(*args: str, cwd: pathlib.Path | None = None) -> str:
    proc = subprocess.run(
        args,
        cwd=cwd,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"command failed ({proc.returncode}): {' '.join(args)}\n"
            f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        )
    return proc.stdout.strip()


def parse_manifest(
    path: pathlib.Path,
) -> tuple[list[SourceBlob], str, str, list[SourceBinding]]:
    text = path.read_text(encoding="utf-8")
    blobs = [
        SourceBlob(m.group("name"), m.group("path"), m.group("sha"))
        for m in BLOB_RE.finditer(text)
    ]
    if not blobs:
        raise RuntimeError(f"no SourceBlob declarations parsed from {path}")

    agda = AGDA_COMMIT_RE.search(text)
    if agda is None:
        raise RuntimeError("agdaSourceCommit not found in manifest")

    bishop = BISHOP_COMMIT_RE.search(text)
    if bishop is None:
        raise RuntimeError("bishopSubmoduleCommit not found in manifest")

    bindings = [
        SourceBinding(
            m.group("name"),
            m.group("owner"),
            m.group("agda"),
            m.group("lean_owner"),
            m.group("lean"),
        )
        for m in BINDING_RE.finditer(text)
    ]
    if not bindings:
        raise RuntimeError("no SourceTheoremBinding declarations parsed from manifest")

    return blobs, agda.group("sha"), bishop.group("sha"), bindings


def git_blob_sha(root: pathlib.Path, rel: str) -> str:
    return run("git", "hash-object", rel, cwd=root)


def declaration_present(text: str, name: str) -> bool:
    pattern = re.compile(
        rf"(?m)^\s*(?:record\s+|data\s+|postulate\s+)?{re.escape(name)}\s*(?::|=)"
    )
    if pattern.search(text):
        return True
    # Fields can occur inside an Agda field block without a leading keyword.
    return re.search(rf"(?m)^\s+{re.escape(name)}\s*:", text) is not None


def resolve_module(agda_root: pathlib.Path, module: str) -> pathlib.Path | None:
    rel = pathlib.Path(*module.split(".")).with_suffix(".agda")
    candidates = [
        agda_root / rel,
        agda_root / "vendor" / "bishop" / rel,
    ]
    for candidate in candidates:
        if candidate.exists():
            return candidate
    return None


def recursive_import_closure(
    agda_root: pathlib.Path, roots: Iterable[pathlib.Path]
) -> list[pathlib.Path]:
    seen: set[pathlib.Path] = set()
    pending = list(roots)

    while pending:
        path = pending.pop()
        path = path.resolve()
        if path in seen:
            continue
        seen.add(path)
        text = path.read_text(encoding="utf-8")
        for module in IMPORT_RE.findall(text):
            resolved = resolve_module(agda_root, module)
            if resolved is not None and resolved.resolve() not in seen:
                pending.append(resolved)

    return sorted(seen)


def rel_display(agda_root: pathlib.Path, path: pathlib.Path) -> str:
    try:
        return str(path.relative_to(agda_root.resolve()))
    except ValueError:
        return str(path)


def lean_string(value: str) -> str:
    return value.replace("\\", "\\\\").replace('"', '\\"')


def write_lean_certificate(
    out_path: pathlib.Path,
    blobs: list[SourceBlob],
    bindings: list[SourceBinding],
    bishop_commit: str,
    agda_commit: str,
    closure: list[str],
) -> None:
    blob_items = "\n".join(
        f'  , ⟨"{lean_string(blob.path)}", "{blob.sha}"⟩' for blob in blobs[1:]
    )
    first = blobs[0]
    blob_by_name = {blob.name: blob for blob in blobs}
    binding_items = "\n".join(
        "  , ⟨"
        f'"{lean_string(blob_by_name[binding.owner_blob].path)}", '
        f'"{lean_string(binding.agda_declaration)}", '
        f'"{lean_string(binding.lean_owner)}", '
        f'"{lean_string(binding.lean_declaration)}"'
        "⟩"
        for binding in bindings[1:]
    )
    first_binding = bindings[0]
    first_binding_owner = blob_by_name[first_binding.owner_blob].path
    closure_items = "\n".join(f'  , "{lean_string(p)}"' for p in closure[1:])
    first_closure = closure[0] if closure else ""

    content = f'''import Integration.BishopRound11MachinBindingManifest

/-!
# Generated Round11/Machin Agda provenance replay certificate

GENERATED FILE. Do not edit by hand.

The companion verifier checked these values against an actual dashi_agda
checkout before writing this file. Kernel elaboration below then checks that
the observed load-bearing blob list and Bishop submodule commit agree with the
checked-in Lean manifest.
-/

namespace Generated.BishopRound11MachinReplayCertificate

open Integration.BishopRound11MachinBindingManifest

def observedAgdaCommit : String := "{agda_commit}"
def observedBishopCommit : String := "{bishop_commit}"

def observedLoadBearingBlobs : List SourceBlob :=
  [ ⟨"{lean_string(first.path)}", "{first.sha}"⟩
{blob_items}
  ]

def observedTheoremBindings : List SourceTheoremBinding :=
  [ ⟨"{lean_string(first_binding_owner)}", "{lean_string(first_binding.agda_declaration)}",
      "{lean_string(first_binding.lean_owner)}", "{lean_string(first_binding.lean_declaration)}"⟩
{binding_items}
  ]

def observedImportClosure : List String :=
  [ "{lean_string(first_closure)}"
{closure_items}
  ]

theorem agda_commit_matches_manifest :
    observedAgdaCommit = agdaSourceCommit := by
  native_decide

theorem bishop_commit_matches_manifest :
    observedBishopCommit = bishopSubmoduleCommit := by
  native_decide

theorem load_bearing_blobs_match_manifest :
    observedLoadBearingBlobs = loadBearingBlobs := by
  native_decide

theorem theorem_bindings_match_manifest :
    observedTheoremBindings = theoremBindings := by
  native_decide

structure GeneratedReplayReceipt where
  agdaCheckoutObserved : Bool
  bishopSubmoduleObserved : Bool
  loadBearingBlobsVerified : Bool
  sourceDeclarationsVerified : Bool
  theoremBindingTableKernelMatched : Bool
  recursiveImportClosureObserved : Bool
  leanManifestKernelMatch : Bool

def generatedReplayReceipt : GeneratedReplayReceipt where
  agdaCheckoutObserved := true
  bishopSubmoduleObserved := true
  loadBearingBlobsVerified := true
  sourceDeclarationsVerified := true
  theoremBindingTableKernelMatched := true
  recursiveImportClosureObserved := true
  leanManifestKernelMatch := true

end Generated.BishopRound11MachinReplayCertificate
'''
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(content, encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--agda-root", required=True, type=pathlib.Path)
    parser.add_argument(
        "--manifest",
        type=pathlib.Path,
        default=pathlib.Path("Integration/BishopRound11MachinBindingManifest.lean"),
    )
    parser.add_argument(
        "--out-json",
        type=pathlib.Path,
        default=pathlib.Path("build/round11-machin-replay.json"),
    )
    parser.add_argument(
        "--out-lean",
        type=pathlib.Path,
        default=pathlib.Path("Generated/BishopRound11MachinReplayCertificate.lean"),
    )
    args = parser.parse_args()

    agda_root = args.agda_root.resolve()
    manifest = args.manifest.resolve()
    blobs, expected_agda_commit, expected_bishop_commit, bindings = parse_manifest(manifest)
    blob_by_name = {blob.name: blob for blob in blobs}

    failures: list[str] = []

    try:
        observed_agda_commit = run("git", "rev-parse", "HEAD", cwd=agda_root)
    except RuntimeError:
        observed_agda_commit = "unknown"
        failures.append("unable to resolve dashi_agda checkout commit")
    if observed_agda_commit != expected_agda_commit:
        failures.append(
            "dashi_agda checkout mismatch: "
            f"expected {expected_agda_commit}, observed {observed_agda_commit}"
        )

    observed_blobs: list[dict[str, str]] = []
    root_paths: list[pathlib.Path] = []
    for blob in blobs:
        source_path = agda_root / blob.path
        if not source_path.exists():
            failures.append(f"missing source file: {blob.path}")
            continue
        observed = git_blob_sha(agda_root, blob.path)
        observed_blobs.append(
            {"name": blob.name, "path": blob.path, "expected": blob.sha, "observed": observed}
        )
        if observed != blob.sha:
            failures.append(
                f"blob mismatch {blob.path}: expected {blob.sha}, observed {observed}"
            )
        root_paths.append(source_path)

    bishop_root = agda_root / "vendor" / "bishop"
    if not bishop_root.exists():
        failures.append("vendor/bishop checkout is missing")
        observed_bishop_commit = ""
    else:
        observed_bishop_commit = run("git", "rev-parse", "HEAD", cwd=bishop_root)
        if observed_bishop_commit != expected_bishop_commit:
            failures.append(
                "Bishop submodule mismatch: "
                f"expected {expected_bishop_commit}, observed {observed_bishop_commit}"
            )

    observed_bindings: list[dict[str, object]] = []
    for binding in bindings:
        owner = blob_by_name.get(binding.owner_blob)
        if owner is None:
            failures.append(
                f"binding {binding.name} refers to unknown blob {binding.owner_blob}"
            )
            continue
        source_path = agda_root / owner.path
        if not source_path.exists():
            continue
        source_text = source_path.read_text(encoding="utf-8")
        present = declaration_present(source_text, binding.agda_declaration)
        observed_bindings.append(
            {
                "binding": binding.name,
                "owner": owner.path,
                "agda_declaration": binding.agda_declaration,
                "lean_owner": binding.lean_owner,
                "lean_declaration": binding.lean_declaration,
                "present": present,
            }
        )
        if not present:
            failures.append(
                f"declaration {binding.agda_declaration} not found in {owner.path}"
            )

    closure_paths = recursive_import_closure(agda_root, root_paths)
    closure = [rel_display(agda_root, p) for p in closure_paths]

    receipt = {
        "agda_commit": {
            "expected": expected_agda_commit,
            "observed": observed_agda_commit,
        },
        "bishop_submodule": {
            "expected": expected_bishop_commit,
            "observed": observed_bishop_commit,
        },
        "load_bearing_blobs": observed_blobs,
        "theorem_bindings": observed_bindings,
        "recursive_import_closure": closure,
        "failures": failures,
    }

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    if failures:
        for failure in failures:
            print(f"ERROR: {failure}", file=sys.stderr)
        return 1

    write_lean_certificate(
        args.out_lean,
        blobs,
        bindings,
        observed_bishop_commit,
        observed_agda_commit,
        closure,
    )
    print(
        f"verified {len(blobs)} load-bearing blobs, "
        f"{len(bindings)} declaration bindings, "
        f"{len(closure)} files in recursive import closure"
    )
    print(f"JSON receipt: {args.out_json}")
    print(f"Lean certificate: {args.out_lean}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
