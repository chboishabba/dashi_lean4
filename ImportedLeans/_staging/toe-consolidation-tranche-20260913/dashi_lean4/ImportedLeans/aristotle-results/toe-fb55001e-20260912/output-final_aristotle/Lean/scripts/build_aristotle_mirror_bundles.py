#!/usr/bin/env python3
"""Build source-only, lane-scoped Aristotle bundles for the Lean mirror."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import sys
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / "config" / "aristotle_mirror_wave1.json"
DEFAULT_OUTPUT = ROOT / "outputs" / "aristotle_mirror_waves"
LEAN_SOURCE_SUFFIXES = {".lean", ".json"}
HELPER_SUFFIXES = {".py", ".sh"}
IGNORED_DIRS = {
    ".git", ".cache", ".tmp-nix-cache", ".tmp-nix-state", ".agda",
    ".venv", ".venv-fluid", ".playwright-mcp", "_build", "build",
    "MAlonzo", "artifacts", "outputs", "temp-DOWNLOADED", "__pycache__",
}


def digest_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_json(path: Path, payload: object) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def copy_file(source: Path, destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, destination)


def first_namespace_root(path: Path) -> str | None:
    for raw_line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        stripped = raw_line.strip()
        if not stripped or stripped.startswith("--"):
            continue
        if not stripped.startswith("namespace "):
            continue
        namespace = stripped.split(maxsplit=1)[1].strip()
        return namespace.split(".", 1)[0].strip("«»")
    return None


def should_skip_lean_path(path: Path) -> bool:
    if not path.is_file() or ".git" in path.parts:
        return True
    if any(part in {".lake", "target", "build", "_build", "__pycache__", ".venv"} for part in path.parts):
        return True
    if "output-final_aristotle" in path.parts or "Klüver’s Form Constants_aristotle" in path.parts:
        return True
    return False


def collect_agda_mirror_imports(source: Path) -> set[str]:
    imported: set[str] = set()
    for path in sorted(source.rglob("*.lean")):
        if not path.is_file() or any(part in IGNORED_DIRS for part in path.parts):
            continue
        for raw_line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
            stripped = raw_line.strip()
            if not stripped.startswith("import "):
                continue
            for token in stripped.split()[1:]:
                if token.startswith("AgdaMirror."):
                    imported.add(token.split(".", 1)[1].split(".", 1)[0].strip("«»"))
    return imported


def parse_agda_module(path: Path, repo: Path) -> tuple[str, tuple[str, ...]]:
    module = ".".join(path.relative_to(repo).with_suffix("").parts)
    imports: list[str] = []
    in_block_comment = 0
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if line.startswith("module "):
            pieces = line.split()
            if len(pieces) >= 2 and pieces[1] != "_":
                module = pieces[1].split("{")[0]
        if in_block_comment:
            if "-}" in line:
                in_block_comment -= 1
            continue
        if line.startswith("--"):
            continue
        if "{-#" in line:
            continue
        if "{-#" not in line and "{-" in line:
            in_block_comment += line.count("{-") - line.count("-}")
            if in_block_comment:
                continue
        if line.startswith("import ") or line.startswith("open import "):
            words = line.split()
            try:
                index = words.index("import")
                imports.append(words[index + 1].rstrip(";"))
            except (ValueError, IndexError):
                pass
    return module, tuple(dict.fromkeys(imports))


def build_agda_index(repo: Path) -> dict[str, tuple[Path, tuple[str, ...]]]:
    index: dict[str, tuple[Path, tuple[str, ...]]] = {}
    for path in sorted(repo.rglob("*.agda")):
        if not path.is_file() or any(part in IGNORED_DIRS for part in path.parts):
            continue
        module, imports = parse_agda_module(path, repo)
        index.setdefault(module, (path, imports))
    return index


def forward_cone(repo: Path, index: dict[str, tuple[Path, tuple[str, ...]]], targets: Iterable[str]) -> list[Path]:
    modules_by_path = {path.relative_to(repo).as_posix(): module for module, (path, _) in index.items()}
    del modules_by_path
    target_modules: list[str] = []
    for target in targets:
        path = (repo / target).resolve()
        if not path.is_file():
            raise FileNotFoundError(f"Agda target does not exist: {target}")
        module, _ = parse_agda_module(path, repo)
        target_modules.append(module)

    seen: set[str] = set()
    queue = list(target_modules)
    selected: set[Path] = set()
    while queue:
        module = queue.pop()
        if module in seen:
            continue
        seen.add(module)
        record = index.get(module)
        if record is None:
            continue
        path, imports = record
        selected.add(path)
        queue.extend(imported for imported in imports if imported not in seen)
    return sorted(selected)


def copy_lean_baseline(source: Path, destination: Path, agda_mirror_roots: set[str]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for path in sorted(source.rglob("*")):
        if should_skip_lean_path(path):
            continue
        relative = path.relative_to(source)
        if path.suffix not in LEAN_SOURCE_SUFFIXES and path.name not in {"lean-toolchain", "README.md"}:
            continue
        if path.name == "lakefile.toml":
            continue
        destination_path = destination / relative
        if path.suffix == ".lean":
            if relative.parent == Path(".") and path.stem in agda_mirror_roots and path.stem not in {"Main", "Main11", "AgdaMirror", "DashiPerf"}:
                destination_path = destination / "AgdaMirror" / f"{path.stem}.lean"
        copy_file(path, destination_path)
        rows.append({"path": relative.as_posix(), "bytes": path.stat().st_size, "sha256": digest_file(path)})
    return rows


def collect_lean_roots(source: Path, agda_mirror_roots: set[str]) -> list[str]:
    roots: set[str] = {"AgdaMirror", "DashiPerf"}
    for path in sorted(source.rglob("*.lean")):
        if should_skip_lean_path(path):
            continue
        relative = path.relative_to(source)
        if relative.parent == Path(".") and path.stem in agda_mirror_roots and path.stem not in {"Main", "Main11", "AgdaMirror", "DashiPerf"}:
            continue
        if relative.parent == Path("."):
            roots.add(path.stem)
        else:
            roots.add(relative.parts[0])
    return sorted(roots)


def write_lakefile_lean(path: Path, roots: list[str]) -> None:
    roots_literal = ", ".join(f"`{name}" for name in roots)
    path.write_text(
        "import Lake\n"
        "open Lake DSL\n\n"
        'package «RequestProject» where\n\n'
        'require mathlib from git\n'
        '  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"\n\n'
        "@[default_target]\n"
        "lean_lib «Wave1Mirror» where\n"
        '  srcDir := "lean-baseline"\n'
        f"  roots := #[{roots_literal}]\n",
        encoding="utf-8",
    )


def copy_helpers(helper_paths: Iterable[str], destination: Path) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for raw in helper_paths:
        source = Path(raw).resolve() if Path(raw).is_absolute() else (ROOT / raw).resolve()
        if not source.is_file() or source.suffix not in HELPER_SUFFIXES:
            raise FileNotFoundError(f"Helper script is missing or unsupported: {raw}")
        target = destination / Path(raw).name
        copy_file(source, target)
        rows.append({"path": raw, "bytes": source.stat().st_size, "sha256": digest_file(source)})
    return rows


def worker_brief(wave_id: str, lane: dict[str, object], target_paths: list[str]) -> str:
    return f"""# Aristotle Lean mirror worker brief

Wave: `{wave_id}`
Lane: `{lane['id']}`
Claim: {lane['claim']}

## Task

Mirror the assigned Agda surfaces into the Lean4 baseline. Work only on the
assigned lane. Preserve existing Lean namespaces and reuse existing mirrored
definitions instead of duplicating them.

Assigned Agda targets:

{''.join(f'- `{path}`\n' for path in target_paths)}

## Required honesty boundary

- Agda `postulate`s become explicit Lean hypotheses or structure fields.
- Do not add `sorry`, `admit`, Lean `axiom`, or fake `rfl` witnesses.
- Preserve all authority boundaries and keep Clay promotion flags false.
- Do not claim an Agda theorem is proved merely because a Lean interface was
  transcribed.

## Required result

Add or update only lane-owned files under `lean-baseline/`. Run
`lake build` from the bundle root, report the exact command and result, list changed files, and list any remaining imported
hypotheses or blocked theorem surfaces.
"""


def build_lane(manifest: dict[str, object], lane: dict[str, object], output: Path, index: dict[str, tuple[Path, tuple[str, ...]]]) -> dict[str, object]:
    lane_id = str(lane["id"])
    lane_dir = output / lane_id
    lane_dir.mkdir(parents=True, exist_ok=True)
    agda_source = Path(str(manifest["agda_root"])).resolve()
    targets = [str(item) for item in lane["targets"]]  # type: ignore[index]
    agda_files = forward_cone(agda_source, index, targets)
    agda_root = lane_dir / "agda"
    agda_rows: list[dict[str, object]] = []
    for source in agda_files:
        relative = source.relative_to(agda_source)
        copy_file(source, agda_root / relative)
        agda_rows.append({"path": relative.as_posix(), "bytes": source.stat().st_size, "sha256": digest_file(source)})

    for lib_file in agda_source.glob("*.agda-lib"):
        copy_file(lib_file, agda_root / lib_file.name)

    lean_root = lane_dir / "lean-baseline"
    lean_source = Path(str(manifest["lean_baseline"])).resolve()
    copy_file(lean_source / "lean-toolchain", lane_dir / "lean-toolchain")
    agda_mirror_roots = collect_agda_mirror_imports(lean_source)
    lean_rows = copy_lean_baseline(lean_source, lean_root, agda_mirror_roots)
    write_lakefile_lean(lane_dir / "lakefile.lean", collect_lean_roots(lean_source, agda_mirror_roots))
    helper_rows = copy_helpers([str(item) for item in manifest["helper_scripts"]], lane_dir / "helpers")  # type: ignore[index]
    (lane_dir / "WORKER_BRIEF.md").write_text(worker_brief(str(manifest["wave_id"]), lane, targets), encoding="utf-8")

    payload = {
        "schema": manifest["schema"],
        "wave_id": manifest["wave_id"],
        "lane_id": lane_id,
        "claim": lane["claim"],
        "targets": targets,
        "agda_files": agda_rows,
        "lean_baseline_files": lean_rows,
        "helper_files": helper_rows,
        "excluded": ["agda-toolchain", ".git", "*.agdai", "MAlonzo", "_build", ".lake", "target", "PDF/log/cache/generated data"],
    }
    write_json(lane_dir / "bundle-manifest.json", payload)
    return {
        "id": lane_id,
        "bundle_dir": str(lane_dir.resolve()),
        "prompt_file": str((lane_dir / "WORKER_BRIEF.md").resolve()),
        "agda_file_count": len(agda_rows),
        "lean_file_count": len(lean_rows),
        "bundle_bytes": sum(int(row["bytes"]) for row in agda_rows + lean_rows + helper_rows),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--clean", action="store_true", help="Remove only the selected output directory first.")
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    output = args.output_dir / str(manifest["wave_id"])
    if args.clean and output.exists():
        shutil.rmtree(output)
    output.mkdir(parents=True, exist_ok=True)
    index = build_agda_index(Path(str(manifest["agda_root"])).resolve())
    lanes = [build_lane(manifest, lane, output, index) for lane in manifest["lanes"]]
    summary = {"schema": manifest["schema"], "wave_id": manifest["wave_id"], "lanes": lanes}
    write_json(output / "wave-manifest.json", summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
