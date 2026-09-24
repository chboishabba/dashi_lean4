#!/usr/bin/env python3
"""Generate the project-local Agda dependency closure needed for route-B replay.

This is the kernel-replay stage after route_b_agda_replay_probe.py.

Starting from the seven content-addressed Agda roots, recursively transliterate
all project-local dependencies using the repository's retained agda2lean.py.
Generated modules are staged into a caller-selected AgdaVendor directory so
Lean's existing AgdaVendor library can elaborate them.

The script fails rather than substituting a hand-written theorem if:
- a dependency cannot be located in the live Agda source tree;
- a module lies outside the supported Agda→Lean fragment;
- a root declaration named by the binding manifest disappears.

This script itself does not claim success.  A successful CI invocation followed
by Lean elaboration of the generated roots is the replay receipt.
"""

from __future__ import annotations

import argparse
import importlib.util
import pathlib
import shutil
import sys
from collections import deque


ROOTS: dict[str, tuple[str, ...]] = {
    "DASHI/Moonshine/BishopRound11MachinSetoidComplexInstanceExact.agda": (
        "round11MachinExpConverges",
        "round11MachinSineConverges",
        "round11MachinCosineConverges",
        "round11MachinAtanOneFifthConverges",
        "round11MachinAtanOneTwoHundredThirtyNinthConverges",
    ),
    "DASHI/Foundations/BishopMachinArctanConstructionExact.agda": (
        "bishopMachinPi",
    ),
    "DASHI/Foundations/BishopExponentialSeriesConvergenceExact.agda": (
        "bishopExpConverges",
    ),
    "DASHI/Foundations/BishopConcreteTrigSeriesConvergenceExact.agda": (
        "concreteSineSeriesConverges",
        "concreteCosineSeriesConverges",
    ),
    "DASHI/Analysis/BishopSetoidComplexExact.agda": (
        "expC",
        "expCongruent",
    ),
    "DASHI/Moonshine/JInvariantEisensteinBishopSetoidFiniteQSeriesExact.agda": (
        "qOf",
        "e4Truncated",
        "e6Truncated",
        "discriminantNumeratorTruncated",
    ),
    "DASHI/Moonshine/JInvariantEisensteinBishopSetoidExtractionExact.agda": (
        "mapQ",
        "mapE4",
        "mapE6",
        "mapDiscriminantNumerator",
    ),
}


def load_translator(repo_root: pathlib.Path):
    path = repo_root / "DASHI/output-final_aristotle/tools/agda2lean.py"
    spec = importlib.util.spec_from_file_location("dashi_agda2lean_replay", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load translator: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def live_module_map(translator, source_root: pathlib.Path) -> dict[str, pathlib.Path]:
    result: dict[str, pathlib.Path] = {}
    for path in source_root.rglob("*.agda"):
        module = translator.module_of(str(path))
        if not module:
            continue
        # Prefer the shortest path if duplicate module declarations occur.
        old = result.get(module)
        if old is None or len(path.parts) < len(old.parts):
            result[module] = path
    return result


def full_module_universe(translator, live: dict[str, pathlib.Path]) -> set[str]:
    modules = set(live)
    for path in translator.corpus_files():
        mod = translator.module_of(path)
        if mod:
            modules.add(mod)
    return modules


def has_decl(lean: str, name: str) -> bool:
    for line in lean.splitlines():
        stripped = line.strip()
        if stripped.startswith("--") or stripped.startswith("/-"):
            continue
        if (
            stripped.startswith(name + " :")
            or stripped.startswith(name + " ")
            or stripped.startswith("«" + name + "» :")
            or stripped.startswith("«" + name + "» ")
        ):
            return True
    return False


def module_dest(dest_root: pathlib.Path, module: str) -> pathlib.Path:
    return dest_root.joinpath(*module.split(".")).with_suffix(".lean")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--source-root", required=True)
    ap.add_argument("--dest", required=True)
    ap.add_argument("--roots-file", required=True)
    args = ap.parse_args()

    repo_root = pathlib.Path(__file__).resolve().parents[1]
    source_root = pathlib.Path(args.source_root).resolve()
    dest_root = pathlib.Path(args.dest).resolve()
    roots_file = pathlib.Path(args.roots_file).resolve()

    translator = load_translator(repo_root)
    live = live_module_map(translator, source_root)
    universe = full_module_universe(translator, live)

    root_modules: list[str] = []
    expected_by_module: dict[str, tuple[str, ...]] = {}
    for rel, expected in ROOTS.items():
        path = source_root / rel
        if not path.is_file():
            raise SystemExit(f"missing route-B replay root: {rel}")
        mod = translator.module_of(str(path))
        if not mod:
            raise SystemExit(f"missing module header: {rel}")
        root_modules.append(mod)
        expected_by_module[mod] = expected
        live[mod] = path

    queue = deque(root_modules)
    seen: set[str] = set()
    generated: dict[str, str] = {}
    failures: list[str] = []

    while queue:
        mod = queue.popleft()
        if mod in seen:
            continue
        seen.add(mod)

        path = live.get(mod)
        if path is None:
            # A dependency already supplied by the retained AgdaVendor archive
            # does not need regeneration.  It will be resolved by Lean from the
            # existing library.
            continue

        out = translator.transliterate(str(path), universe)
        if not out.ok:
            reasons = "; ".join(sorted(set(out.reasons)))
            failures.append(f"{mod}: {reasons}")
            continue

        generated[mod] = out.lean
        for dep in out.deps:
            if dep in live and dep not in seen:
                queue.append(dep)

    if failures:
        print("Agda kernel-replay closure is outside the supported fragment:", file=sys.stderr)
        for failure in failures:
            print(f"  - {failure}", file=sys.stderr)
        return 1

    # Verify the load-bearing root declarations before staging anything.
    for mod, expected in expected_by_module.items():
        lean = generated.get(mod)
        if lean is None:
            print(f"root was not generated: {mod}", file=sys.stderr)
            return 1
        missing = [name for name in expected if not has_decl(lean, name)]
        if missing:
            print(
                f"{mod}: expected declarations missing after translation: "
                + ", ".join(missing),
                file=sys.stderr,
            )
            return 1

    dest_root.mkdir(parents=True, exist_ok=True)
    staged: list[pathlib.Path] = []
    for mod, lean in sorted(generated.items()):
        dest = module_dest(dest_root, mod)
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(lean, encoding="utf-8")
        staged.append(dest)

    roots_file.parent.mkdir(parents=True, exist_ok=True)
    roots_file.write_text(
        "\n".join(str(module_dest(dest_root, mod)) for mod in root_modules) + "\n",
        encoding="utf-8",
    )

    print(f"generated {len(staged)} project-local AgdaVendor modules")
    print(f"root list: {roots_file}")
    for mod in root_modules:
        print(f"  replay-root {mod}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
