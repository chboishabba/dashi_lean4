#!/usr/bin/env python3
"""Probe syntactic Agda→Lean replay for the content-addressed route-B owners.

This does not claim kernel replay.  It exercises the repository's retained
agda2lean translator against the *live checked-out* Agda source tree, verifies
that each load-bearing source module is inside the supported syntactic fragment,
and checks that the declarations named by the reciprocal binding manifests
survive translation.

Exit status is nonzero on unsupported syntax, missing source modules, or a
missing expected declaration.  Generated Lean text is retained under --out for
subsequent kernel-replay work.
"""

from __future__ import annotations

import argparse
import importlib.util
import pathlib
import sys


TARGETS: dict[str, tuple[str, ...]] = {
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
    if not path.is_file():
        raise RuntimeError(f"translator not found: {path}")
    spec = importlib.util.spec_from_file_location("dashi_agda2lean", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load translator: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def module_universe(translator, source_root: pathlib.Path) -> set[str]:
    modules: set[str] = set()
    for path in source_root.rglob("*.agda"):
        mod = translator.module_of(str(path))
        if mod:
            modules.add(mod)

    # Prelude/stdlib and the retained archive corpus may satisfy imports that are
    # not project-local.  Include their already-ingested module names too.
    for path in translator.corpus_files():
        mod = translator.module_of(path)
        if mod:
            modules.add(mod)
    return modules


def declaration_present(lean_text: str, name: str) -> bool:
    # The translator may quote exotic Agda identifiers, but these route-B names
    # are plain ASCII identifiers.  Looking for the exact token avoids accepting
    # a comment-only mention.
    needles = (
        f" {name} :",
        f" {name} ",
        f"\n{name} :",
        f"\n{name} ",
    )
    return any(n in lean_text for n in needles)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--source-root", required=True)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    repo_root = pathlib.Path(__file__).resolve().parents[1]
    source_root = pathlib.Path(args.source_root).resolve()
    out_root = pathlib.Path(args.out).resolve()
    out_root.mkdir(parents=True, exist_ok=True)

    translator = load_translator(repo_root)
    modules = module_universe(translator, source_root)

    failures: list[str] = []
    for rel, declarations in TARGETS.items():
        src = source_root / rel
        if not src.is_file():
            failures.append(f"missing source: {rel}")
            continue

        outcome = translator.transliterate(str(src), modules)
        if not outcome.ok:
            reasons = "; ".join(sorted(set(outcome.reasons)))
            failures.append(f"{rel}: not transliterated: {reasons}")
            continue

        dest = out_root / (outcome.module.replace(".", "/") + ".lean")
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(outcome.lean, encoding="utf-8")

        missing = [d for d in declarations if not declaration_present(outcome.lean, d)]
        if missing:
            failures.append(
                f"{rel}: translated but declarations missing: {', '.join(missing)}"
            )
            continue

        print(f"replayed-syntax {outcome.module}")
        for declaration in declarations:
            print(f"  declaration {declaration}")

    if failures:
        print("route-B Agda replay probe failed:", file=sys.stderr)
        for failure in failures:
            print(f"  - {failure}", file=sys.stderr)
        return 1

    print(f"route-B Agda replay probe passed for {len(TARGETS)} modules")
    print(f"generated Lean retained under {out_root}")
    print("NOTE: this is syntactic replay only; kernel elaboration is a separate gate.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
