#!/usr/bin/env python3
"""Drift guard for the Agda mirrors consumed by the Level-II/III spine.

What this does
--------------
For every (Lean mirror, cited Agda source) pair consumed by the Level-II/III
integration spine, record a SHA-256 digest of the source file and detect whether
that file has changed since the digest was recorded.

What this does *not* do
-----------------------
It does not typecheck Agda, and it says nothing about whether a mirror faithfully
states its original.  It answers exactly one question: *did the source surface we
transcribed change?*

Usage
-----
    python3 scripts/mirror_drift.py            # check against the manifest
    python3 scripts/mirror_drift.py --update   # (re)write the manifest
    python3 scripts/mirror_drift.py --lean     # print the Lean table rows
    python3 scripts/mirror_drift.py --verify-lean
                                               # check the digests pinned in
                                               # Lean/Integration/MirrorDrift.lean

Exit status is non-zero when drift, a missing source, or a Lean/manifest
mismatch is detected.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "MIRROR_DRIFT_MANIFEST.json"
LEAN_TABLE = ROOT / "Lean" / "Integration" / "MirrorDrift.lean"

# The mirrors consumed by the Level-II/III spine, and the Agda files their
# headers cite.  Keep in step with `Integration.MirrorDrift.consumedMirrors`.
PAIRS: list[tuple[str, str]] = [
    ("Lean/AgdaMirror/MonsterOntos.lean", "Agda/MonsterOntos.agda"),
    ("Lean/AgdaMirror/NonFactorabilityKernels.lean",
     "Agda/DASHI/Core/IntersectionalNonFactorability.agda"),
    ("Lean/AgdaMirror/NonFactorabilityKernels.lean",
     "Agda/DASHI/Core/ReopenableConsumerInterventionKernelExact.agda"),
    ("Lean/AgdaMirror/NonFactorabilityKernels.lean",
     "Agda/DASHI/Core/SocioEcologicalFeedbackExact.agda"),
    ("Lean/AgdaMirror/NonFactorabilityKernels.lean",
     "Agda/DASHI/Education/EarlyLearningIntersectionalCapabilityExact.agda"),
    ("Lean/AgdaMirror/NonFactorabilityKernels.lean",
     "Agda/DASHI/Education/EarlyLearningMultiOutcomeVectorExact.agda"),
    ("Lean/AgdaMirror/FibreAveraging.lean",
     "Agda/DASHI/Analysis/NormalizedFibreAveragingExact.agda"),
    ("Lean/AgdaMirror/FibreAveraging.lean",
     "Agda/DASHI/Analysis/WeightedCoarseFineOrthogonalExact.agda"),
    ("Lean/AgdaMirror/InteractionTables.lean",
     "Agda/DASHI/Visualisation/FiniteAnisotropicKernelExact.agda"),
    ("Lean/AgdaMirror/InteractionTables.lean",
     "Agda/DASHI/Visualisation/SelfConsistentEventRendererExact.agda"),
    ("Lean/AgdaMirror/InteractionTables.lean",
     "Agda/DASHI/Visualisation/MeasureFieldAdapterExact.agda"),
    ("Lean/AgdaMirror/AuthorityRoutes.lean",
     "Agda/DASHI/Promotion/ExplanationAuthorityBoundaryCore.agda"),
    ("Lean/AgdaMirror/AuthorityRoutes.lean",
     "Agda/DASHI/Culture/CulturalProvenanceBoundaryCore.agda"),
    ("Lean/AgdaMirror/AuthorityRoutes.lean",
     "Agda/DASHI/Philosophy/CulturalProvenanceAdapter.agda"),
    ("Lean/AgdaMirror/EntitlementRoutes.lean",
     "Agda/DASHI/Education/EarlyLearningEntitlementRouteSeparationExact.agda"),
]

# Cited by `Integration.ClaimTransportGeometry` and not present in this cutset.
ABSENT_CITATIONS: list[str] = ["FormalClaimTransportGeometryExact.agda"]

DIGEST_PREFIX = 16


def digest(path: Path) -> str | None:
    if not path.is_file():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()[:DIGEST_PREFIX]


def current() -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for mirror, source in PAIRS:
        d = digest(ROOT / source)
        rows.append({
            "mirror": mirror,
            "source": source,
            "digest": d,
            "status": "present" if d else "sourceAbsent",
        })
    for cited in ABSENT_CITATIONS:
        rows.append({
            "mirror": "Lean/Integration/ClaimTransportGeometry.lean",
            "source": cited,
            "digest": None,
            "status": "sourceAbsent",
        })
    return rows


def cmd_update() -> int:
    rows = current()
    MANIFEST.write_text(json.dumps({"digestPrefixLength": DIGEST_PREFIX, "rows": rows},
                                   indent=2) + "\n")
    print(f"wrote {MANIFEST.relative_to(ROOT)} with {len(rows)} rows")
    return 0


def cmd_check() -> int:
    if not MANIFEST.is_file():
        print("no manifest; run with --update", file=sys.stderr)
        return 2
    recorded = {(r["mirror"], r["source"]): r for r in json.loads(MANIFEST.read_text())["rows"]}
    now = {(r["mirror"], r["source"]): r for r in current()}
    problems = 0
    for key, row in now.items():
        old = recorded.get(key)
        if old is None:
            print(f"UNRECORDED  {key[0]} <- {key[1]}")
            problems += 1
        elif old["digest"] != row["digest"]:
            print(f"DRIFTED     {key[0]} <- {key[1]}: {old['digest']} -> {row['digest']}")
            problems += 1
    for key in recorded:
        if key not in now:
            print(f"DROPPED     {key[0]} <- {key[1]}")
            problems += 1
    absent = [k for k, r in now.items() if r["status"] == "sourceAbsent"]
    print(f"{len(now)} consumed (mirror, source) pairs; {len(absent)} with no source in this "
          f"cutset; {problems} problem(s)")
    for k in absent:
        print(f"  sourceAbsent: {k[1]} (cited by {k[0]})")
    return 1 if problems else 0


def cmd_lean() -> int:
    for row in current():
        d = row["digest"] or ""
        status = ".present" if row["digest"] else ".sourceAbsent"
        print(f'  , {{ mirror := "{row["mirror"]}"\n'
              f'      source := "{row["source"]}"\n'
              f'      digest := "{d}"\n'
              f'      status := {status} }}')
    return 0


def cmd_verify_lean() -> int:
    if not LEAN_TABLE.is_file():
        print(f"missing {LEAN_TABLE}", file=sys.stderr)
        return 2
    text = LEAN_TABLE.read_text()
    entries = re.findall(
        r'mirror\s*:=\s*"([^"]*)"\s*\n\s*source\s*:=\s*"([^"]*)"\s*\n\s*digest\s*:=\s*"([^"]*)"',
        text)
    pinned = {(m, s): d for m, s, d in entries}
    now = {(r["mirror"], r["source"]): (r["digest"] or "") for r in current()}
    problems = 0
    for key, d in now.items():
        if key not in pinned:
            print(f"LEAN MISSING  {key[0]} <- {key[1]}")
            problems += 1
        elif pinned[key] != d:
            print(f"LEAN STALE    {key[0]} <- {key[1]}: pinned {pinned[key]}, actual {d}")
            problems += 1
    for key in pinned:
        if key not in now:
            print(f"LEAN EXTRA    {key[0]} <- {key[1]}")
            problems += 1
    print(f"{len(pinned)} rows pinned in Lean; {problems} problem(s)")
    return 1 if problems else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--update", action="store_true")
    ap.add_argument("--lean", action="store_true")
    ap.add_argument("--verify-lean", action="store_true")
    args = ap.parse_args()
    if args.update:
        return cmd_update()
    if args.lean:
        return cmd_lean()
    if args.verify_lean:
        return cmd_verify_lean()
    return cmd_check()


if __name__ == "__main__":
    raise SystemExit(main())
