#!/usr/bin/env python3
"""Apply the 2026-09-10 combined Lean + Agda consolidation tranche.

Policy (never silently overwrite, never drop a lane):

  * ``identical``        — no action, recorded.
  * ``absent-locally``   — adopted at the natural local path, except for
                           declared-excluded build artefacts, which are staged
                           under ``Provenance/spine-20260910/donor-artifact/``.
  * ``divergent``        — the local version is retained and the donor version
                           is preserved verbatim under
                           ``Provenance/spine-20260910/donor-version/``.  Both
                           sha256 values are recorded in the ledger, so the
                           donor content is recoverable and the decision is
                           auditable.  (For this tranche the reconciliation
                           test in ``spine_intake_index.py`` found the local
                           version equal-or-ahead in every divergence.)

Writes ``SPINE_INTAKE_LEDGER.csv`` with a row per delivered path.

Usage: python3 scripts/spine_intake_apply.py <tranche-root> [project-root] [--apply]
"""

from __future__ import annotations

import csv
import hashlib
import os
import shutil
import sys

PROV = os.path.join("Provenance", "spine-20260910")
# Build artefacts the handoff declares excluded; if one is delivered anyway it
# is staged rather than injected into the source tree.
ARTEFACT_SUFFIXES = (".agdai", ".olean", ".ilean")


def sha256_of(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def copy(src: str, dst: str, apply: bool) -> None:
    if not apply:
        return
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    shutil.copy2(src, dst)


def main() -> int:
    tranche = sys.argv[1]
    project = sys.argv[2] if len(sys.argv) > 2 else "."
    apply = "--apply" in sys.argv

    rows = []
    for lang, payload, localdir in (
        ("agda", os.path.join(tranche, "dashi_agda"), os.path.join(project, "Agda")),
        ("lean", os.path.join(tranche, "dashi_lean4"), os.path.join(project, "Lean")),
    ):
        for base, _dirs, files in os.walk(payload):
            for f in sorted(files):
                dp = os.path.join(base, f)
                rel = os.path.relpath(dp, payload).replace(os.sep, "/")
                lp = os.path.join(localdir, rel)
                dsha = sha256_of(dp)
                if os.path.exists(lp):
                    lsha = sha256_of(lp)
                    if lsha == dsha:
                        rows.append((lang, rel, "identical-no-action", rel, dsha, lsha, ""))
                        continue
                    keep = os.path.join(project, PROV, "donor-version", lang, rel)
                    copy(dp, keep, apply)
                    rows.append((lang, rel, "retained-local-donor-preserved",
                                 os.path.relpath(keep, project).replace(os.sep, "/"),
                                 dsha, lsha,
                                 "local version retained; donor version preserved verbatim"))
                    continue
                if rel.endswith(ARTEFACT_SUFFIXES):
                    keep = os.path.join(project, PROV, "donor-artifact", lang, rel)
                    copy(dp, keep, apply)
                    rows.append((lang, rel, "staged-donor-artifact",
                                 os.path.relpath(keep, project).replace(os.sep, "/"),
                                 dsha, "",
                                 "build artefact the handoff declares excluded; staged, not injected"))
                    continue
                copy(dp, lp, apply)
                rows.append((lang, rel, "adopted-new",
                             os.path.relpath(lp, project).replace(os.sep, "/"), dsha, "", ""))

    out = os.path.join(project, "SPINE_INTAKE_LEDGER.csv")
    with open(out, "w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["lang", "donor_path", "disposition", "target_path",
                    "sha256_donor", "sha256_local_prior", "note"])
        w.writerows(rows)

    tally: dict[tuple[str, str], int] = {}
    for r in rows:
        tally[(r[0], r[2])] = tally.get((r[0], r[2]), 0) + 1
    for k in sorted(tally):
        print(k, tally[k])
    print("total", len(rows), "apply" if apply else "dry-run")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
