#!/usr/bin/env python3
"""Intake of the 2026-09-10 full cross-pollination handoff into the project tree.

Policy (per the 2026-09-10 handoff, which supersedes the topic-filtered
2026-09-09 cutset):

  * every donor payload path is preserved, whatever its lane -- no topic-based
    refusal (YM/NS, physics, law, ecology, optics, Moonshine, Goedel/Turing,
    game theory and the rest are all indexed and kept);
  * ``absent-locally``  -> copied in;
  * ``divergent`` and the donor preserves every local top-level declaration and
    every local ``DASHI.*`` import -> reconciled to the donor, with the
    pre-intake local sha256 recorded;
  * ``divergent`` and the donor would drop local declarations/imports -> the
    local version is kept and the donor version is preserved verbatim under
    ``Provenance/donor-<commit>/`` with the exact reason;
  * ``identical`` -> nothing to do.

Nothing here is a typecheck: no Agda toolchain exists in this environment.
Operational import into build aggregates is a separate, later decision.

Usage: python3 scripts/xpoll_intake.py <donor-root> [project-root]
"""

from __future__ import annotations

import csv
import os
import shutil
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from xpoll_index import analyse, sha256_of  # noqa: E402

DONOR_COMMIT = "1d3cb03c1dec2d1b1293ada9684b168fd963da8f"


def main() -> int:
    donor_root = sys.argv[1]
    project = sys.argv[2] if len(sys.argv) > 2 else "."
    payload = os.path.join(donor_root, "dashi_agda")
    local_agda = os.path.join(project, "Agda")
    conflict_root = os.path.join(project, "Provenance", "donor-" + DONOR_COMMIT[:12])

    rows = []
    counts = {"new": 0, "reconciled": 0, "conflict-kept-local": 0, "identical": 0}
    for base, _dirs, files in os.walk(payload):
        for f in sorted(files):
            if not f.endswith(".agda"):
                continue
            dp = os.path.join(base, f)
            rel = os.path.relpath(dp, payload)
            lp = os.path.join(local_agda, rel)
            dsha = sha256_of(dp)
            if not os.path.exists(lp):
                os.makedirs(os.path.dirname(lp), exist_ok=True)
                shutil.copy2(dp, lp)
                action, reason, lsha = "new", "", ""
            else:
                lsha = sha256_of(lp)
                if lsha == dsha:
                    action, reason = "identical", ""
                else:
                    with open(lp, encoding="utf-8", errors="replace") as fh:
                        li = analyse(fh.read())
                    with open(dp, encoding="utf-8", errors="replace") as fh:
                        di = analyse(fh.read())
                    md = sorted(set(li["decls"]) - set(di["decls"]))
                    mi = sorted(
                        {i for i in li["imports"] if i.startswith("DASHI.")}
                        - set(di["imports"])
                    )
                    if md or mi:
                        dest = os.path.join(conflict_root, rel)
                        os.makedirs(os.path.dirname(dest), exist_ok=True)
                        shutil.copy2(dp, dest)
                        action = "conflict-kept-local"
                        reason = "donor drops local declarations [%s]; donor drops local DASHI imports [%s]" % (
                            ",".join(md),
                            ",".join(mi),
                        )
                    else:
                        shutil.copy2(dp, lp)
                        action, reason = "reconciled", "donor preserves all local declarations and DASHI imports"
            counts[action] += 1
            rows.append(
                dict(
                    path="Agda/" + rel.replace(os.sep, "/"),
                    action=action,
                    donor_sha256=dsha,
                    prior_local_sha256=lsha,
                    donor_commit=DONOR_COMMIT,
                    reason=reason,
                )
            )

    # NS worker supplement (source + reports), preserved verbatim
    ns_src = os.path.join(donor_root, "ns_worker_result")
    ns_dest = os.path.join(project, "Provenance", "ns_worker_result")
    for base, _dirs, files in os.walk(ns_src):
        for f in sorted(files):
            sp = os.path.join(base, f)
            rel = os.path.relpath(sp, ns_src)
            dp = os.path.join(ns_dest, rel)
            os.makedirs(os.path.dirname(dp), exist_ok=True)
            shutil.copy2(sp, dp)
            rows.append(
                dict(
                    path="Provenance/ns_worker_result/" + rel.replace(os.sep, "/"),
                    action="new" if not os.path.exists(dp) else "ns-supplement",
                    donor_sha256=sha256_of(sp),
                    prior_local_sha256="",
                    donor_commit=DONOR_COMMIT,
                    reason="NS worker source/report supplement, preserved verbatim; not built",
                )
            )

    ledger = os.path.join(project, "XPOLL_LEDGER.csv")
    with open(ledger, "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(
            fh,
            fieldnames=[
                "path",
                "action",
                "donor_sha256",
                "prior_local_sha256",
                "donor_commit",
                "reason",
            ],
        )
        w.writeheader()
        w.writerows(rows)
    print(counts)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
