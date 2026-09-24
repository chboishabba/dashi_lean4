#!/usr/bin/env python3
"""Verify, overlay and index the 2026-09-11 current-master Agda delta.

Delivery: ``toe-agda-master-delta-20260911.tar.gz``
Base Agda commit   ``a866c675f60ad2ee5cd5a96f213cdd3e7e50cf26``
Target Agda commit ``4c8ebfb733f5768ce7ed61388cc5272ececd5d0d``

Two payload paths only:

  dashi_agda/DASHI/Reasoning/FibreRoutingGrokkingMoEBrainCrossPollinationExact.agda
  dashi_agda/DASHI/Reasoning/Everything.agda   (rollup, one added import line)

The script is idempotent: rows already present for these paths are rewritten in
place rather than duplicated.  It reuses the analyser of
``scripts/spine_intake_index.py`` so the new rows carry exactly the same
mechanical markers as the 20 074 rows already in ``SPINE_INDEX.csv``.

Outputs / updates, at the project root:

  SPINE_INDEX.csv          rows for the two delta paths (status, markers)
  SPINE_IMPORT_EDGES.csv   import edges of the two delta paths
  SPINE_INTAKE_LEDGER.csv  per-path disposition with donor/prior sha256
  XPOLL_INDEX.csv          same rows in the cross-pollination index schema
  XPOLL_IMPORT_EDGES.csv   same edges in the cross-pollination schema
  XPOLL_LEDGER.csv         cross-pollination disposition rows
  DELTA_20260911_LEDGER.csv  standalone ledger for this delta

Usage: python3 scripts/delta_overlay_20260911.py [project-root]
"""

from __future__ import annotations

import csv
import hashlib
import importlib.util
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(sys.argv[1]) if len(sys.argv) > 1 else os.path.dirname(HERE)

spec = importlib.util.spec_from_file_location(
    "spine_intake_index", os.path.join(HERE, "spine_intake_index.py")
)
sii = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(sii)

DONOR_COMMIT = "4c8ebfb733f5768ce7ed61388cc5272ececd5d0d"
BASE_COMMIT = "a866c675f60ad2ee5cd5a96f213cdd3e7e50cf26"
TARBALL = "toe-agda-master-delta-20260911.tar.gz"
TARBALL_SHA = "28087139cd7b6a8cd99683bd05bca2811f94d374f365fccfff94d55ca0592f98"

# path (relative to Agda/) -> (donor sha256, prior local sha256 or "", disposition)
DELTA = {
    "DASHI/Reasoning/FibreRoutingGrokkingMoEBrainCrossPollinationExact.agda": (
        "0f80173ee5fa3510993a51a440982fa34c7b53112cea577dbeace4c002d1e215",
        "",
        "new-module-adopted",
        "current dashi_agda master; no prior local copy",
    ),
    "DASHI/Reasoning/Everything.agda": (
        "828182dbdcc0ee31380205c85d6aea5210c0293faffb56bb479612c36c8231a8",
        "c62f687c35fd33d5e0aaed4a9ff809f796af6153fd9bb125d8a454c98e8962d6",
        "adopted-donor",
        "donor is strictly additive: single new import line, all local imports retained",
    ),
}

AGDA_ROOT = os.path.join(ROOT, "Agda")


def sha256_of(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def local_modules() -> set[str]:
    mods = set()
    for dirpath, _dirnames, filenames in os.walk(AGDA_ROOT):
        for name in filenames:
            if name.endswith(".agda"):
                rel = os.path.relpath(os.path.join(dirpath, name), AGDA_ROOT)
                mods.add(rel[: -len(".agda")].replace(os.sep, "."))
    return mods


def read_rows(path: str) -> tuple[list[str], list[dict]]:
    with open(path, newline="", encoding="utf-8") as fh:
        reader = csv.DictReader(fh)
        return list(reader.fieldnames or []), list(reader)


def write_rows(path: str, header: list[str], rows: list[dict]) -> None:
    with open(path, "w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=header, lineterminator="\r\n")
        writer.writeheader()
        writer.writerows(rows)


def upsert(path: str, header: list[str], rows: list[dict], key: str,
           new_rows: list[dict]) -> None:
    keys = {r[key] for r in new_rows}
    kept = [r for r in rows if r.get(key) not in keys]
    write_rows(path, header, kept + new_rows)


def main() -> int:
    tar = os.path.join(ROOT, TARBALL)
    if os.path.exists(tar) and sha256_of(tar) != TARBALL_SHA:
        print(f"FAIL: {TARBALL} sha256 mismatch", file=sys.stderr)
        return 1

    mods = local_modules()
    index_rows, edge_rows, xindex_rows, xedge_rows = [], [], [], []
    ledger_rows, xledger_rows, delta_rows = [], [], []

    for rel, (donor_sha, prior_sha, disposition, note) in sorted(DELTA.items()):
        abs_path = os.path.join(AGDA_ROOT, rel)
        actual = sha256_of(abs_path)
        if actual != donor_sha:
            print(f"FAIL: {rel} overlay sha256 {actual} != donor {donor_sha}",
                  file=sys.stderr)
            return 1
        text = open(abs_path, encoding="utf-8").read()
        info = sii.analyse_agda(text)
        counts = info["counts"]
        lane = rel.split("/")[1] if rel.startswith("DASHI/") and "/" in rel[6:] else "<root>"
        internal = [i for i in info["imports"] if i.split(".")[0] == "DASHI"]
        row = {
            "lang": "agda",
            "path": rel,
            "lane": lane,
            "module": info["module"],
            "sha256_donor": donor_sha,
            "sha256_local": actual,
            "status": "adopted" if prior_sha else "new",
            "donor_preserves_local": "yes" if prior_sha else "",
            "bytes": str(os.path.getsize(abs_path)),
            "lines": str(len(text.splitlines())),
            "imports": str(len(info["imports"])),
            "internal_imports": str(len(internal)),
            "decls": str(len(info["decls"])),
            "data": str(counts.get("data", 0)),
            "record": str(counts.get("record", 0)),
            "postulate": str(counts.get("postulate", 0)),
            "terminating": str(counts.get("terminating", 0)),
            "trustme": str(counts.get("trustme", 0)),
            "holes": str(counts.get("holes", 0)),
            "bool_ledger": str(counts.get("bool_ledger", 0)),
            "absurd_boundary": str(counts.get("absurd_boundary", 0)),
            "theorem": "0", "definition": "0", "structure": "0", "instance": "0",
            "sorry": "0", "axiom_decl": "0", "native_decide": "0",
            "implemented_by": "0",
            "dependency_complete":
                "yes" if all(i in mods or not i.startswith("DASHI") for i in info["imports"]) else "no",
        }
        index_rows.append(row)
        xindex_rows.append({
            "path": rel, "lane": lane, "module": info["module"],
            "sha256_donor": donor_sha, "sha256_local": actual,
            "status": row["status"], "donor_preserves_local": row["donor_preserves_local"],
            "bytes": row["bytes"], "lines": row["lines"], "imports": row["imports"],
            "dashi_imports": row["internal_imports"], "decls": row["decls"],
            "data": row["data"], "record": row["record"], "postulate": row["postulate"],
            "terminating": row["terminating"], "trustme": row["trustme"],
            "holes": row["holes"], "bool_ledger": row["bool_ledger"],
            "absurd_boundary": row["absurd_boundary"],
            "dependency_complete": row["dependency_complete"],
        })
        for target in info["imports"]:
            resolution = "both" if target in mods else "external"
            edge_rows.append({"lang": "agda", "source": info["module"],
                              "target": target, "resolution": resolution})
            xedge_rows.append({"source": info["module"], "target": target,
                               "resolution": resolution})
        ledger_rows.append({
            "lang": "agda", "donor_path": rel, "disposition": disposition,
            "target_path": rel, "sha256_donor": donor_sha,
            "sha256_local_prior": prior_sha, "note": f"delta-20260911: {note}",
        })
        xledger_rows.append({
            "path": f"Agda/{rel}", "action": disposition, "donor_sha256": donor_sha,
            "prior_local_sha256": prior_sha, "donor_commit": DONOR_COMMIT,
            "reason": note,
        })
        delta_rows.append({
            "donor_path": f"dashi_agda/{rel}", "target_path": f"Agda/{rel}",
            "disposition": disposition, "sha256_donor": donor_sha,
            "sha256_local_prior": prior_sha, "sha256_local_now": actual,
            "base_commit": BASE_COMMIT, "donor_commit": DONOR_COMMIT,
            "module": info["module"], "decls": row["decls"],
            "records": row["record"], "data": row["data"],
            "postulates": row["postulate"], "holes": row["holes"],
            "bool_ledger": row["bool_ledger"],
            "absurd_boundary": row["absurd_boundary"],
            "dependency_complete": row["dependency_complete"], "note": note,
        })

    for fname, key, new in (
        ("SPINE_INDEX.csv", "path", index_rows),
        ("SPINE_INTAKE_LEDGER.csv", "donor_path", ledger_rows),
        ("XPOLL_INDEX.csv", "path", xindex_rows),
        ("XPOLL_LEDGER.csv", "path", xledger_rows),
    ):
        p = os.path.join(ROOT, fname)
        header, rows = read_rows(p)
        upsert(p, header, rows, key, new)

    for fname, new in (("SPINE_IMPORT_EDGES.csv", edge_rows),
                       ("XPOLL_IMPORT_EDGES.csv", xedge_rows)):
        p = os.path.join(ROOT, fname)
        header, rows = read_rows(p)
        sources = {r["source"] for r in new}
        kept = [r for r in rows if r.get("source") not in sources]
        write_rows(p, header, kept + new)

    delta_header = list(delta_rows[0].keys())
    write_rows(os.path.join(ROOT, "DELTA_20260911_LEDGER.csv"), delta_header, delta_rows)

    print(f"indexed {len(index_rows)} paths, {len(edge_rows)} import edges")
    for r in delta_rows:
        print(f"  {r['target_path']}: {r['disposition']}, decls={r['decls']}, "
              f"records={r['records']}, dependency_complete={r['dependency_complete']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
