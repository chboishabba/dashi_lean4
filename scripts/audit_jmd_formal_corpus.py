#!/usr/bin/env python3
"""Read-only admission audit for independent JMD stars and GitHub-wide Lean corpora.

This verifies repository identities and ingestion snapshots only. Neither a
GitHub language tag nor a repository overlap establishes a theorem, proof
equivalence, or an Agda source owner.
"""
import argparse
import csv
import datetime as dt
import json
from pathlib import Path

class AuditError(ValueError):
    pass

def load_rows(path, required):
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        if not reader.fieldnames or not required.issubset(reader.fieldnames):
            raise AuditError(f"{path}: missing columns {sorted(required-set(reader.fieldnames or []))}")
        result = {}
        for line, row in enumerate(reader, 2):
            raw = (row.get("github_id") or "").strip()
            if not raw.isdecimal() or int(raw) == 0:
                raise AuditError(f"{path}:{line}: invalid GitHub ID")
            ident = int(raw)
            name = (row.get("full_name") or "").strip()
            url = (row.get("html_url") or "").strip()
            if len(name.split("/")) != 2 or url != f"https://github.com/{name}":
                raise AuditError(f"{path}:{line}: invalid full name or URL")
            if ident in result:
                raise AuditError(f"{path}:{line}: repeated GitHub ID {ident}")
            result[ident] = row
        return result

def expected(summary, key):
    n = summary.get(key)
    if type(n) is not int or n < 0:
        raise AuditError(f"summary missing valid {key}")
    return n

def audit_partitions(checkpoint, global_summary):
    parts = checkpoint.get("partitions")
    if not isinstance(parts, dict):
        raise AuditError("checkpoint missing partitions")
    windows, pages = [], 0
    for key, row in parts.items():
        try:
            start, end = dt.date.fromisoformat(row["start"]), dt.date.fromisoformat(row["end"])
            n, p = row["count"], row["pages"]
        except (KeyError, ValueError, TypeError) as exc:
            raise AuditError(f"bad partition {key}") from exc
        if type(n) is not int or type(p) is not int or n < 0 or p < 0 or start > end:
            raise AuditError(f"bad partition count/pages {key}")
        if key != f"{start}_{end}" or p != (n+99)//100:
            raise AuditError(f"partition incomplete or miskeyed: {key}")
        windows.append((start, end, key))
        pages += p
    windows.sort()
    for (_, end, _), (start, _, key) in zip(windows, windows[1:]):
        if start != end + dt.timedelta(days=1):
            raise AuditError(f"partition gap/overlap before {key}")
    if len(windows) != expected(global_summary, "partitions"):
        raise AuditError("partition count differs from summary")
    return {"partitions": len(windows), "completed_pages": pages,
            "first_created_date": windows[0][0].isoformat() if windows else None,
            "last_created_date": windows[-1][1].isoformat() if windows else None,
            "all_partition_pages_accounted": True}

def verify(global_rows, star_rows, lean_rows, global_summary, star_summary, checkpoint):
    if len(global_rows) != expected(global_summary, "repository_count"):
        raise AuditError("global CSV differs from summary")
    if len(star_rows) != expected(star_summary, "total_public_starred"):
        raise AuditError("stars CSV differs from summary")
    if len(lean_rows) != expected(star_summary, "primary_language_lean"):
        raise AuditError("Lean stars CSV differs from summary")
    for ident, row in lean_rows.items():
        if ident not in star_rows or row["language"] != "Lean":
            raise AuditError(f"Lean starred repository not in stars / wrong language: {ident}")
        if row["full_name"] != star_rows[ident]["full_name"]:
            raise AuditError(f"Lean starred name disagreement: {ident}")
    if {i for i, row in star_rows.items() if row["language"] == "Lean"} != set(lean_rows):
        raise AuditError("Lean stars are not the exact primary-language subset")
    if global_summary.get("query") != "language:Lean":
        raise AuditError("wrong global query")
    if star_summary.get("github_user") != "jmikedupont2":
        raise AuditError("wrong stars user")
    repos = checkpoint.get("repos")
    if not isinstance(repos, dict):
        raise AuditError("checkpoint missing repos")
    if {int(i) for i in repos} != set(global_rows):
        raise AuditError("checkpoint and global CSV IDs disagree")
    for i, row in global_rows.items():
        if repos[str(i)].get("full_name") != row["full_name"]:
            raise AuditError(f"checkpoint/CSV name mismatch for {i}")
    partition = audit_partitions(checkpoint, global_summary)
    both = set(global_rows) & set(star_rows)
    both_lean = both & set(lean_rows)
    return ({
        "schema": "dashi-jmd-formal-corpus-ingress-v1",
        "authority": "repository-discovery-only",
        "establishes_theorem": False,
        "establishes_same_object": False,
        "global_retrieval_utc": global_summary.get("retrieval_date_utc"),
        "stars_retrieval_utc": star_summary.get("retrieval_date_utc"),
        "global_lean_repositories": len(global_rows),
        "jmd_public_stars": len(star_rows),
        "jmd_primary_lean_stars": len(lean_rows),
        "jmd_stars_in_global_lean_snapshot": len(both),
        "jmd_primary_lean_stars_in_global_lean_snapshot": len(both_lean),
        "identity_key": "numeric_github_repository_id",
        "snapshot_caveat": "Mutable searches at different retrieval times; overlap is not a complete language intersection.",
        "partition_integrity": partition,
    }, both)

def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--global-dir", type=Path, default=Path("docs/roadmap/jmd_lean_corpus"))
    p.add_argument("--stars-dir", type=Path, default=Path("docs/roadmap/jmd_stars"))
    p.add_argument("--out-dir", type=Path, default=Path("docs/roadmap/jmd_formal_ingress"))
    args = p.parse_args(argv)
    global_rows = load_rows(args.global_dir/"github_lean_repositories.csv",
                            {"github_id", "full_name", "html_url"})
    stars = load_rows(args.stars_dir/"jmd_starred_all.csv",
                      {"github_id", "full_name", "html_url", "language"})
    lean = load_rows(args.stars_dir/"jmd_starred_primary_lean.csv",
                     {"github_id", "full_name", "html_url", "language"})
    gs = json.loads((args.global_dir/"summary.json").read_text(encoding="utf-8"))
    ss = json.loads((args.stars_dir/"jmd_starred_summary.json").read_text(encoding="utf-8"))
    cp = json.loads((args.global_dir/"checkpoint.json").read_text(encoding="utf-8"))
    audit, both = verify(global_rows, stars, lean, gs, ss, cp)
    args.out_dir.mkdir(parents=True, exist_ok=True)
    (args.out_dir/"audit.json").write_text(
        json.dumps(audit, indent=2, sort_keys=True)+"\n", encoding="utf-8")
    with (args.out_dir/"starred_global_overlap.tsv").open(
            "w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle, delimiter="\t")
        writer.writerow(["github_id", "repository", "global_primary_language",
                         "starred_primary_language", "claim_status"])
        for ident in sorted(both):
            writer.writerow([ident, global_rows[ident]["full_name"],
                             global_rows[ident]["language"],
                             stars[ident]["language"],
                             "REPOSITORY_ID_ONLY_NOT_THEOREM"])
    print(json.dumps(audit, indent=2, sort_keys=True))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
