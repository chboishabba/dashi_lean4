#!/usr/bin/env python3
"""Discover retained GWB native/legacy parser coordinates; never ingest.

Native SELECT joins are from SLR #77's slr_pg_leech_grammar_export.py.
Optional SCALE-1 receipt is a locator, not proof of current DB state.
Run against each configured database separately. No automatic selection.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path

PIN = "a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233"


def read(cur, sql, args=()):
    cur.execute(sql, args)
    names = [c[0] for c in cur.description]
    return [dict(zip(names, row)) for row in cur.fetchall()]


def inspect(cur, receipt=None):
    tables = read(cur, """
        SELECT to_regclass('ingest.parser_run')::text AS native_run,
               to_regclass('ingest.generic_source_revision')::text AS native_revision,
               to_regclass('corpus.document')::text AS native_document,
               to_regclass('corpus.canonical_content')::text AS native_content,
               to_regclass('ingest.parser_job')::text AS native_job,
               to_regclass('execution.semantic_parser_source')::text AS legacy_source
    """)[0]
    result = dict(schema="gwb-persistence-discovery-v1", pinned_sha256=PIN,
                  database=read(cur, "SELECT current_database() AS name")[0]["name"],
                  tables=tables, native=[], legacy=[], receipt_locators=[])
    known = set()
    if receipt is not None:
        if receipt.get("schema_version") != "sensiblaw.gwb-scale1-db-native.v0_1":
            raise ValueError("expected original GWB SCALE-1 multi-document receipt")
        for d in receipt["documents"]:
            loc = {k:d[k] for k in ("source_ref","source_revision_ref","canonical_ref",
                                   "document_ref","parser_run_ref","projected_sha256")}
            result["receipt_locators"].append(loc)
            known.add(loc["source_revision_ref"])
    if all(tables[k] for k in ("native_run","native_revision","native_document","native_content")):
        # Search exact digest AND original GWB raw-source namespace, and
        # receipt locators. Different bytes remain separate revisions.
        records = read(cur, """
            SELECT g.source_revision_ref,g.document_ref,g.content_digest_ref,
                   r.parser_run_ref,r.status,r.model_ref,r.config_digest_ref,
                   r.candidate_only,r.creates_semantic_authority,
                   r.claim_truth_promoted,d.canonical_ref,c.payload
            FROM ingest.generic_source_revision g
            JOIN corpus.document d ON d.document_ref=g.document_ref
            JOIN corpus.canonical_content c ON c.canonical_ref=d.canonical_ref
            LEFT JOIN ingest.parser_run r ON r.source_revision_ref=g.source_revision_ref
            WHERE g.content_digest_ref=%s OR g.source_revision_ref=ANY(%s::text[])
               OR g.source_revision_ref ILIKE '%%gwb%%'
               OR g.document_ref ILIKE '%%gwb%%'
               OR g.source_ref ILIKE 'source:gwb:%%'
            ORDER BY g.source_revision_ref,r.parser_run_ref
        """, ("sha256:"+PIN, sorted(known)))
        for row in records:
            raw = bytes(row.pop("payload"))
            sha = hashlib.sha256(raw).hexdigest()
            row.update(actual_sha256=sha, byte_count=len(raw),
                       digest_consistent=(row["content_digest_ref"]=="sha256:"+sha),
                       exact_pinned_bytes=(sha==PIN),
                       receipt_locator=(row["source_revision_ref"] in known))
            if tables["native_job"] and row["parser_run_ref"]:
                row["job_status_counts"] = read(cur, """
                    SELECT status,count(*) AS count FROM ingest.parser_job
                    WHERE parser_run_ref=%s GROUP BY status ORDER BY status
                """, (row["parser_run_ref"],))
            result["native"].append(row)
    if tables["legacy_source"]:
        result["legacy"] = read(cur, """
            SELECT source_ref,run_ref,document_ref,encode(content_sha256,'hex') AS sha256,
                   byte_count FROM execution.semantic_parser_source
            WHERE content_sha256=decode(%s,'hex')
               OR source_ref ILIKE '%%gwb%%' OR document_ref ILIKE '%%gwb%%'
               OR source_ref ILIKE '%%George%%Bush%%' OR document_ref ILIKE '%%George%%Bush%%'
            ORDER BY run_ref,document_ref,source_ref
        """, (PIN,))
    result["native_exact_count"] = sum(r["exact_pinned_bytes"] and r["digest_consistent"]
                                       for r in result["native"])
    result["legacy_exact_count"] = sum(r["sha256"]==PIN for r in result["legacy"])
    result["semantic_resolution_checked"] = False
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--receipt", type=Path)
    p.add_argument("--output", type=Path)
    a = p.parse_args()
    import psycopg2
    conn = psycopg2.connect(os.environ["DATABASE_URL"])
    try:
        conn.set_session(isolation_level="REPEATABLE READ", readonly=True, autocommit=False)
        with conn.cursor() as cur:
            cur.execute("SET LOCAL statement_timeout = '120s'")
            result = inspect(cur, json.loads(a.receipt.read_text()) if a.receipt else None)
    finally:
        conn.close()
    rendered = json.dumps(result, indent=2, default=str)+"\n"
    if a.output:
        a.output.parent.mkdir(parents=True, exist_ok=True)
        with a.output.open("x", encoding="utf-8") as f:
            f.write(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
