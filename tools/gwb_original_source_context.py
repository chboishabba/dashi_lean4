#!/usr/bin/env python3
"""Reopen SAME-SOURCE native SLR discourse around a captured mention.

Read-only original SLR PostgreSQL state: generic source revision, exact
canonical content, original long-document regions and source statements.
Neither a parser nor a resolver is invoked, and no identity is admitted.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path

from tools.gwb_native_binding_adapter import require, sha, validate_region


def fetch_rows(cur, sql: str, args: tuple) -> list[tuple]:
    cur.execute(sql, args)
    return list(cur.fetchall())


def reopen(native: dict, conn, *, before: int = 4, after: int = 2) -> dict:
    require(0 <= before <= 20 and 0 <= after <= 20, "context bounds outside 0..20")
    source, focus = native["source"], native["focus_mention"]
    require(native.get("authority") == "candidate_only"
            and native.get("semantic_authority_promoted") is False,
            "native source is no longer candidate-only")
    require(sha(source["document_literal"]) == source["region_literal_sha256"],
            "archived region checksum mismatch")
    item = {**source, **focus, "exact_span_ref": source["region_ref"],
            "literal_text": source["document_literal"]}
    validate_region(item, native["parser_tokens"], native["parser_entities"],
                    native["pnf_product_factors"], native["l2_entity_factors"])
    with conn.cursor() as cur:
        source_rows = fetch_rows(cur, """
          SELECT g.source_ref,g.document_ref,g.content_digest_ref,
                 g.candidate_only,g.creates_semantic_authority,
                 g.applicability_promoted,g.claim_truth_promoted,c.payload
          FROM ingest.generic_source_revision g
          JOIN corpus.document d ON d.document_ref=g.document_ref
          JOIN corpus.canonical_content c ON c.canonical_ref=d.canonical_ref
          WHERE g.source_revision_ref=%s
        """, (source["source_revision_ref"],))
        require(len(source_rows) == 1, "missing/ambiguous canonical source revision")
        (source_ref, document_ref, digest_ref, candidate_only, semantic,
         applicability, truth, payload) = source_rows[0]
        require(document_ref == source["document_ref"], "foreign document")
        require(candidate_only is True and semantic is False
                and applicability is False and truth is False,
                "source revision promoted")
        raw = bytes(payload)
        digest = hashlib.sha256(raw).hexdigest()
        require(digest_ref == "sha256:" + digest, "stored canonical digest mismatch")
        require(document_ref == "document:sha256:" + digest,
                "canonical content/document identity mismatch")
        original = raw.decode("utf-8")
        start, end = source["region_start_char"], source["region_end_char"]
        require(0 <= start < end <= len(original), "region out of canonical source")
        require(original[start:end] == source["document_literal"],
                "native region differs from original full source")
        a, b = focus["source_start_char"], focus["source_end_char"]
        require(start <= a < b <= end and original[a:b] == focus["surface"],
                "focus offset/surface mismatch in original source")

        # These are the ORIGINAL persisted sentence statements. They do not
        # imply antecedent resolution, quotation scope or world truth.
        rows = fetch_rows(cur, """
          SELECT r.region_ref,r.start_char,r.end_char,r.region_kind,
                 s.statement_ref,s.literal_text,
                 s.candidate_only,s.creates_semantic_authority,
                 s.applicability_promoted,s.claim_truth_promoted,
                 r.candidate_only,r.creates_semantic_authority,
                 r.claim_truth_promoted
          FROM ingest.long_document_region r
          JOIN corpus.source_statement s
            ON s.source_revision_ref=r.source_revision_ref
           AND s.exact_span_ref=r.region_ref
           AND s.document_ref=%s
          WHERE r.source_revision_ref=%s AND r.region_kind='sentence'
          ORDER BY r.start_char,r.end_char,r.region_ref,s.statement_ref
        """, (document_ref, source["source_revision_ref"]))
    require(bool(rows), "no original persisted sentence statements")
    seen = set()
    entries = []
    for (region_ref, x, y, kind, stmt, literal, sc, sa, sap, st,
         rc, ra, rt) in rows:
        require(region_ref not in seen, "ambiguous same-revision region/statement")
        seen.add(region_ref)
        require(0 <= x < y <= len(original)
                and original[x:y] == literal, "neighbor original-source mismatch")
        require((sc,sa,sap,st,rc,ra,rt) ==
                (True,False,False,False,True,False,False),
                "neighbor source/region promoted")
        entries.append({"region_ref": region_ref, "start_char": x,
                        "end_char": y, "statement_ref": stmt,
                        "literal": literal, "candidate_only": True})
    exact = [i for i, row in enumerate(entries)
             if row["region_ref"] == source["region_ref"]
             and row["start_char"] == start and row["end_char"] == end
             and row["statement_ref"] == source["statement_ref"]]
    require(len(exact) == 1, "focus not one persisted original statement")
    index = exact[0]
    result = {
        "schema": "slr-native-original-discourse-context-v1",
        "original_source_ref": source_ref,
        "source_revision_ref": source["source_revision_ref"],
        "document_ref": document_ref,
        "canonical_content_sha256": digest,
        "focus": {"mention_ref": focus["mention_ref"],
                  "candidate_ref": focus["candidate_ref"],
                  "statement_ref": source["statement_ref"],
                  "region_ref": source["region_ref"],
                  "start_char": a, "end_char": b, "surface": original[a:b]},
        "before": entries[max(0,index-before):index],
        "at": entries[index],
        "after": entries[index+1:index+1+after],
        "antecedent_resolution": "UNRESOLVED_REVIEW_REQUIRED",
        "resolved_referent": None,
        "external_qid": "NOT_TESTED",
        "semantic_authority_promoted": False,
    }
    return result


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--native", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--before", type=int, default=4)
    ap.add_argument("--after", type=int, default=2)
    args = ap.parse_args()
    native = json.loads(args.native.read_text(encoding="utf-8"))
    import psycopg2
    conn = psycopg2.connect(os.environ["DATABASE_URL"])
    try:
        conn.set_session(isolation_level="REPEATABLE READ", readonly=True)
        result = reopen(native, conn, before=args.before, after=args.after)
    finally:
        conn.close()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n",
                           encoding="utf-8")
    print("GWB_NATIVE_ORIGINAL_CONTEXT_REOPEN_OK",
          len(result["before"]), len(result["after"]),
          "identity=UNRESOLVED_REVIEW_REQUIRED")


if __name__ == "__main__":
    main()
