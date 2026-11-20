#!/usr/bin/env python3
"""Export existing native SLR GWB candidate rows; never parse or mutate DB."""
import argparse
import hashlib
import json
import os
from pathlib import Path

RUN_A = "parser-run:sha256:56ea4c0a05c3beb97f05dfe447570c7d753f15d8b8bf76cb86145ca41f8f2d63"
RUN_B = "parser-run:sha256:0071e359b56b3e31342f45a59752cbbeb35636e7d4180ad6ad892b9884723b7c"
REV_A = "source-revision:sha256:8dd2afe20c7cfb36bc1372f764b7683962e6acdfac6fe0bfa47554812d4eab00"
REV_B = "source-revision:sha256:bc5c811a8e10281f3d6ebd3a6284e84711b4bd350906097f95a44569784259a8"
DOC = "document:sha256:7ff2ec8ffe6243871ad682e7d7060fe3b84025fb15dbe229154d7aa7f6a72b30"
PINNED = "a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233"


def fetch(cur, sql, args=()):
    cur.execute(sql, args)
    cols = [d.name for d in cur.description]
    return [dict(zip(cols, row)) for row in cur.fetchall()]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    import psycopg2

    runs = [RUN_A, RUN_B]
    revisions = [REV_A, REV_B]
    conn = psycopg2.connect(os.environ["DATABASE_URL"])
    try:
        conn.set_session(isolation_level="REPEATABLE READ", readonly=True, autocommit=False)
        with conn.cursor() as cur:
            cur.execute("SET LOCAL statement_timeout = '120s'")
            source = fetch(cur, """
                SELECT g.source_revision_ref,g.source_ref,g.document_ref,
                       g.content_digest_ref,d.canonical_ref,c.encoding_ref,
                       c.normalization_ref,c.uncompressed_byte_length,
                       encode(c.content_sha256,'hex') AS actual_sha256
                FROM ingest.generic_source_revision g
                JOIN corpus.document d USING(document_ref)
                JOIN corpus.canonical_content c USING(canonical_ref)
                WHERE g.source_revision_ref = ANY(%s::text[])
                ORDER BY g.source_revision_ref
            """, (revisions,))
            canonical = fetch(cur, """
                SELECT canonical_ref,encode(content_sha256,'hex') AS sha256,
                       encoding_ref,normalization_ref,uncompressed_byte_length
                FROM corpus.canonical_content WHERE canonical_ref=%s
            """, ("canonical:sha256:7ff2ec8ffe6243871ad682e7d7060fe3b84025fb15dbe229154d7aa7f6a72b30",))
            jobs = fetch(cur, """
                SELECT parser_run_ref, status, count(*) AS count
                FROM ingest.parser_job WHERE parser_run_ref=ANY(%s::text[])
                GROUP BY parser_run_ref,status ORDER BY parser_run_ref,status
            """, (runs,))
            parser_runs = fetch(cur, """
                SELECT * FROM ingest.parser_run WHERE parser_run_ref=ANY(%s::text[])
                ORDER BY parser_run_ref
            """, (runs,))
            token_counts = fetch(cur, """
                SELECT j.parser_run_ref,count(t.*) AS token_count
                FROM ingest.parser_job j JOIN ingest.parser_token t USING(compilation_key)
                WHERE j.parser_run_ref=ANY(%s::text[]) AND j.status='succeeded'
                GROUP BY j.parser_run_ref ORDER BY j.parser_run_ref
            """, (runs,))
            pnf_receipts = fetch(cur, """
                SELECT * FROM pnf.candidate_persistence_stage_receipt
                WHERE parser_run_ref=ANY(%s::text[]) ORDER BY parser_run_ref
            """, (runs,))
            reconciliation = fetch(cur, """
                SELECT * FROM semantic.corpus_reconciliation_stage_receipt
                WHERE parser_run_ref=ANY(%s::text[]) ORDER BY parser_run_ref
            """, (runs,))
            auto_receipts = fetch(cur, """
                SELECT * FROM semantic.scale1_auto_event_stage_receipt
                WHERE parser_run_ref=ANY(%s::text[]) ORDER BY parser_run_ref
            """, (runs,))
            named = fetch(cur, """
                SELECT * FROM semantic.named_entity_candidate
                WHERE parser_run_ref=%s ORDER BY start_char,end_char,mention_ref
            """, (RUN_A,))
            temporal = fetch(cur, """
                SELECT * FROM semantic.temporal_mention_candidate
                WHERE parser_run_ref=%s ORDER BY start_char,end_char,temporal_mention_ref
            """, (RUN_A,))
            events = fetch(cur, """
                SELECT * FROM semantic.event_candidate_occurrence
                WHERE source_revision_ref=%s ORDER BY exact_span_ref,event_fingerprint_ref
            """, (REV_A,))
            propositions = fetch(cur, """
                SELECT * FROM semantic.proposition_candidate_occurrence
                WHERE source_revision_ref=%s ORDER BY exact_span_ref,proposition_fingerprint_ref
            """, (REV_A,))
            observations = fetch(cur, """
                SELECT * FROM semantic.scale1_auto_observation_candidate
                WHERE parser_run_ref=%s ORDER BY statement_ref,observation_ref
            """, (RUN_A,))
            mentions = fetch(cur, """
                SELECT m.*
                FROM semantic.entity_mention_candidate m
                JOIN corpus.source_statement s USING(statement_ref)
                WHERE s.source_revision_ref=%s
                  AND starts_with(m.candidate_ref, 'candidate-pnf-db:' || %s || ':')
                ORDER BY m.source_start_char,m.source_end_char,m.mention_ref
            """, (REV_A, RUN_A))
            bindings = fetch(cur, """
                SELECT b.batch_ref,b.statement_ref,b.candidate_product_ref,
                       s.exact_span_ref,j.region_start_char,j.compilation_key
                FROM pnf.statement_candidate_batch b
                JOIN corpus.source_statement s USING(statement_ref)
                JOIN ingest.parser_job j
                  ON j.source_revision_ref=s.source_revision_ref
                 AND j.region_ref=s.exact_span_ref
                 AND ('db-parser:' || j.parser_run_ref || ':' || j.region_ref)=b.parser_receipt_ref
                WHERE s.source_revision_ref=%s AND j.parser_run_ref=%s
                  AND j.status='succeeded'
                ORDER BY b.batch_ref
            """, (REV_A, RUN_A))
            products = sorted({b["candidate_product_ref"] for b in bindings
                               if b["candidate_product_ref"] is not None})
            factors = fetch(cur, """
                SELECT * FROM pnf.candidate_semantic_product_factor
                WHERE product_ref=ANY(%s::text[])
                ORDER BY product_ref,factor_ordinal
            """, (products,))
            entity_factors = fetch(cur, """
                SELECT * FROM semantic.l2_candidate_product_entity_factor
                WHERE product_ref=ANY(%s::text[])
                ORDER BY product_ref,detector_ref,factor_ordinal
            """, (products,))
            summaries = fetch(cur, """
                SELECT * FROM semantic.l2_candidate_product_summary
                WHERE product_ref=ANY(%s::text[])
                ORDER BY product_ref,detector_ref
            """, (products,))
            # This database revision does not have the proposed
            # corpus_reconciliation_review_delta_fibre relation.  The native
            # reconciliation review population is represented by review_item;
            # its reconciliation item reference carries the source revision
            # and its semantic_ref carries the fingerprint.
            review_fibres = fetch(cur, """
                SELECT * FROM semantic.review_item
                WHERE review_item_ref LIKE %s
                   OR review_item_ref LIKE %s
                ORDER BY review_item_ref
            """, (
                'review-item:reconciliation:' + REV_A + ':%',
                'review-item:reconciliation:' + REV_B + ':%',
            ))
            review_receipts = fetch(cur, """
                SELECT r.* FROM semantic.review_receipt r
                JOIN semantic.review_item i USING(review_item_ref)
                WHERE i.review_item_ref LIKE %s
                   OR i.review_item_ref LIKE %s
                ORDER BY r.review_item_ref,r.command_ref
            """, (
                'review-item:reconciliation:' + REV_A + ':%',
                'review-item:reconciliation:' + REV_B + ':%',
            ))
            pressure = fetch(cur, """
                SELECT p.* FROM semantic.reconciliation_pressure_candidate p
                WHERE EXISTS (
                    SELECT 1 FROM semantic.review_item i
                    WHERE i.semantic_ref=p.semantic_fingerprint_ref
                      AND (i.review_item_ref LIKE %s OR i.review_item_ref LIKE %s)
                )
                ORDER BY p.pressure_ref
            """, (
                'review-item:reconciliation:' + REV_A + ':%',
                'review-item:reconciliation:' + REV_B + ':%',
            ))
    finally:
        conn.close()

    result = {
        "schema": "gwb-native-semantic-observation-v2",
        "authority": "candidate-only-native-persistence",
        "source_sha256": "7ff2ec8ffe6243871ad682e7d7060fe3b84025fb15dbe229154d7aa7f6a72b30",
        "pinned_comparison_sha256": PINNED,
        "selected_run": RUN_A,
        "parity_control_run": RUN_B,
        "source": source,
        "canonical": canonical,
        "parser_runs": parser_runs,
        "parser_job_status": jobs,
        "parser_token_counts": token_counts,
        "pnf_candidate_persistence": pnf_receipts,
        "corpus_reconciliation": reconciliation,
        "scale1_auto_event_receipts": auto_receipts,
        "selected_run_candidates": {
            "named_entities": named,
            "temporal_mentions": temporal,
            "events": events,
            "propositions": propositions,
            "auto_observations": observations,
        },
        "native_entity_fibres": {
            "general_mentions": mentions,
            "mention_scope": "selected revision and native DB parser candidate prefix",
            "batch_bindings": bindings,
            "product_factors": factors,
            "entity_factors": entity_factors,
            "product_summaries": summaries,
            "review_delta_fibres": review_fibres,
                "review_receipts": review_receipts,
                "review_delta_storage": "semantic.review_item (the installed native schema has no corpus_reconciliation_review_delta_fibre table)",
            "matching_global_pressure_candidates": pressure,
        },
        "semantic_authority": {
            "candidate_only": True,
            "creates_identity": False,
            "creates_event_identity": False,
            "claim_truth_promoted": False,
            "lean_checked": False,
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, default=str) + "\n", encoding="utf-8")
    print("GWB_NATIVE_SEMANTIC_EXPORT", len(named), len(temporal), len(events), len(propositions), len(observations))


if __name__ == "__main__":
    main()
