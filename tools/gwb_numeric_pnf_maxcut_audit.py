#!/usr/bin/env python3
"""P0-C/D original numeric-PNF maximum cut: one READ-ONLY audit.

The existing SLR source-relative Bush answer is an upstream premise, not
a numeric identity witness. Query original SensibLaw owner tables only.
Never guess a numeric run, rewrite a source, refresh admissions or insert
a synthetic demand. Original migrations: 051,069,070,074,077,083,086,089,
123,124. Missing data remains an explicit residual.
"""
import argparse
import json
import os
from pathlib import Path

BOOK_SHA="7ff2ec8ffe6243871ad682e7d7060fe3b84025fb15dbe229154d7aa7f6a72b30"

def query(cur, sql, *params):
    cur.execute(sql, params)
    names=[col.name for col in cur.description]
    return [dict(zip(names,row)) for row in cur.fetchall()]

def available(cur, name):
    return query(cur, "SELECT to_regclass(%s) AS relation", name)[0]["relation"] is not None

def source_gate(consumer):
    checks={
      "schema": "slr-native-source-local-consumer-v1",
      "source_content_sha256":BOOK_SHA,
      "original_focus_span":[4534,4536],
      "original_selected_antecedent_span":[4310,4314],
      "original_focus_surface":"he",
      "original_selected_antecedent_surface":"Bush",
      "answer_kind":"DERIVED_UNDER_NAMED_TOPIC_POLICY",
      "answer_value":"Bush",
      "source_local_policy_inference_paid":True,
      "typed_unique_identity_witness_paid":False,
      "governed_semantic_identity_paid":False,
      "level_three_substitution_paid":False,
      "external_qid_paid":False,
      "historical_truth_paid":False,
    }
    for key,expected in checks.items():
        if consumer.get(key)!=expected:
            raise ValueError(f"original SLR consumer mismatch: {key}")
    for key in ("source_document_ref","source_revision_ref",
                "original_parser_run_ref","original_candidate_set_ref",
                "answer_receipt_ref","original_policy_ref"):
        if not consumer.get(key):
            raise ValueError(f"missing original SLR dependency: {key}")

def inspect(cur,consumer,run_ref,doc_ref):
    output={"run_ref":run_ref,"document_ref":doc_ref,
            "numeric_document_exact_ref_match":
                doc_ref==consumer["source_document_ref"],
            "numeric_original_source_digest_witness":False}
    match=query(cur,"""
        SELECT r.run_id,d.document_id
        FROM execution.semantic_pnf_run_identity AS r
        CROSS JOIN execution.semantic_pnf_document_identity AS d
        WHERE r.run_ref=%s AND d.document_ref=%s
    """,run_ref,doc_ref)
    output["registered_numeric_scope"]=match
    if not match:
        output["first_blocker"]="ORIGINAL_NUMERIC_RUN_OR_DOCUMENT_UNAVAILABLE"
        return output
    run_id=match[0]["run_id"]
    document_id=match[0]["document_id"]
    coverage=query(cur,"""
        SELECT state,completed_partitions,total_partitions,
               open_boundary_obligations
        FROM execution.semantic_parser_document_coverage
        WHERE run_ref=%s AND document_ref=%s
    """,run_ref,doc_ref)
    output["parser_coverage"]=coverage
    supports={}
    for label,start,end,surface in (
       ("focus_he",4534,4536,"he"),
       ("Bush_22",4310,4314,"Bush"),
       ("Bush_19",4061,4065,"Bush"),
    ):
        tokens=query(cur,"""
            SELECT t.token_id,t.sentence_id,t.sentence_ref,
                   orth.symbol_text AS surface, t.start_char,t.end_char
            FROM execution.semantic_parser_token AS t
            JOIN execution.semantic_symbol AS orth
              ON orth.symbol_id=t.orth_symbol_id
            WHERE t.run_ref=%s AND t.document_ref=%s
              AND t.start_char=%s AND t.end_char=%s
              AND t.representation_version=2
        """,run_ref,doc_ref,start,end)
        tokens=[x for x in tokens if x["surface"]==surface]
        supports[label]=tokens
    output["exact_original_parser_tokens"]=supports
    focus_ids=[x["token_id"] for x in supports["focus_he"]]
    bush_ids=[x["token_id"] for label in ("Bush_19","Bush_22")
              for x in supports[label]]
    if not available(cur,"execution.semantic_pnf_object_token_support"):
        output["first_blocker"]="ORIGINAL_NUMERIC_TOKEN_OBJECT_SUPPORT_MISSING"
        return output
    objects=query(cur,"""
        SELECT s.token_id,s.object_id,r.region_id,
               r.start_char AS region_start,r.end_char AS region_end
        FROM execution.semantic_pnf_object_token_support AS s
        JOIN execution.semantic_pnf_object AS o ON o.object_id=s.object_id
        JOIN execution.semantic_pnf_region AS r ON r.region_id=o.region_id
        WHERE s.token_id=ANY(%s::bigint[])
          AND r.run_id=%s AND r.document_id=%s
        ORDER BY s.token_id,s.object_id LIMIT 200
    """,focus_ids+bush_ids,run_id,document_id)
    output["exact_token_object_support"]=objects
    focus_objects=sorted({x["object_id"] for x in objects
                          if x["token_id"] in focus_ids})
    bush_objects=sorted({x["object_id"] for x in objects
                         if x["token_id"] in bush_ids})
    output["focus_object_ids"]=focus_objects
    output["Bush_object_ids"]=bush_objects
    if not focus_objects:
        output["first_blocker"]="EXACT_HE_NUMERIC_PNF_OBJECT_MISSING"
        return output
    # Legacy demand source_object_id is a diagnostic; the original H9
    # occurrence bearer is a separate required producer witness.
    demands=query(cur,"""
        SELECT d.demand_id,d.state,d.source_object_id
        FROM execution.semantic_pnf_demand AS d
        JOIN execution.semantic_pnf_region AS r
          ON r.region_id=d.source_region_id
        WHERE r.run_id=%s AND r.document_id=%s
          AND d.source_object_id=ANY(%s::bigint[])
        ORDER BY d.demand_id LIMIT 100
    """,run_id,document_id,focus_objects)
    output["legacy_source_object_demands"]=demands
    if available(cur,"execution.semantic_pnf_h9_entity_bearing_v1"):
        h9=query(cur,"""
            SELECT b.demand_id,b.source_object_id,b.anchor_kind
            FROM execution.semantic_pnf_h9_entity_bearing_v1 AS b
            JOIN execution.semantic_pnf_demand AS d
              ON d.demand_id=b.demand_id
            JOIN execution.semantic_pnf_region AS r
              ON r.region_id=d.source_region_id
            WHERE r.run_id=%s AND r.document_id=%s
              AND b.source_object_id=ANY(%s::bigint[])
            ORDER BY b.demand_id LIMIT 100
        """,run_id,document_id,focus_objects)
    else:
        h9=[]
    output["h9_supported_occurrence_demands"]=h9
    ids=sorted({x["demand_id"] for x in h9})
    if not ids:
        output["first_blocker"]="NO_ORIGINAL_H9_SUPPORTED_TYPED_DEMAND"
        return output
    output["typed_frontier_resolutions"]=query(cur,"""
        SELECT demand_id,outcome_state,selected_target_kind,
               selected_target_id,candidate_count,interface_id
        FROM execution.semantic_pnf_frontier_resolution
        WHERE demand_id=ANY(%s::bigint[]) LIMIT 100
    """,ids)
    if available(cur,"execution.semantic_pnf_demand_funnel_v1"):
        output["demand_funnel"]=query(cur,"""
            SELECT demand_id,represented_candidate_count,
              active_candidate_count,residual_candidate_count,
              refuted_candidate_count,outside_model_possible,
              resource_limited,admitted_identity_witness_count
            FROM execution.semantic_pnf_demand_funnel_v1
            WHERE demand_id=ANY(%s::bigint[])
        """,ids)
    if available(cur,"execution.semantic_pnf_demand_open_world_state"):
        output["open_world"]=query(cur,"""
            SELECT demand_id,outside_model_possible,
              coverage_witness_ref,represented_residual_count,
              resource_limited
            FROM execution.semantic_pnf_demand_open_world_state
            WHERE demand_id=ANY(%s::bigint[])
        """,ids)
    if available(cur,"execution.semantic_pnf_candidate_state_v1"):
        output["represented_candidate_state"]=query(cur,"""
            SELECT demand_id,target_kind,target_id,active,
              execution_residual,refuted,admissible,
              admissibility_evidence_id
            FROM execution.semantic_pnf_candidate_state_v1
            WHERE demand_id=ANY(%s::bigint[]) LIMIT 256
        """,ids)
    output["original_identity_witnesses"]=query(cur,"""
        SELECT w.witness_id,w.source_object_id,w.target_entity_id,
          w.authority_class,w.witness_kind,w.candidate_count,
          w.demand_id,a.admission_state
        FROM execution.semantic_pnf_identity_witness AS w
        LEFT JOIN execution.semantic_pnf_identity_witness_admission AS a
          ON a.witness_id=w.witness_id
        WHERE w.source_object_id=ANY(%s::bigint[])
        LIMIT 100
    """,focus_objects)
    output["original_current_projection"]=query(cur,"""
        SELECT source_object_id,target_entity_id,authority_class,
          witness_ids,witness_count
        FROM execution.semantic_pnf_identity_projection
        WHERE source_object_id=ANY(%s::bigint[])
    """,focus_objects)
    if available(cur,"execution.semantic_pnf_identity_factor_alignment_audit_v1"):
        output["factor_alignment"]=query(cur,"""
            SELECT source_object_id,authority_class,
              target_entity_id,alignment_class
            FROM execution.semantic_pnf_identity_factor_alignment_audit_v1
            WHERE source_object_id=ANY(%s::bigint[])
              AND run_id=%s AND document_id=%s
        """,focus_objects,run_id,document_id)
    if available(cur,"execution.semantic_pnf_factor_derivation_argument"):
        output["level_three_argument_witnesses"]=query(cur,"""
            SELECT a.derivation_id,a.source_object_id,
              a.identity_entity_id,a.identity_witness_ids
            FROM execution.semantic_pnf_factor_derivation_argument AS a
            JOIN execution.semantic_pnf_factor_derivation AS d
              ON d.derivation_id=a.derivation_id
            WHERE a.source_object_id=ANY(%s::bigint[])
              AND d.rule_ref='identity-substitution:v1'
            LIMIT 100
        """,focus_objects)
    output["first_blocker"]="NUMERIC_SOURCE_MANIFEST_AND_RETRACTION_UNPAID"
    return output


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--consumer",type=Path,required=True)
    parser.add_argument("--numeric-run-ref",required=True)
    parser.add_argument("--numeric-document-ref")
    parser.add_argument("--database-url",default=os.getenv("SENSIBLAW_DATABASE_URL"))
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    if not args.database_url:
        parser.error("--database-url or SENSIBLAW_DATABASE_URL required")
    consumer=json.loads(args.consumer.read_text(encoding="utf-8"))
    source_gate(consumer)
    document=args.numeric_document_ref or consumer["source_document_ref"]
    import psycopg
    with psycopg.connect(args.database_url) as connection:
        with connection.cursor() as cur:
            cur.execute("SET TRANSACTION READ ONLY")
            cur.execute("SET LOCAL statement_timeout='90000ms'")
            result=inspect(cur,consumer,args.numeric_run_ref,document)
            connection.rollback()
    result.update(schema="gwb-original-numeric-pnf-maxcut-read-only-v1",
        original_slr_consumer_ref=consumer["answer_receipt_ref"],
        original_slr_revision=consumer["source_revision_ref"],
        original_book_sha256=BOOK_SHA,
        source_local_answer="Bush",
        real_numeric_document_identity_admitted=False,
        full_typed_open_world_coverage_paid=False,
        real_level_three_retraction_paid=False,
        external_world_qid_paid=False,
        historical_truth_paid=False)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2,default=str)+"\n",
                          encoding="utf-8")
    print("GWB_NUMERIC_PNF_MAXCUT_READ_ONLY_AUDIT_OK")
    print("first_blocker="+result["first_blocker"])
    print("output="+str(args.output))


if __name__=="__main__":
    main()
