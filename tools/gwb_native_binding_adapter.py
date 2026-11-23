#!/usr/bin/env python3
"""C4.09a: reopen one native SLR region and weld to an *existing* owner graph.

Read-only DB source; no parser, semantic factor synthesis, identity decision,
QID lookup, schema migration, or semantic authority mutation.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path


def require(condition: bool, reason: str) -> None:
    if not condition:
        raise ValueError(reason)


def sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def rows(cur, sql, parameters):
    cur.execute(sql, parameters)
    columns = [column.name for column in cur.description]
    return [dict(zip(columns, row)) for row in cur.fetchall()]


def capture(conn, *, run: str, revision: str, mention: str) -> dict:
    """Reopen a native mention's exact owning statement, parser job and factors."""
    require(bool(run and revision and mention), "exact run/revision/mention required")
    with conn.cursor() as cur:
        cur.execute("SET TRANSACTION ISOLATION LEVEL REPEATABLE READ, READ ONLY")
        cur.execute("SET LOCAL statement_timeout = '120s'")
        scope = rows(cur, """
          SELECT m.*, s.exact_span_ref,s.literal_text,s.source_revision_ref,
                 j.compilation_key,j.parser_run_ref,j.region_start_char,j.region_end_char,
                 j.parser_product_key,j.status AS job_status,
                 b.batch_ref,b.candidate_product_ref
          FROM semantic.entity_mention_candidate m
          JOIN corpus.source_statement s ON s.statement_ref=m.statement_ref
          JOIN ingest.parser_job j
            ON j.source_revision_ref=s.source_revision_ref
           AND j.region_ref=s.exact_span_ref
           AND j.parser_run_ref=%s
          JOIN pnf.statement_candidate_batch b ON b.statement_ref=s.statement_ref
           AND b.parser_receipt_ref=('db-parser:' || j.parser_run_ref || ':' || j.region_ref)
          WHERE m.mention_ref=%s AND s.source_revision_ref=%s
            AND starts_with(m.candidate_ref,'candidate-pnf-db:' || %s || ':')
        """, (run, mention, revision, run))
        require(len(scope) == 1, "missing or ambiguous same-source mention/batch")
        item = scope[0]
        require(item["job_status"] == "succeeded", "parser job not succeeded")
        require(item["candidate_only"] is True and
                item["creates_entity_identity"] is False and
                item["creates_semantic_authority"] is False and
                item["claim_truth_promoted"] is False, "native mention promoted")
        start, end = item["region_start_char"], item["region_end_char"]
        literal = item["literal_text"]
        require(end - start == len(literal), "region literal/character coordinates disagree")
        require(start <= item["source_start_char"] < item["source_end_char"] <= end,
                "mention out of region")
        require(literal[item["source_start_char"]-start:item["source_end_char"]-start]
                == item["surface"], "mention literal mismatch")
        tokens = rows(cur, """
          SELECT * FROM ingest.parser_token
          WHERE compilation_key=%s ORDER BY token_ordinal
        """, (item["compilation_key"],))
        entities = rows(cur, """
          SELECT * FROM ingest.parser_entity
          WHERE compilation_key=%s ORDER BY entity_ordinal
        """, (item["compilation_key"],))
        factors = rows(cur, """
          SELECT * FROM pnf.candidate_semantic_product_factor
          WHERE product_ref=%s ORDER BY factor_ordinal
        """, (item["candidate_product_ref"],))
        l2 = rows(cur, """
          SELECT * FROM semantic.l2_candidate_product_entity_factor
          WHERE product_ref=%s ORDER BY detector_ref,factor_ordinal
        """, (item["candidate_product_ref"],))
    validate_region(item, tokens, entities, factors, l2)
    return {
        "schema":"gwb-native-parser-binding-carrier-v1",
        "authority":"candidate_only",
        "source":{
            "source_revision_ref":revision,"parser_run_ref":run,
            "statement_ref":item["statement_ref"],
            "region_ref":item["exact_span_ref"],
            "region_start_char":start,"region_end_char":end,
            "document_literal":literal,"region_literal_sha256":sha(literal),
            "compilation_key":item["compilation_key"],
            "parser_product_key":item["parser_product_key"],
            "batch_ref":item["batch_ref"],
            "candidate_product_ref":item["candidate_product_ref"],
        },
        "focus_mention":{k:item[k] for k in ("mention_ref","candidate_ref",
            "source_start_char","source_end_char","surface","lemma",
            "role_ref","entity_fingerprint_ref")},
        "parser_tokens":tokens,"parser_entities":entities,
        "pnf_product_factors":factors,"l2_entity_factors":l2,
        "binding_admission":"NOT_TESTED",
        "external_qid":"NOT_TESTED",
        "semantic_authority_promoted":False,
    }


def validate_region(item, tokens, entities, factors, l2) -> None:
    start, end = item["region_start_char"], item["region_end_char"]
    literal = item["literal_text"]
    require(bool(tokens), "missing original parser tokens")
    seen = set()
    previous = start
    for token in tokens:
        ordinal = token["token_ordinal"]
        require(ordinal not in seen, "duplicate token ordinal")
        seen.add(ordinal)
        a, b = token["start_char"], token["end_char"]
        require(start <= a < b <= end and a >= previous, "token out of order/scope")
        require(literal[a-start:b-start] == token["surface"], "parser token literal mismatch")
        previous = b
        if token["morph_json"] is not None:
            require(isinstance(json.loads(token["morph_json"]), (dict, list)),
                    "unexpected morphology JSON")
    require(all(t["head_ordinal"] is None or t["head_ordinal"] in seen for t in tokens),
            "foreign dependency head")
    for entity in entities:
        a, b = entity["start_char"], entity["end_char"]
        require(start <= a < b <= end, "entity out of scope")
        require(literal[a-start:b-start] == entity["surface"],
                "entity surface mismatch")
    for factor in factors:
        a, b = factor["start_offset"],factor["end_offset"]
        require(0 <= a < b <= len(literal), "PNF factor local span invalid")
        require(literal[a:b] == factor["surface"], "PNF factor surface mismatch")
    for factor in l2:
        require(factor["product_ref"] == item["candidate_product_ref"],
                "L2 foreign product")
    matching = [t for t in tokens if t["start_char"] == item["source_start_char"]
                and t["end_char"] == item["source_end_char"]]
    require(len(matching) == 1, "mention does not align to a unique native token")
    token = matching[0]
    expected = (f'candidate-pnf-db:{item["parser_run_ref"]}:'
                f'{item["exact_span_ref"]}:{token["token_ordinal"]}:'
                f'{token["start_char"]}:{token["end_char"]}')
    require(item["candidate_ref"] == expected,
            "mention candidate reference does not match native token")


def verify_owner_carrier(native: dict, owner: dict) -> dict:
    """Prove exact same-region observation alignment; no semantic relabeling."""
    source = native["source"]
    require(source["parser_product_key"] not in (None, ""),
            "strict SLR #78 requires parser_product_key; legacy NULL is unresolved")
    require(owner.get("canonical_text") == source["document_literal"],
            "owner canonical region text mismatch")
    graph = owner.get("pnf_graph") or {}
    require(graph.get("document_ref") == source["source_revision_ref"],
            "owner graph revision mismatch")
    layer = owner.get("semantic_annotation_layer") or {}
    spans = [s for s in layer.get("span_annotations", [])
             if s.get("annotation_type") == "parser_token"]
    require(len(spans) == len(native["parser_tokens"]),
            "owner does not cover every native parser token")
    native_tokens = native["parser_tokens"]
    # Original owner token index is region-local. Never reassign native
    # absolute source offsets without proving alignment first.
    for index, (s, t) in enumerate(zip(sorted(spans,key=lambda x:x["start_token"]),
                                      native_tokens)):
        val = s.get("value") or {}
        a, b = t["start_char"], t["end_char"]
        require(s["start_token"] == index and s["end_token"] == index + 1,
                "nonbijective parser token ordinal")
        require(val.get("start_char") == a - source["region_start_char"] and
                val.get("end_char") == b - source["region_start_char"],
                "owner token coordinate mismatch")
        require(val.get("surface") == t["surface"],
                "owner parser token surface mismatch")
    for f in graph.get("factors") or ():
        require(f.get("factor_type") and f.get("factor_ref"),
                "untyped owner factor")
        # Do not accept SLR's actor/patient vocabulary as an established
        # SensibLaw semantic kind. Those must come from original owner.
        require(str(f["factor_type"]).startswith("semantic."),
                "missing original semantic reduction")
    return {"schema":"gwb-native-owner-binding-check-v1",
            "source_revision_ref":source["source_revision_ref"],
            "parser_run_ref":source["parser_run_ref"],
            "region_ref":source["region_ref"],
            "matched_parser_tokens":len(native_tokens),
            "owner_factor_count":len(graph.get("factors") or ()),
            "source_alignment":"EXACT",
            "semantic_authority_promoted":False}


def invoke_existing_binder(native: dict, owner: dict, sensiblaw_root: Path) -> dict:
    import sys
    sys.path.insert(0, str(sensiblaw_root.resolve()))
    try:
        from src.pnf.reference_binding import build_set_valued_binding_artifacts
    finally:
        sys.path.pop(0)
    check = verify_owner_carrier(native, owner)
    bound = build_set_valued_binding_artifacts(owner)
    return {"check":check,
            "binding_candidate_sets":bound["binding_candidate_sets"],
            "resolution_demands":bound["resolution_demands"],
            "binding_compaction_summary":bound["binding_compaction_summary"],
            "identity_admission":"NOT_TESTED",
            "external_qid":"NOT_TESTED",
            "semantic_authority_promoted":False}


def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--run-ref",required=True)
    ap.add_argument("--revision-ref",required=True)
    ap.add_argument("--mention-ref",required=True)
    ap.add_argument("--output",type=Path,required=True)
    ap.add_argument("--owner-artifacts",type=Path)
    ap.add_argument("--sensiblaw-root",type=Path)
    args=ap.parse_args()
    require(args.owner_artifacts is None or args.sensiblaw_root is not None,
            "owner artifacts require SensibLaw root")
    import psycopg2
    conn=psycopg2.connect(os.environ["DATABASE_URL"])
    try:
        result=capture(conn,run=args.run_ref,revision=args.revision_ref,
                       mention=args.mention_ref)
    finally:
        conn.close()
    if args.owner_artifacts:
        owner=json.loads(args.owner_artifacts.read_text(encoding="utf-8"))
        result["owner_binding"]=invoke_existing_binder(result,owner,args.sensiblaw_root)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2,default=str)+"\n",encoding="utf-8")
    print("GWB_NATIVE_BINDING_CARRIER",len(result["parser_tokens"]),
          len(result["parser_entities"]),bool(result.get("owner_binding")))


if __name__=="__main__":
    main()
