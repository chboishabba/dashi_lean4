#!/usr/bin/env python3
"""C4.09b: read-only proof-relevant native↔SensibLaw identity inspection.

Requires *original* owner semantic factors and an explicit owner-produced
source-object crosswalk. Reads the original SensibLaw numeric proof tables;
never creates a factor, resolver decision, witness, QID or database mutation.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
from tools.gwb_native_binding_adapter import require, verify_owner_carrier


def one(cur, sql, args, label):
    cur.execute(sql, args)
    found = cur.fetchall()
    require(len(found) == 1, f"{label}: expected exactly one persisted row, got {len(found)}")
    return found[0]


def audit(native: dict, owner: dict, crosswalk: dict, conn) -> dict:
    """Evidence gate, not a candidate-set resolver or QID projection."""
    alignment = verify_owner_carrier(native, owner)
    source, focus = native["source"], native["focus_mention"]
    require(native["authority"] == "candidate_only", "promoted native source")
    require(not native["semantic_authority_promoted"], "promoted native authority")
    for k in ("source_revision_ref", "parser_run_ref", "region_ref"):
        require(crosswalk.get(k) == source[k], "crosswalk wrong " + k)
    for k in ("source_start_char", "source_end_char", "surface", "candidate_ref"):
        require(crosswalk.get(k) == focus[k], "crosswalk wrong " + k)
    require(crosswalk.get("owner_document_ref") == source["document_ref"],
            "owner/native document disagreement")
    require(crosswalk.get("coordinate_frame") in ("region_local", "source_absolute"),
            "unlicensed coordinate frame")
    index = [i for i, t in enumerate(native["parser_tokens"])
             if t["start_char"] == focus["source_start_char"]
             and t["end_char"] == focus["source_end_char"]]
    require(len(index) == 1, "focus must be one original parser token")
    require(native["parser_tokens"][index[0]]["pos"] == "PRON",
            "focus is not a native pronoun observation")
    # Original SensibLaw factor anchor is metadata.atom_span_ref or
    # licensing.mentions/metadata.mention_ref; never add an imaginary
    # parser_token_index field to the owner's semantic factor.
    factors = [f for f in owner["pnf_graph"].get("factors", ())
               if f.get("factor_ref") == crosswalk.get("factor_ref")]
    require(len(factors) == 1, "missing/duplicate owner factor")
    meta = factors[0].get("metadata") or {}
    require(meta.get("parser_pos") == "PRON", "owner focus factor not pronoun-typed")
    spans = (owner.get("semantic_annotation_layer") or {}).get("span_annotations") or ()
    anchored = any(row.get("span_ref") == meta.get("atom_span_ref")
                   and row.get("annotation_type") in ("semantic_atom", "parser_token")
                   and row.get("start_token") == index[0]
                   and row.get("end_token") == index[0] + 1
                   for row in spans) if meta.get("atom_span_ref") else False
    mentions = (owner.get("licensing") or {}).get("mentions") or ()
    anchored = anchored or any(row.get("mention_ref") == meta.get("mention_ref")
                               and row.get("start_token") == index[0]
                               and row.get("end_token") == index[0] + 1
                               for row in mentions) if meta.get("mention_ref") else anchored
    require(anchored, "owner semantic factor lacks exact focus-token anchor")
    require(crosswalk.get("owner_graph_ref") == owner["pnf_graph"].get("graph_ref"),
            "numeric crosswalk does not name original owner graph")
    for field in ("source_object_id", "premise_factor_id", "demand_id"):
        require(type(crosswalk.get(field)) is int and crosswalk[field] > 0,
                "missing exact numeric " + field)
    obj, premise, demand = (crosswalk[k] for k in
                            ("source_object_id", "premise_factor_id", "demand_id"))
    with conn.cursor() as cur:
        # Read-only transaction established by caller. No refresh/backfill.
        run, doc, left, right = one(cur, """
            SELECT r.run_ref,r.document_ref,r.start_char,r.end_char
              FROM execution.semantic_pnf_object o
              JOIN execution.semantic_pnf_region r ON r.region_id=o.region_id
             WHERE o.object_id=%s
        """, (obj,), "original owner source object")
        require(run == crosswalk.get("owner_run_ref") and doc == source["document_ref"],
                "owner numeric source scope mismatch")
        off = 0 if crosswalk["coordinate_frame"] == "source_absolute" else source["region_start_char"]
        a, b = focus["source_start_char"]-off, focus["source_end_char"]-off
        require(left <= a < b <= right, "owner numeric region excludes focus")
        linked, = one(cur, """
            SELECT count(*) FROM execution.semantic_pnf_hyperedge
             WHERE factor_id=%s AND object_id=%s
        """, (premise, obj), "original Level-1 premise edge")
        require(linked > 0, "missing original Level-1 premise edge")
        target_kind, target_id, outcome, candidate_count = one(cur, """
            SELECT r.selected_target_kind,r.selected_target_id,
                   r.outcome_state,r.candidate_count
              FROM execution.semantic_pnf_frontier_resolution r
              JOIN execution.semantic_pnf_demand d ON d.demand_id=r.demand_id
             WHERE r.demand_id=%s AND d.source_object_id=%s
        """, (demand, obj), "original resolved demand")
        require((outcome, candidate_count, target_kind) == (2, 1, 1),
                "demand not resolved_unique with one object target")
        entity, anchor, authority, witness_ids = one(cur, """
            SELECT p.target_entity_id,e.anchor_object_id,e.authority_class,p.witness_ids
              FROM execution.semantic_pnf_identity_projection p
              JOIN execution.semantic_pnf_canonical_entity e
                ON e.entity_id=p.target_entity_id
             WHERE p.source_object_id=%s AND p.authority_class=2
        """, (obj,), "original admitted identity projection")
        require(anchor == target_id and authority == 2 and bool(witness_ids),
                "projection target/authority does not match resolved object")
        witness = one(cur, """
            SELECT w.witness_id,w.witness_kind,w.candidate_count,w.authority_class,
                   a.admission_state
              FROM execution.semantic_pnf_identity_witness w
              JOIN execution.semantic_pnf_identity_witness_admission a
                ON a.witness_id=w.witness_id
             WHERE w.source_object_id=%s AND w.target_entity_id=%s AND w.demand_id=%s
        """, (obj, entity, demand), "original anaphor witness")
        wid, kind, count, wauth, admission = witness
        require((kind, count, wauth, admission) == (5, 1, 2, 2),
                "missing admitted anaphor_demand_resolution witness")
        require(wid in witness_ids, "accepted witness absent from current projection")
        cur.execute("""
            SELECT d.derivation_id,a.identity_entity_id,a.identity_witness_ids
              FROM execution.semantic_pnf_factor_derivation d
              JOIN execution.semantic_pnf_factor_derivation_premise p
                ON p.derivation_id=d.derivation_id AND p.premise_ordinal=0
              JOIN execution.semantic_pnf_factor_derivation_argument a
                ON a.derivation_id=d.derivation_id
             WHERE d.rule_ref='identity-substitution:v1'
               AND d.epistemic_level=3 AND p.factor_id=%s
               AND a.source_object_id=%s
        """, (premise, obj))
        derivations = cur.fetchall()
        require(bool(derivations), "no Level-3 substitution for original premise")
        require(all(ident == entity and wid in (ids or ())
                    for _, ident, ids in derivations),
                "Level-3 substitution does not retain admitted identity witness")
    return {"schema": "gwb-native-owner-admitted-identity-v1",
            "source_revision_ref": source["source_revision_ref"],
            "region_ref": source["region_ref"],
            "focus_mention_ref": focus["mention_ref"],
            "owner_run_ref": run,
            "owner_factor_ref": factors[0]["factor_ref"],
            "source_object_id": obj, "demand_id": demand,
            "document_local_entity_id": entity, "witness_id": wid,
            "derivation_ids": [row[0] for row in derivations],
            "source_alignment": alignment["source_alignment"],
            "identity_admission": "ORIGINAL_DB_ADMITTED_RESOLVED_UNIQUE",
            "external_qid": "NOT_TESTED", "historical_truth": "NOT_LICENSED"}


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    for name in ("native", "owner", "owner_crosswalk", "output"):
        ap.add_argument("--" + name.replace("_", "-"), type=Path, required=True)
    args = ap.parse_args()
    import psycopg2
    native, owner, crosswalk = (json.loads(getattr(args, key).read_text())
                                for key in ("native", "owner", "owner_crosswalk"))
    conn = psycopg2.connect(os.environ["SENSIBLAW_DATABASE_URL"])
    try:
        conn.set_session(isolation_level="REPEATABLE READ", readonly=True)
        receipt = audit(native, owner, crosswalk, conn)
    finally:
        conn.close()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2) + "\n")
    print("GWB_C409B_ORIGINAL_DB_IDENTITY_ADMISSION_OK")


if __name__ == "__main__":
    main()
