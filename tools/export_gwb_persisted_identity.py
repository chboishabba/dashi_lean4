#!/usr/bin/env python3
"""Read persisted numeric PNF identities, never refresh or resolve them.

Run with the SensibLaw Python environment. This is a DB observation export,
not a Lean certificate or a new semantic producer.
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
import os
from pathlib import Path
import sys

REVISION = "enwiki-revid:1385850169"
DIGEST = "a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233"


def require(ok, message):
    if not ok:
        raise ValueError(message)


def read_inputs(article_path, audit_path):
    raw = article_path.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == DIGEST, "wrong article bytes")
    article = raw.decode("utf-8")
    audit = json.loads(audit_path.read_text(encoding="utf-8"))
    require(audit["source_revision"] == REVISION and
            audit["source_utf8_sha256"] == DIGEST, "wrong audit source")
    fibres = audit["p0b_selected_individual_fibres"]
    require(len(fibres) == 534, "wrong selected fibre inventory")
    require(len({x["mention"]["mention_ref"] for x in fibres}) == 534,
            "duplicate source mention")
    for f in fibres:
        m = f["mention"]
        a, b = m["start_char"], m["end_char"]
        require(0 <= a < b <= len(article) and article[a:b] == f["literal"],
                "bad source mention span")
    return raw, fibres


def rows(cur, sql, params=()):
    cur.execute(sql, params)
    return [r[0] for r in cur.fetchall()]


def group(records, key):
    out = defaultdict(list)
    for r in records:
        out[r[key]].append(r)
    return out


def attach(fibres, mentions, demands, candidates, resolutions, witnesses,
           projections, participation):
    by_span = defaultdict(list)
    for m in mentions:
        by_span[m["start_char"], m["end_char"]].append(m)
    by_object = group(demands, "source_object_id")
    by_demand_c = group(candidates, "demand_id")
    by_demand_r = group(resolutions, "demand_id")
    by_witness = group(witnesses, "source_object_id")
    by_projection = group(projections, "source_object_id")
    by_participation = group(participation, "surface_object_id")
    output = []
    for f in fibres:
        m = f["mention"]
        matches = []
        for db in by_span[m["start_char"], m["end_char"]]:
            oid = db["object_id"]
            ds = [dict(d, candidates=by_demand_c[d["demand_id"]],
                       frontier_resolutions=by_demand_r[d["demand_id"]])
                  for d in by_object[oid]] if oid is not None else []
            matches.append(dict(mention=db, demands=ds,
                                witnesses=by_witness[oid],
                                identity_projections=by_projection[oid],
                                witnessed_participation=by_participation[oid]))
        output.append(dict(source_mention=m, literal=f["literal"],
                           source_licences=f["original_licences"],
                           coordinate_matches=matches,
                           coordinate_status=("absent" if not matches else
                                              "one" if len(matches) == 1 else "multiple")))
    return output


def extract(cur, run, doc, raw, fibres):
    scope = (run, doc)
    sources = rows(cur, """
        SELECT jsonb_build_object('source_ref',source_ref,
            'run_ref',run_ref,'document_ref',document_ref,
            'sha256',encode(content_sha256,'hex'),'byte_count',byte_count)
        FROM execution.semantic_parser_source
        WHERE run_ref=%s AND document_ref=%s
        ORDER BY source_ref
    """, scope)
    require(len(sources) == 1 and sources[0]["sha256"] == DIGEST and
            sources[0]["byte_count"] == len(raw), "DB parser source mismatch/ambiguity")
    # Every selected mention is rooted in a sentence whose actual partition
    # cites the matching parser source. Do not join on a surname or lemma.
    mentions = rows(cur, """
        SELECT to_jsonb(m) || jsonb_build_object('sentence_ref',s.sentence_ref,
            'source_ref',p.source_ref,'region_run_ref',r.run_ref,
            'region_document_ref',r.document_ref)
        FROM execution.semantic_pnf_mention m
        JOIN execution.semantic_pnf_region r ON r.region_id=m.region_id
        JOIN execution.semantic_parser_sentence s ON s.sentence_id=m.sentence_id
        JOIN execution.semantic_parser_partition p ON p.partition_ref=s.partition_ref
        WHERE r.run_ref=%s AND r.document_ref=%s AND m.active
          AND s.run_ref=r.run_ref AND s.document_ref=r.document_ref
          AND p.source_ref=%s
        ORDER BY m.start_char,m.end_char,m.mention_id
    """, (*scope, sources[0]["source_ref"]))
    selected_spans = {(f["mention"]["start_char"], f["mention"]["end_char"]) for f in fibres}
    mentions = [m for m in mentions if (m["start_char"],m["end_char"]) in selected_spans]
    ids = sorted({m["object_id"] for m in mentions if m["object_id"] is not None})
    # Object scope must match source. Reject a foreign object instead of
    # accepting the mention's object_id as an identity assertion.
    objects = rows(cur, """
        SELECT to_jsonb(o) FROM execution.semantic_pnf_object o
        JOIN execution.semantic_pnf_region r ON r.region_id=o.region_id
        WHERE o.object_id=ANY(%s::bigint[]) AND r.run_ref=%s AND r.document_ref=%s
        ORDER BY o.object_id
    """, (ids,*scope))
    require({o["object_id"] for o in objects} == set(ids), "foreign source object")
    demands = rows(cur, """
        SELECT to_jsonb(d) || jsonb_build_object('residual',sym.symbol_text)
        FROM execution.semantic_pnf_demand d
        JOIN execution.semantic_pnf_region r ON r.region_id=d.source_region_id
        JOIN execution.semantic_symbol sym ON sym.symbol_id=d.residual_type_symbol_id
        WHERE d.source_object_id=ANY(%s::bigint[]) AND r.run_ref=%s AND r.document_ref=%s
        ORDER BY d.demand_id
    """, (ids,*scope))
    dids = [d["demand_id"] for d in demands]
    candidates = rows(cur, """
        SELECT to_jsonb(c) FROM execution.semantic_pnf_demand_candidate c
        WHERE c.demand_id=ANY(%s::bigint[]) ORDER BY c.demand_id,c.ordinal
    """, (dids,))
    resolutions = rows(cur, """
        SELECT to_jsonb(f) || jsonb_build_object('outcome',o.outcome_name)
        FROM execution.semantic_pnf_frontier_resolution f
        JOIN execution.semantic_pnf_frontier_outcome o USING(outcome_state)
        WHERE f.demand_id=ANY(%s::bigint[]) ORDER BY f.demand_id,f.interface_id
    """, (dids,))
    witnesses = rows(cur, """
        SELECT to_jsonb(w) || jsonb_build_object('admission',to_jsonb(a),
            'admission_name',st.admission_name,'witness_name',k.witness_name,
            'constraints',COALESCE((SELECT jsonb_agg(to_jsonb(c) ORDER BY c.constraint_ordinal)
                FROM execution.semantic_pnf_identity_witness_constraint c
                WHERE c.witness_id=w.witness_id),'[]'::jsonb))
        FROM execution.semantic_pnf_identity_witness w
        LEFT JOIN execution.semantic_pnf_identity_witness_admission a USING(witness_id)
        LEFT JOIN execution.semantic_pnf_identity_admission_state st USING(admission_state)
        JOIN execution.semantic_pnf_identity_witness_kind k USING(witness_kind)
        WHERE w.source_object_id=ANY(%s::bigint[]) ORDER BY w.witness_id
    """, (ids,))
    projections = rows(cur, """
        SELECT to_jsonb(p) || jsonb_build_object('entity',to_jsonb(e),
            'canonical_label',s.symbol_text)
        FROM execution.semantic_pnf_identity_projection p
        JOIN execution.semantic_pnf_canonical_entity e ON e.entity_id=p.target_entity_id
        LEFT JOIN execution.semantic_symbol s ON s.symbol_id=e.canonical_symbol_id
        WHERE p.source_object_id=ANY(%s::bigint[]) ORDER BY p.source_object_id,p.authority_class
    """, (ids,))
    participation = rows(cur, """
        SELECT to_jsonb(h) FROM execution.semantic_pnf_witnessed_hyperedge h
        WHERE h.surface_object_id=ANY(%s::bigint[])
        ORDER BY h.surface_object_id,h.factor_id,h.slot_ordinal,h.epistemic_level
    """, (ids,))
    # Retain original target objects and their exact source supports so target
    # IDs are not mistaken for portable entity identity.
    target_ids = sorted({r["target_id"] for r in candidates if r["target_kind"] == 1}
                        | {r["selected_target_id"] for r in resolutions
                           if r["selected_target_kind"] == 1 and r["selected_target_id"] is not None}
                        | {p["entity"]["anchor_object_id"] for p in projections
                           if p["entity"]["anchor_object_id"] is not None})
    targets = rows(cur, """
        SELECT to_jsonb(o) || jsonb_build_object('region',to_jsonb(r),
            'head',s.symbol_text,'mention_support',COALESCE((
                SELECT jsonb_agg(to_jsonb(m) ORDER BY m.mention_id)
                FROM execution.semantic_pnf_object_mention_support x
                JOIN execution.semantic_pnf_mention m USING(mention_id)
                WHERE x.object_id=o.object_id),'[]'::jsonb))
        FROM execution.semantic_pnf_object o
        JOIN execution.semantic_pnf_region r USING(region_id)
        LEFT JOIN execution.semantic_symbol s ON s.symbol_id=o.head_symbol_id
        WHERE o.object_id=ANY(%s::bigint[]) AND r.run_ref=%s AND r.document_ref=%s
        ORDER BY o.object_id
    """, (target_ids,*scope))
    selected = attach(fibres, mentions, demands, candidates, resolutions,
                      witnesses, projections, participation)
    return dict(schema="gwb-persisted-identity-observation-v1",
                source_revision=REVISION, source_sha256=DIGEST,
                parser_source=sources[0], selected_fibres=selected,
                source_objects=objects, same_document_target_objects=targets,
                unexported_target_object_ids=sorted(set(target_ids)-{t["object_id"] for t in targets}),
                coordinate_counts=dict(Counter(f["coordinate_status"] for f in selected)),
                resolution_counts=dict(Counter(r["outcome"] for r in resolutions)),
                admission_counts=dict(Counter(w["admission_name"] or "absent" for w in witnesses)),
                world_truth_paid=False, lean_checked=False)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--sensiblaw-root", type=Path, required=True)
    p.add_argument("--run-ref", required=True)
    p.add_argument("--document-ref", required=True)
    p.add_argument("--article", type=Path, default=Path(".dashi/gwb-source/article.txt"))
    p.add_argument("--audit", type=Path, default=Path(".dashi/gwb-relation/mention-inspection.json"))
    p.add_argument("--output", type=Path, default=Path(".dashi/gwb-relation/persisted-identity.json"))
    a = p.parse_args()
    raw, fibres = read_inputs(a.article, a.audit)
    sys.path.insert(0, str(a.sensiblaw_root.resolve()))
    from src.storage.postgres.spacy_parser_model import connect
    conn = connect(os.environ["DATABASE_URL"])
    try:
        with conn.transaction():
            with conn.cursor() as cur:
                cur.execute("SET TRANSACTION ISOLATION LEVEL REPEATABLE READ, READ ONLY")
                cur.execute("SET LOCAL statement_timeout = '120s'")
                result = extract(cur, a.run_ref, a.document_ref, raw, fibres)
    finally:
        conn.close()
    a.output.parent.mkdir(parents=True, exist_ok=True)
    temp = a.output.with_suffix(a.output.suffix + ".tmp")
    temp.write_text(json.dumps(result, ensure_ascii=False, indent=2, default=str)+"\n",
                    encoding="utf-8")
    temp.replace(a.output)
    print("GWB_PERSISTED_IDENTITY_OBSERVATION", result["coordinate_counts"],
          result["resolution_counts"], result["admission_counts"])


if __name__ == "__main__":
    main()
