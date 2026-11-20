#!/usr/bin/env python3
"""Inspect existing checked relation rows; no identity resolution or parser."""
import argparse
from collections import defaultdict, Counter
import json
from pathlib import Path
from gwb_semantic_observer_audit import load, check, require

def inspect(article, slr, proj, p0b, receipt):
    audit = check(article, slr, proj, p0b)
    require(receipt["source_revision"] == slr["revision_ref"] and
            receipt["source_unit_ref"] == slr["source_unit_ref"], "source mismatch")
    sentences = {s["sentence_index"]: s for s in slr["pnf_candidates"]}
    tokens = {(sid,t["i"]):t for sid,s in sentences.items() for t in s["dependency_rows"]}
    mentions = p0b["mentions"]
    licences = defaultdict(list)
    for lic in p0b["licenses"]:
        licences[lic["mention_ref"]].append(lic)
    def endpoint(sid, i):
        t = tokens[sid,i]
        a,b = t["idx"],t["idx"]+len(t["text"])
        require(article[a:b] == t["text"], "endpoint literal mismatch")
        return dict(token=t, literal=article[a:b], mentions=[
            dict(mention=m, licences=licences[m["mention_ref"]])
            for m in mentions if m["start_char"] < b and a < m["end_char"]])
    incoming=defaultdict(list)
    indexed={}
    relations=[]
    for r in receipt["relations"]:
        sid,i=r["sentence_index"],r["token_i"]
        require((sid,i) not in indexed, "duplicate relation")
        t=tokens[sid,i]
        require(r["head_i"]==t["head_i"] and r["start_char"]==t["idx"] and
                r["end_char"]==t["idx"]+len(t["text"]) and
                r["candidate_only"] is True and r["context_resolution_required"] is True,
                "relation coordinate or authority mismatch")
        edge=dict(relation=r, dependent=endpoint(sid,i), head=endpoint(sid,r["head_i"]))
        indexed[sid,i]=edge
        incoming[sid,r["head_i"]].append(edge)
        relations.append(edge)
    cases=[]
    for event in proj["event_candidates"]:
        sid=event["sentence_index"]
        for role in ("actors","patients"):
            for item in event[role]:
                if (role,item["surface"]) not in (("actors","by"),("patients","to")):
                    continue
                if any(m["start_char"]==item["start_char"] and m["end_char"]==item["end_char"] for m in mentions):
                    continue
                matches=[t for t in sentences[sid]["dependency_rows"] if
                         t["idx"]==item["start_char"] and t["idx"]+len(t["text"])==item["end_char"]]
                require(len(matches)==1,"marker span mismatch")
                i=matches[0]["i"]
                cases.append(dict(event=event,role_observation=item,role=role,
                    marker=endpoint(sid,i), marker_relation=indexed.get((sid,i)),
                    structural_children=incoming[sid,i],
                    sentence_text=article[sentences[sid]["source_span_start"]:sentences[sid]["source_span_end"]],
                    semantic_identity_paid=False, semantic_role_paid=False))
    fibres=[]
    for f in audit["p0b_selected_individual_fibres"]:
        keys={(c["sentence_index"],t["i"]) for c in f["parser_contexts"] for t in c["mention_tokens"]}
        edges=[e for e in relations if (e["relation"]["sentence_index"],e["relation"]["token_i"]) in keys or
               (e["relation"]["sentence_index"],e["relation"]["head_i"]) in keys]
        fibres.append(dict(original_fibre=f,incident_relations=edges))
    return dict(schema="gwb-relation-mention-inspection-v1",source_revision=slr["revision_ref"],
                source_utf8_sha256=audit["source_utf8_sha256"],relation_count=len(relations),
                relation_kind_counts=dict(Counter(e["relation"]["kind"] for e in relations)),
                marker_counts=dict(Counter(c["role_observation"]["surface"] for c in cases)),
                marker_cases=cases,selected_fibres=fibres,relations=relations,
                semantic_identity_paid=False,semantic_role_paid=False)

def main():
    p=argparse.ArgumentParser()
    p.add_argument("source")
    p.add_argument("relations",type=Path)
    p.add_argument("output",type=Path)
    a=p.parse_args()
    result=inspect(*load(a.source),json.loads(a.relations.read_text()))
    a.output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
    print("GWB_RELATION_MENTION_INSPECTION",result["relation_count"],result["marker_counts"],"fibres",len(result["selected_fibres"]))

if __name__=="__main__":
    main()
