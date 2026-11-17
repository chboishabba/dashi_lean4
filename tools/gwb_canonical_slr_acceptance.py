#!/usr/bin/env python3
"""Audit original SLR/ITIR source carriers, not experimental Rust candidates."""
import argparse, json, hashlib
from collections import Counter
from pathlib import Path
REV="enwiki-revid:1385850169"
SHA="a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233"
def demand(test,why):
    if not test: raise ValueError(why)
def inspect(article,slr,projection,p0b):
    digest=hashlib.sha256(article.encode("utf-8")).hexdigest()
    demand(digest==SHA,"source sha")
    demand(slr.get("schema")=="slr-source-unit-pnf-record-v1","wrong SLR producer")
    demand(projection.get("schema")=="slr-jmd-wikipedia-article-candidates-v1","wrong article projection")
    demand(slr.get("revision_ref")==REV==projection.get("source_revision_ref"),"revision")
    demand(slr.get("manifestation",{}).get("source_text_sha256")==digest and
           projection.get("source_text_sha256")==digest,"source hash")
    sr=slr.get("source_unit_ref")
    demand(bool(sr) and sr==projection.get("source_unit_ref")==p0b.get("source_ref"),"source refs")
    demand(slr.get("candidate_only") is True and slr.get("semantic_promotion") is False,"source promotion")
    for flag in ("source_assertion_is_world_truth","parser_carries_semantic_licence",
                 "cross_sentence_identity_paid","text_order_is_event_chronology"):
        demand(projection.get(flag) is False,flag+" promoted")
    sentences=slr.get("pnf_candidates")
    events=projection.get("event_candidates")
    years=projection.get("timeline_candidates")
    sections=projection.get("sections")
    proper=projection.get("proper_noun_tokens")
    mentions=p0b.get("mentions")
    licences=p0b.get("licenses")
    for name,rows in (("sentences",sentences),("events",events),("years",years),
                      ("sections",sections),("proper",proper),("mentions",mentions),
                      ("licences",licences)):
        demand(isinstance(rows,list),"missing "+name)
    demand(len(sentences)==643,"pinned source sentence count")
    index={row["sentence_index"]:row for row in sentences}
    demand(len(index)==len(sentences),"duplicate sentence")
    deps=Counter()
    for row in sentences:
        demand(row.get("candidate_only") is True and row.get("semantic_promotion") is False,"sentence promotion")
        for token in row["dependency_rows"]:
            demand(isinstance(token.get("dep"),str) and bool(token["dep"]),"missing dependency")
            demand(isinstance(token.get("head_i"),int) and isinstance(token.get("idx"),int),
                   "missing parser head or offset")
            deps[token["dep"]]+=1
    event_deps=Counter()
    for e in events:
        source=index.get(e.get("sentence_index"))
        demand(source is not None,"orphan event")
        demand(e.get("candidate_only") is True and e.get("semantic_licence_paid") is False and
               e.get("world_event_occurrence_paid") is False,"event promotion")
        pred=e.get("predicate",{})
        demand(any(t.get("i")==pred.get("i") and t.get("idx")==pred.get("start_char") and
                   t.get("text")==pred.get("surface") for t in source["dependency_rows"]),
               "predicate not anchored in original SLR")
        for role in ("actors","patients"):
            demand(isinstance(e.get(role),list),"missing role observations")
        event_deps[str(pred.get("dep"))]+=1
    for row in years:
        demand(row.get("candidate_only") is True and row.get("event_time_paid") is False and
               row.get("kind")=="source-year-mention-not-event-date","time promotion")
    return {
      "schema":"gwb-original-slr-canonical-source-acceptance-v1",
      "source_revision":REV,"source_utf8_sha256":digest,"source_unit_ref":sr,
      "original_slr_producer_schema":slr["schema"],
      "original_article_projection_schema":projection["schema"],
      "parser_receipt":slr.get("parser_receipt"),
      "counts":{"sentences":len(sentences),"parser_tokens":sum(deps.values()),
                "dependency_labels":len(deps),"original_predicates":len(events),
                "actor_role_observations":sum(len(e["actors"]) for e in events),
                "patient_role_observations":sum(len(e["patients"]) for e in events),
                "year_occurrences":len(years),"proper_noun_tokens":len(proper),
                "sections":len(sections),"p0b_mentions":len(mentions),
                "p0b_licenses":len(licences)},
      "original_dependency_histogram":dict(sorted(deps.items())),
      "selected_predicate_dependency_histogram":dict(sorted(event_deps.items())),
      "experimental_sl_semantic_expansion_used":False,
      "semantic_authority_created":False,
      "original_source_provenance_checked":True,
      "reviewed_semantic_admission":"requires separate existing SensibLaw/ITIR review receipts",
    }
def main():
    p=argparse.ArgumentParser()
    p.add_argument("--source-dir",type=Path,default=Path(".dashi/gwb-source"))
    p.add_argument("--output",type=Path,required=True)
    a=p.parse_args(); d=a.source_dir
    result=inspect((d/"article.txt").read_text(encoding="utf-8"),
                   json.loads((d/"slr-record.json").read_text(encoding="utf-8")),
                   json.loads((d/"article-candidates.json").read_text(encoding="utf-8")),
                   json.loads((d/"gwb_sensiblaw_p0b_mention_licences.json").read_text(encoding="utf-8")))
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print("GWB_CANONICAL_SLR_SOURCE_VALIDATED",result["counts"],"experimental_projector=false")
if __name__=="__main__":main()
