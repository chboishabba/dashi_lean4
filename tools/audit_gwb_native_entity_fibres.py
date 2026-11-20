#!/usr/bin/env python3
"""Offline candidate-only audit of native semantic v2 (JSON or gzip)."""
import argparse
from collections import Counter, defaultdict
import gzip
import hashlib
import json
from pathlib import Path
import struct

PRONOUNS = set("i me my mine myself we us our ours ourselves you your yours yourself yourselves he him his himself she her hers herself it its itself they them their theirs themselves who whom whose".split())
# Rust char::is_whitespace uses Unicode White_Space, not Python's extra C0 separators.
WS = " \t\n\r\v\f\u0085\u00a0\u1680\u2000\u2001\u2002\u2003\u2004\u2005\u2006\u2007\u2008\u2009\u200a\u2028\u2029\u202f\u205f\u3000"

def normalize(s):
    return " ".join(x for x in "".join(" " if c in WS else c for c in s).split(" ") if x).lower()

def digest(domain, *parts):
    h = hashlib.sha256()
    for part in (domain, *parts):
        b = part.encode("utf-8")
        h.update(struct.pack(">Q", len(b)))
        h.update(b)
    return "sha256:" + h.hexdigest()

def require(ok, message):
    if not ok:
        raise ValueError(message)

def boundary(rows):
    for row in rows:
        if "candidate_only" in row:
            require(row["candidate_only"] is True, "noncandidate row")
        for k, v in row.items():
            if k in {"creates_entity_identity", "creates_event_identity", "creates_proposition_identity", "creates_semantic_authority", "claim_truth_promoted", "applicability_promoted"}:
                require(v is False, "promotion: " + k)

def audit(d, limit):
    require(d["schema"] == "gwb-native-semantic-observation-v2", "wrong schema")
    f = d["native_entity_fibres"]
    m = f["general_mentions"]
    run = d["selected_run"]
    require(d["semantic_authority"]["candidate_only"] is True, "authority boundary")
    require(all(d["semantic_authority"][k] is False for k in ("creates_identity","creates_event_identity","claim_truth_promoted")), "authority boundary")
    for rows in (m, f["entity_factors"], f["product_factors"], f["product_summaries"], f["matching_global_pressure_candidates"], *d["selected_run_candidates"].values()):
        boundary(rows)
    require(len({x["mention_ref"] for x in m}) == len(m), "duplicate mentions")
    index = defaultdict(list)
    for x in f["entity_factors"]:
        index[x["product_ref"]].append(x)
    native = {(x["product_ref"], x["factor_ordinal"]): x for x in f["product_factors"]}
    expected = defaultdict(list)
    for b in f["batch_bindings"]:
        for x in index[b["candidate_product_ref"]]:
            p = native[(x["product_ref"], x["factor_ordinal"])]
            require(all(p[k] == x[k] for k in ("token_ordinal","start_offset","end_offset","surface","lemma","role_ref")), "factor drift")
            start = b["region_start_char"] + x["start_offset"]
            end = b["region_start_char"] + x["end_offset"]
            require(0 <= start < end, "invalid occurrence span")
            c = f'candidate-pnf-db:{run}:{b["exact_span_ref"]}:{x["token_ordinal"]}:{start}:{end}'
            ref = "entity-mention:" + digest("entity-mention:v1", b["statement_ref"], b["batch_ref"], c)
            expected[ref].append((b, x, c, start, end))
    counts = Counter()
    fibres = defaultdict(list)
    pronouns = []
    bad = []
    for x in m:
        fp = "entity-fingerprint:" + digest("entity:v1", normalize(x["lemma"]))
        matches = expected.get(x["mention_ref"], [])
        good = [b for b,y,c,s,e in matches if x["statement_ref"] == b["statement_ref"] and x["candidate_ref"] == c and x["source_start_char"] == s and x["source_end_char"] == e and all(x[k] == y[k] for k in ("surface","lemma","role_ref","detector_ref","entity_fingerprint_ref"))]
        counts["fingerprint_match"] += fp == x["entity_fingerprint_ref"]
        counts["unique_occurrence_match"] += len(good) == 1
        if fp != x["entity_fingerprint_ref"] or len(good) != 1:
            if len(bad) < limit:
                bad.append(x["mention_ref"])
        fibres[x["entity_fingerprint_ref"]].append(x)
        if normalize(x["surface"]) in PRONOUNS or normalize(x["lemma"]) in PRONOUNS:
            pronouns.append(x)
    names = defaultdict(list)
    for x in d["selected_run_candidates"]["named_entities"]:
        names[x["statement_ref"]].append(x)
    samples = []
    # Same statement, preceding NER only: candidate search, not a resolver.
    for x in pronouns:
        preceding = [n for n in names[x["statement_ref"]] if n["end_char"] <= x["source_start_char"]]
        if not preceding:
            continue
        samples.append({"mention": x, "preceding_named_candidates": sorted(preceding,key=lambda n:n["end_char"],reverse=True)[:5], "identity_status":"unresolved"})
        if len(samples) >= limit:
            break
    review = defaultdict(set)
    for x in f["review_delta_fibres"]:
        # Installed schema uses review_item, not the later delta-fibre table.
        ref = x["review_item_ref"]
        prefix = "review-item:reconciliation:"
        require(ref.startswith(prefix), "unexpected review reference")
        revisions = [s["source_revision_ref"] for s in d["source"] if ref.startswith(prefix+s["source_revision_ref"]+":")]
        require(len(revisions)==1, "unscoped review")
        review[revisions[0]].add(x["semantic_ref"])
    revs = sorted(review)
    overlap = review[revs[0]] & review[revs[1]] if len(revs)==2 else set()
    return {"schema":"gwb-native-entity-audit-v1","candidate_only":True,
            "creates_identity":False,"creates_semantic_authority":False,
            "source_sha256":d["source_sha256"],"selected_run":run,
            "counts":{k:len(f[k]) for k in ("general_mentions","batch_bindings","product_factors","entity_factors","review_delta_fibres","matching_global_pressure_candidates")},
            "replay":dict(counts),"expected_distinct_occurrences":len(expected),
            "expected_not_exported":len(set(expected)-{x["mention_ref"] for x in m}),
            "mismatch_examples":bad,
            "pronoun_count":len(pronouns),
            "pronoun_histogram":[{"surface":s,"lemma":l,"role":r,"count":n} for (s,l,r),n in sorted(Counter((x["surface"],x["lemma"],x["role_ref"]) for x in pronouns).items())],
            "lexical_fibre_count":len(fibres),
            "repeated_fibres":[{"fingerprint":k,"count":len(v),"statement_count":len({x["statement_ref"] for x in v}),"examples":v[:3]} for k,v in sorted(fibres.items(),key=lambda kv:(-len(kv[1]),kv[0]))[:limit] if len(v)>1],
            "antecedent_search_examples":samples,"antecedent_resolution":"NOT_TESTED",
            "source_excerpts":"NOT_EXPORTED_IN_BINDINGS",
            "review_unique_semantic_refs_by_revision":{k:len(v) for k,v in review.items()},
            "review_shared_semantic_refs":len(overlap),
            "review_only_by_revision":{k:len(v-overlap) for k,v in review.items()},
            "identity_controls":"NOT_TESTED","empirical_nonfactorisation":"OPEN"}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--input",type=Path,required=True)
    ap.add_argument("--output",type=Path,required=True)
    ap.add_argument("--limit",type=int,default=30)
    a=ap.parse_args()
    require(a.limit>0,"positive limit required")
    require(a.input.resolve()!=a.output.resolve(),"refuse overwrite input")
    opener=gzip.open if a.input.suffix==".gz" else open
    with opener(a.input,"rt",encoding="utf-8") as stream:
        d=json.load(stream)
    result=audit(d,a.limit)
    h=hashlib.sha256()
    with a.input.open("rb") as stream:
        for chunk in iter(lambda:stream.read(1024*1024),b""):
            h.update(chunk)
    result["input_artifact_sha256"]=h.hexdigest()
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n",encoding="utf-8")
    print(json.dumps(result["replay"],sort_keys=True))
    require(result["replay"].get("fingerprint_match")==result["counts"]["general_mentions"],"fingerprint mismatch")
    require(result["replay"].get("unique_occurrence_match")==result["counts"]["general_mentions"],"occurrence mismatch")
    require(result["expected_not_exported"]==0,"missing reconstructed mentions")

if __name__=="__main__":
    main()
