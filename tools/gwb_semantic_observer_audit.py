#!/usr/bin/env python3
"""Read-only GWB semantic-observer adequacy audit. NO NLP producer.

Only reopens original SLR dependency rows, article candidate observations,
and P0b mention licences. Tests what queries do *not* factor through lossy
scope/role/year projections. Never resolves identities, temporal assertions,
world truth, or reviewed semantic-fibre closure.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import tarfile

EMBED = frozenset(("acl", "relcl", "ccomp", "xcomp", "advcl"))

def require(ok, why):
    if not ok:
        raise ValueError(why)

def load(path):
    """Read existing source evidence from a directory; legacy TAR is import-only."""
    source = Path(path)
    names = ("article.txt", "slr-record.json",
             "article-candidates.json", "gwb_sensiblaw_p0b_mention_licences.json")
    if source.is_dir():
        content = {name: (source / name).read_text(encoding="utf-8")
                   for name in names}
    else:
        with tarfile.open(source, "r:") as archive:
            members = archive.getmembers()
            require(len(set(m.name for m in members)) == len(members),
                    "duplicate legacy input TAR members")
            require(all(m.isfile() for m in members), "unsafe TAR member")
            content = {name: archive.extractfile(name).read().decode("utf-8")
                       for name in names}
    return (content["article.txt"],
            json.loads(content["slr-record.json"]),
            json.loads(content["article-candidates.json"]),
            json.loads(content["gwb_sensiblaw_p0b_mention_licences.json"]))

def check(article, slr, proj, p0b):
    digest = hashlib.sha256(article.encode("utf-8")).hexdigest()
    require(slr["manifestation"]["source_text_sha256"] == digest,
            "original SLR raw UTF-8 SHA")
    require(proj["source_text_sha256"] == digest, "projection raw UTF-8 SHA")
    require(slr["revision_ref"] == proj["source_revision_ref"], "source revision")
    require(slr["source_unit_ref"] == proj["source_unit_ref"] == p0b["source_ref"],
            "source unit identity")
    sentences = {c["sentence_index"]: c for c in slr["pnf_candidates"]}
    events = proj["event_candidates"]
    event_by_sentence = collections.defaultdict(list)
    mention_spans = {(m["start_char"], m["end_char"]) for m in p0b["mentions"]}
    require(len(mention_spans) == len(p0b["mentions"]),
            "duplicate original P0b span")
    embedded, root, missing = [], [], []
    for event in events:
        idx = event["sentence_index"]
        event_by_sentence[idx].append(event)
        sentence = sentences[idx]
        rows = {row["i"]: row for row in sentence["dependency_rows"]}
        pred = event["predicate"]
        raw = rows[pred["i"]]
        require(raw["idx"] == pred["start_char"] and
                raw["text"] == pred["surface"] and
                raw["dep"] == pred["dep"], "forged event predicate")
        if raw["dep"] == "conj":
            parent = rows[raw["head_i"]]
            witness = {
                "sentence_index": idx, "predicate": raw["text"],
                "predicate_start": raw["idx"], "parent": parent["text"],
                "parent_dep": parent["dep"], "flat_scope": event["scope"],
                "original_sentence": article[
                    sentence["source_span_start"]:sentence["source_span_end"]],
            }
            if parent["dep"] in EMBED:
                embedded.append(witness)
            if parent["dep"] == "ROOT":
                root.append(witness)
        for role in ("actors", "patients"):
            for item in event[role]:
                if (item["start_char"], item["end_char"]) not in mention_spans:
                    missing.append({
                        "sentence_index": idx, "predicate": pred["surface"],
                        "role": role, "surface": item["surface"], "dep": item["dep"],
                        "span": [item["start_char"], item["end_char"]]})
    pair = next(((a, b) for a in embedded for b in root
                 if a["flat_scope"] == b["flat_scope"]), None)
    require(pair is not None, "no verified scope-observer collision")
    years = proj["timeline_candidates"]
    histogram = collections.Counter()
    year_examples = []
    for year in years:
        sentence = sentences[year["sentence_index"]]
        row = next(r for r in sentence["dependency_rows"]
                   if r["i"] == year["parser_token_i"])
        require(row["idx"] <= year["start_char"] < year["end_char"] <=
                row["idx"] + len(row["text"]), "year not in original token")
        require(year["candidate_only"] is True and
                year["event_time_paid"] is False and
                year["kind"] == "source-year-mention-not-event-date",
                "year was promoted to an event date")
        n = len(year["co_sentential_event_refs"])
        histogram[n] += 1
        if n > 1 and len(year_examples) < 10:
            year_examples.append({
                "year": year["surface"], "sentence": year["sentence_index"],
                "candidate_predicates": [
                    e["predicate"]["surface"] for e in
                    event_by_sentence[year["sentence_index"]]],
                "source_text": article[
                    sentence["source_span_start"]:sentence["source_span_end"]]})
    licences = collections.defaultdict(list)
    for lic in p0b["licenses"]:
        licences[lic["mention_ref"]].append(lic)
    selected = []
    for surface in ("George Walker Bush", "Laura Welch", "Bush",
                    "He", "he", "1977", "possessed"):
        ms = [m for m in p0b["mentions"] if m["canonical_surface"] == surface]
        kinds = sorted({kind for m in ms for lic in licences[m["mention_ref"]]
                        for kind in lic["expected_candidate_kinds"]})
        selected.append({"surface": surface, "mentions": len(ms),
                         "candidate_types": kinds,
                         "semantic_identity_paid": False})
    # Exact per-mention inspection, not a new identity or attachment producer.
    # Retain the original nomination rows and the source parser context.
    per_mention = []
    selected_surfaces = {x["surface"] for x in selected}
    for m in p0b["mentions"]:
        if m["canonical_surface"] not in selected_surfaces:
            continue
        a, b = m["start_char"], m["end_char"]
        require(0 <= a < b <= len(article), "invalid mention span")
        contexts = []
        for idx, sentence in sentences.items():
            if sentence["source_span_start"] <= a and b <= sentence["source_span_end"]:
                rows = sentence["dependency_rows"]
                overlapping = [t for t in rows
                               if t["idx"] < b and a < t["idx"] + len(t["text"])]
                ids = {t["i"] for t in overlapping}
                heads = {t["head_i"] for t in overlapping}
                contexts.append({
                    "sentence_index": idx,
                    "sentence_text": article[sentence["source_span_start"]:sentence["source_span_end"]],
                    "mention_tokens": overlapping,
                    "adjacent_dependency_rows": [t for t in rows
                        if t["i"] in heads or t["head_i"] in ids],
                    "event_observations": event_by_sentence[idx],
                })
        original = licences[m["mention_ref"]]
        per_mention.append({
            "mention": m, "literal": article[a:b],
            "original_licences": original,
            "candidate_types": sorted({k for lic in original
                                       for k in lic["expected_candidate_kinds"]}),
            "parser_contexts": contexts,
            "reviewed_identity_status": "NOT_IN_ARCHIVE",
        })
    require(len(per_mention) == sum(x["mentions"] for x in selected),
            "selected per-mention census mismatch")
    missing_types = collections.Counter(
        f'{x["role"]}:{x["surface"]}' for x in missing)
    return {
        "schema": "gwb-consumer-observer-evidence-audit-v1",
        "source_revision": slr["revision_ref"], "source_utf8_sha256": digest,
        "source_counts": {"sentences": len(sentences), "events": len(events),
                          "years": len(years), "p0b_mentions": len(p0b["mentions"]),
                          "p0b_licenses": len(p0b["licenses"])},
        "scope_label_observer_collision": {
            "consumer_query": "is_conj_parent_embedded",
            "observer": "flat_scope_label_only",
            "same_observation": pair[0]["flat_scope"] == pair[1]["flat_scope"],
            "different_consumer_answers": True,
            "embedded_witness": pair[0], "root_witness": pair[1]},
        "embedded_parent_conjunctions": len(embedded),
        "embedded_conjunction_flat_assertion_labels":
            sum(x["flat_scope"] == "unresolved-source-assertion"
                for x in embedded),
        "embedded_examples": embedded[:12],
        "unmaterialized_grammatical_role_tokens": len(missing),
        "role_missing_surfaces": dict(sorted(missing_types.items())),
        "role_examples": missing[:12],
        "year_sentence_event_count_histogram":
            {str(k):v for k,v in sorted(histogram.items())},
        "ambiguous_year_examples": year_examples,
        "p0b_candidate_fibre_examples": selected,
        "p0b_selected_individual_fibres": per_mention,
        "p0b_individual_fibre_count": len(per_mention),
        "status": {
            "source_observation": "CHECKED",
            "p0b_candidates": "CANDIDATE_ONLY",
            "reviewed_slr_fibres": "NOT_IN_ARCHIVE",
            "s28_join": "NOT_IN_ARCHIVE",
            "query_relative_closure": "NOT_IN_ARCHIVE",
            "world_occurrence": "NOT_LICENSED"}}

def main():
    p = argparse.ArgumentParser()
    p.add_argument("tar")
    p.add_argument("--output", required=True)
    args = p.parse_args()
    result = check(*load(args.tar))
    with open(args.output, "w", encoding="utf-8") as f:
        json.dump(result, f, indent=2, sort_keys=True, ensure_ascii=False)
        f.write("\n")
    print("GWB_SEMANTIC_OBSERVER_AUDIT_PASS",
          "embedded=", result["embedded_parent_conjunctions"],
          "unmaterialized_roles=",
          result["unmaterialized_grammatical_role_tokens"])

if __name__ == "__main__":
    main()
