#!/usr/bin/env python3
"""Read-only regression audit of a flat GWB evidence TAR.

This uses Python's standard library ONLY to validate archived observations.
It is NOT a parser, producer, semantic resolver, licence issuer or authority
source. The production input remains the ORIGINAL SLR Rust/PostgreSQL M12 run.
"""
import argparse
import collections
import hashlib
import json
import tarfile

FIXTURE_SHA256 = "6bbad0f9bcc2f0aa2e0e6f77f15692a945c1331a6337cfe202c19a58e2460f9e"
FIXTURE_SOURCE_REVISION = "enwiki-revid:1385850169"
FIXTURE_SOURCE_SHA256 = "a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233"

FILES = (
    "article.txt", "slr-record.json", "article-candidates.json",
    "gwb_sensiblaw_p0b_mention_licences.json",
)
SUBJECTS = {"nsubj", "csubj", "nsubjpass", "csubjpass", "agent"}
OBJECTS = {"dobj", "obj", "iobj", "pobj", "attr", "oprd", "dative"}
PREDICATES = {"ROOT", "conj", "ccomp", "xcomp", "advcl", "acl", "relcl"}


def sha(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def canonical_json_sha(text):
    # SensibLaw _canonical_digest uses JSON bytes, NOT raw text bytes.
    return hashlib.sha256(json.dumps(text, ensure_ascii=False, sort_keys=True,
                                     separators=(",", ":")).encode("utf-8")).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def load_tar(path):
    with tarfile.open(path, "r:*") as archive:
        names = archive.getnames()
        require(len(names) == len(set(names)), "duplicate TAR members")
        require(all(x in names for x in FILES), "missing required evidence files")
        require(all(m.isfile() and not m.issym() and not m.islnk()
                    for m in archive.getmembers()), "unsafe/non-file archive member")
        def get(name):
            require(name in names, "missing " + name)
            return archive.extractfile(name).read().decode("utf-8")
        return get("article.txt"), *(json.loads(get(x)) for x in FILES[1:])


def validate(text, slr, projection, carrier):
    source_sha = sha(text)
    rev = slr["revision_ref"]
    source_ref = slr["source_unit_ref"]
    parser = slr["parser_receipt"]
    doc = parser["document_ref"]
    require(slr["manifestation"]["source_text_sha256"] == source_sha, "SLR source digest")
    require(projection["source_text_sha256"] == source_sha, "projection source digest")
    require(carrier["canonical_text_sha256"] == canonical_json_sha(text), "P0b JSON-text digest")
    require(len(text) == slr["manifestation"]["character_count"], "source length")
    require(projection["source_revision_ref"] == rev and
            projection["source_unit_ref"] == source_ref, "projection source identity")
    require(carrier["source_ref"] == source_ref and carrier["document_ref"] == doc,
            "P0b source/document identity")
    require(slr["candidate_only"] is True and
            slr["semantic_promotion"] is False and
            carrier["authority"] == "candidate_only" and
            all(carrier[k] == "none" for k in
                ("resolution_effect", "promotion_effect", "execution_effect")),
            "parser or P0b authority promotion")

    sentences = slr["pnf_candidates"]
    require(len(sentences) == parser["sentence_count"] == slr["summary"]["sentences"],
            "sentence count")
    tokens = []
    expected_events = {}
    byref = {}
    for i, sentence in enumerate(sentences):
        start, end = sentence["source_span_start"], sentence["source_span_end"]
        require(0 <= start < end <= len(text), "invalid SLR sentence span")
        require(sha(text[start:end]) == sentence["sentence_text_sha256"],
                "SLR sentence hash mismatch")
        require(sentence["candidate_only"] is True and
                sentence["semantic_promotion"] is False, "sentence authority promotion")
        rows = sentence["dependency_rows"]
        indexed = {r["i"]: r for r in rows}
        require(len(indexed) == len(rows), "duplicate token ordinals")
        byref[sentence["claim_candidate_id"]] = sentence
        for row in rows:
            a = row["idx"]
            b = a + len(row["text"])
            require(start <= a < b <= end and text[a:b] == row["text"],
                    "original token source mismatch")
            require(row["head_i"] in indexed, "missing dependency head")
            tokens.append((a, b, row))
            if row["pos"] == "VERB" and row["dep"] in PREDICATES:
                actor_ids = tuple(r["i"] for r in rows
                                  if r["dep"] in SUBJECTS and r["head_i"] == row["i"])
                patient_ids = tuple(r["i"] for r in rows
                                    if r["dep"] in OBJECTS and r["head_i"] == row["i"])
                negative = any(r["dep"] == "neg" and r["head_i"] == row["i"]
                               for r in rows)
                expected_events[(i, row["i"])] = (a, row["lemma"], actor_ids,
                                                   patient_ids, negative)
    require(len(tokens) == parser["token_count"] == slr["summary"]["tokens"],
            "token count")
    tokens.sort(key=lambda x: x[0])
    require(all(a[1] <= b[0] for a, b in zip(tokens, tokens[1:])),
            "original token overlap")

    events = projection["event_candidates"]
    require(len(events) == len(expected_events), "event candidate cardinality")
    seen = set()
    for ev in events:
        pred = ev["predicate"]
        key = (ev["sentence_index"], pred["i"])
        require(key in expected_events and key not in seen, "event mismatch/duplicate")
        seen.add(key)
        found = (pred["start_char"], pred["lemma"],
                 tuple(x["i"] for x in ev["actors"]),
                 tuple(x["i"] for x in ev["patients"]),
                 ev["negation_dependency_candidate"])
        require(found == expected_events[key], "event predicate/role/scope evidence mismatch")
        require(ev["candidate_only"] is True and
                ev["semantic_licence_paid"] is False and
                ev["world_event_occurrence_paid"] is False,
                "event was promoted")
    require(seen == set(expected_events), "missing original event candidates")
    byevent = {e["event_candidate_ref"]: e for e in events}
    ordered = sorted(events, key=lambda e: (e["predicate"]["start_char"],
                                          e["event_candidate_ref"]))
    expected_order = [
        (a["event_candidate_ref"], b["event_candidate_ref"])
        for a, b in zip(ordered, ordered[1:])
        if a["predicate"]["start_char"] < b["predicate"]["start_char"]
    ]
    actual_order = [(e["before"], e["after"]) for e in projection["text_order_edges"]]
    require(actual_order == expected_order, "textual event order mismatch")
    require(len(byevent) == len(events), "duplicate event candidate reference")

    expected_years = []
    import re
    for m in re.finditer(r"(?<!\d)(?:18|19|20)\d{2}(?!\d)", text):
        coverage = [(a, b, r) for a, b, r in tokens
                    if a <= m.start() < m.end() <= b]
        require(len(coverage) == 1, "year not uniquely backed by original token")
        expected_years.append((m.start(), m.end(), int(m.group())))
    actual_years = [
        (x["start_char"], x["end_char"], x["year_candidate"])
        for x in projection["literal_year_mentions"]
    ]
    require(actual_years == expected_years, "lexical-year evidence mismatch")
    for year in projection["literal_year_mentions"]:
        source = byref[year["slr_claim_candidate_id"]]
        match = [r for r in source["dependency_rows"]
                 if r["i"] == year["parser_token_i"]]
        require(len(match) == 1 and match[0]["idx"] == year["parser_token_start"]
                and match[0]["text"] == year["parser_token_surface"]
                and year["parser_token_end"] ==
                match[0]["idx"] + len(match[0]["text"]),
                "year token provenance mismatch")
        require(year["candidate_only"] is True and year["event_time_paid"] is False,
                "year was promoted to event time")
    require(sorted(actual_years, key=lambda x: (x[2], x[0])) ==
            [(x["start_char"], x["end_char"], x["year_candidate"])
             for x in projection["timeline_candidates"]],
            "timeline index mismatch")
    for row in projection["timeline_candidates"]:
        for ref in row["co_sentential_event_refs"]:
            require(ref in byevent and
                    byevent[ref]["sentence_index"] == row["sentence_index"],
                    "timeline forged event association")
        require(row["kind"] == "source-year-mention-not-event-date",
                "year promoted to chronology")
    proper = projection["proper_noun_tokens"]
    expected_proper = {
        (i, r["i"], r["idx"], r["text"])
        for i, c in enumerate(sentences) for r in c["dependency_rows"]
        if r["pos"] == "PROPN"
    }
    require({(x["sentence_index"], x["i"], x["start_char"], x["surface"])
             for x in proper} == expected_proper and len(proper) == len(expected_proper),
            "PROPN token projection mismatch")
    require(projection["ner_observations_present"] is False and
            not projection["people_mentions"] and not projection["time_mentions"],
            "archived NER availability changed")

    cursor = 0
    for section in projection["sections"]:
        start, end = section["start_char"], section["end_char"]
        require(start == cursor and start < end <= len(text),
                "heading/paragraph source partition mismatch")
        require(section["kind"] in ("heading", "paragraph"),
                "unknown article section kind")
        cursor = end + 2
    require(cursor == len(text) + 2, "article hierarchy fails complete source coverage")

    licenses = carrier["licenses"]
    mentions = carrier["mentions"]
    suppressed = carrier["suppressed_spans"]
    require(len(licenses) == carrier["summary"]["license_count"] and
            len(mentions) == carrier["summary"]["materialized_mention_count"] and
            len(suppressed) == carrier["summary"]["suppressed_span_count"],
            "P0b summary count mismatch")
    require(len({r["license_ref"] for r in licenses}) == len(licenses),
            "duplicate P0b licence")
    mention_refs = {m["mention_ref"] for m in mentions}
    require(len(mention_refs) == len(mentions), "duplicate materialized mention")
    token_boundaries = {x for a, b, _ in tokens for x in (a, b)}
    for m in mentions:
        a, b = m["start_char"], m["end_char"]
        require(m["mention_ref"] == f"mention:{doc}:{a}:{b}" and
                m["document_ref"] == doc and m["source_ref"] == source_ref and
                rev in m["context_refs"] and
                text[a:b] == m["canonical_surface"] and
                a in token_boundaries and b in token_boundaries,
                "P0b mention is not source/token/revision bound")
        lo, hi = m["start_token"], m["end_token"]
        require(0 <= lo < hi <= len(tokens) and tokens[lo][0] == a and
                tokens[hi - 1][1] == b, "P0b token interval mismatch")
    for lic in licenses:
        require(lic["mention_ref"] in mention_refs and
                lic["authority"] == "candidate_only", "orphan/promoted P0b licence")
    for row in suppressed:
        require(0 <= row["start_token"] < row["end_token"] <= len(tokens),
                "invalid suppressed token interval")

    return {
        "schema": "gwb-archived-evidence-regression-v1",
        "source_revision_ref": rev,
        "source_sha256_raw_utf8": source_sha,
        "p0b_canonical_json_text_sha256": carrier["canonical_text_sha256"],
        "source_chars": len(text),
        "sentences": len(sentences),
        "original_parser_tokens": len(tokens),
        "event_candidates": len(events),
        "text_order_edges": len(actual_order),
        "lexical_years": len(actual_years),
        "proper_noun_tokens": len(proper),
        "source_blocks": len(projection["sections"]),
        "p0b_licensed_mentions": len(licenses),
        "p0b_materialized_mentions": len(mentions),
        "p0b_suppressed_spans": len(suppressed),
        "p0b_license_kinds": dict(collections.Counter(x["license_kind"]
                                                       for x in licenses)),
        "source_parser_projection_consistent": True,
        "admitted_semantic_fibre_checked": False,
        "rust_db_native_m12_receipt_present": False,
        "event_occurrence_proved": False,
        "lean_kernel_run": False,
    }


def main():
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument("archive", help="flat gwb_article_proof.tar")
    args.add_argument("--json", action="store_true")
    ns = args.parse_args()
    try:
        with open(ns.archive, "rb") as source_file:
            actual_archive_sha = hashlib.file_digest(source_file, "sha256").hexdigest()
        require(actual_archive_sha == FIXTURE_SHA256,
                "exact GWB archive SHA-256 mismatch; regression requires the supplied fixture")
        report = validate(*load_tar(ns.archive))
        require(report["source_revision_ref"] == FIXTURE_SOURCE_REVISION and
                report["source_sha256_raw_utf8"] == FIXTURE_SOURCE_SHA256,
                "archived GWB source revision/content changed")
        report["archive_sha256"] = actual_archive_sha
    except (ValueError, KeyError, IndexError, TypeError, AssertionError) as exc:
        raise SystemExit("GWB_ARCHIVE_REGRESSION_FAIL: " + str(exc))
    if ns.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print("GWB_ARCHIVE_REGRESSION_PASS "
              f"tokens={report['original_parser_tokens']} "
              f"events={report['event_candidates']} "
              f"years={report['lexical_years']} "
              f"p0b_licences={report['p0b_licensed_mentions']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
