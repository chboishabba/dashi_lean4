#!/usr/bin/env python3
"""GWB Wikipedia -> EXISTING SLR spaCy/PNF -> JMD Lean auditable candidates.

Do not infer world occurrence, coreference, event identity, narrative time
or semantic authority from a dependency row, Wikipedia link or year.
JMD verifies these exact source/parser-bound candidate claims separately.

Uses the existing dashi_agda/tools/slr-discourse-reconstruct
slr_source_unit_pnf_batch.py, not a second NLP parser.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
from urllib.parse import urlencode
from urllib.request import Request, urlopen

TITLE = "George_W._Bush"
QID = "Q207"
ARTICLE = "https://en.wikipedia.org/wiki/George_W._Bush"
SCHEMA = "slr-jmd-wikipedia-article-candidates-v1"
SUBJECT_DEPS = {"nsubj", "csubj", "nsubjpass", "csubjpass", "agent"}
OBJECT_DEPS = {"dobj", "obj", "iobj", "pobj", "attr", "oprd", "dative"}
EVENT_DEPS = {"ROOT", "conj", "ccomp", "xcomp", "advcl", "acl", "relcl"}
YEAR = re.compile(r"(?<!\d)(?:18|19|20)\d{2}(?!\d)")


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def fetch_article(revision: str | None) -> tuple[str, str, str]:
    # The parse response contains text and the SAME response's page revision.
    # An oldid is accepted to pin and reproduce an exact prior snapshot.
    params = {"action": "parse", "format": "json", "formatversion": "2",
              "page": TITLE, "prop": "text|revid"}
    if revision is not None:
        params.pop("page")
        params["oldid"] = revision
    url = "https://en.wikipedia.org/w/api.php?" + urlencode(params)
    req = Request(url, headers={
        "User-Agent": "DASHI-SLR-JMD-article-proof/0.1 (research; source-pinned)",
        "Accept": "application/json",
    })
    with urlopen(req, timeout=90) as response:
        raw = json.loads(response.read().decode("utf-8"))
    if "error" in raw:
        raise RuntimeError(f"MediaWiki returned error: {raw['error']}")
    page = raw.get("parse") or {}
    returned_revision = str(page.get("revid") or "")
    html = page.get("text")
    if not returned_revision or not isinstance(html, str):
        raise ValueError("MediaWiki did not return article HTML and revision")
    if revision is not None and returned_revision != revision:
        raise ValueError("MediaWiki changed the requested article revision")
    page_title = str(page.get("title", "")).replace("_", " ")
    if page_title != "George W. Bush":
        raise ValueError(f"unexpected Wikipedia title: {page_title}")
    return returned_revision, html, url


def html_to_source(html: str) -> tuple[str, list[dict]]:
    from bs4 import BeautifulSoup
    soup = BeautifulSoup(html, "html.parser")
    body = soup.select_one(".mw-parser-output") or soup
    for tag in body.select("sup.reference, .mw-editsection, script, style"):
        tag.decompose()
    blocks: list[str] = []
    sections: list[dict] = []
    cursor = 0
    heading = "Lead"
    for tag in body.find_all(["p", "h2", "h3", "h4"]):
        if tag.find_parent(["table", "nav", "aside", "figure", "footer"]):
            continue
        surface = " ".join(tag.get_text(" ", strip=True).split())
        if not surface:
            continue
        if len(surface) > 100_000:
            raise ValueError("unexpected oversized HTML block")
        kind = "heading" if tag.name.startswith("h") else "paragraph"
        if kind == "heading":
            heading = surface
        if blocks:
            cursor += 2
        start = cursor
        cursor += len(surface)
        blocks.append(surface)
        sections.append({"kind": kind, "heading": heading,
                         "start_char": start, "end_char": cursor})
    if not blocks:
        raise ValueError("Wikipedia parse response contained no narrative blocks")
    return "\n\n".join(blocks), sections


def tok_span(row: dict, text: str) -> dict:
    start = int(row["idx"])
    surface = str(row["text"])
    stop = start + len(surface)
    if start < 0 or text[start:stop] != surface:
        raise ValueError(f"parser token escapes source: {row!r}")
    return {
        "i": int(row["i"]), "start_char": start, "end_char": stop,
        "surface": surface, "lemma": str(row.get("lemma", "")),
        "dep": str(row["dep"]), "head_i": int(row["head_i"]),
        "pos": str(row.get("pos", "")),
    }


def derive_projection(record: dict, text: str, sections: list[dict]) -> dict:
    manifestation = record["manifestation"]
    if manifestation.get("source_text_sha256") != digest(text):
        raise ValueError("SLR record is not bound to the exact supplied text")
    if not record.get("candidate_only") or record.get("semantic_promotion"):
        raise ValueError("SLR producer tried to promote a candidate")
    if not record.get("parser_receipt", {}).get("dependency_capable"):
        raise ValueError("SLR record has no trained dependency parser")

    mentions: list[dict] = []
    times: list[dict] = []
    for entity in record.get("named_entities", []):
        start, stop = int(entity["start_char"]), int(entity["end_char"])
        surface = str(entity["surface"])
        label = str(entity["label_ref"])
        if start < 0 or text[start:stop] != surface:
            raise ValueError("SLR NER entity does not match the source")
        if entity.get("candidate_only") is not True or entity.get("semantic_promotion") is not False:
            raise ValueError("promoted named entity")
        coord = {"start_char": start, "end_char": stop,
                 "surface": surface, "label_ref": label}
        if label == "PERSON":
            mentions.append(coord)
        if label in {"DATE", "TIME"}:
            times.append({**coord, "year_candidates": [int(y) for y in YEAR.findall(surface)]})

    events: list[dict] = []
    sentence_dates: dict[int, list[dict]] = {}
    for candidate in record["pnf_candidates"]:
        if candidate.get("candidate_only") is not True or candidate.get("semantic_promotion") is not False:
            raise ValueError("promoted SLR candidate")
        cid = str(candidate["claim_candidate_id"])
        sentence_index = int(candidate["sentence_index"])
        begin, end = int(candidate["source_span_start"]), int(candidate["source_span_end"])
        if begin < 0 or not begin < end <= len(text):
            raise ValueError("invalid sentence span")
        if digest(text[begin:end]) != candidate["sentence_text_sha256"]:
            raise ValueError("SLR sentence digest does not match exact source")
        rows = candidate["dependency_rows"]
        tokens = [tok_span(row, text) for row in rows]
        ordinals = {t["i"] for t in tokens}
        if len(ordinals) != len(tokens) or any(t["head_i"] not in ordinals for t in tokens):
            raise ValueError("missing/duplicate dependency head")
        if any(t["start_char"] < begin or t["end_char"] > end for t in tokens):
            raise ValueError("dependency escaped its sentence")
        dates = [d for d in times if begin <= d["start_char"] and d["end_char"] <= end]
        sentence_dates[sentence_index] = dates
        for verb in tokens:
            if verb["pos"] != "VERB" or verb["dep"] not in EVENT_DEPS:
                continue
            actors = [r for r in tokens
                      if r["dep"] in SUBJECT_DEPS and r["head_i"] == verb["i"]]
            patients = [r for r in tokens
                        if r["dep"] in OBJECT_DEPS and r["head_i"] == verb["i"]]
            cue_negation = any(r["dep"] == "neg" and r["head_i"] == verb["i"]
                               for r in tokens)
            eid = "source-event-candidate:" + digest(
                cid + "|" + str(verb["i"]) + "|" + str(verb["start_char"]))
            events.append({
                "event_candidate_ref": eid,
                "slr_claim_candidate_id": cid,
                "sentence_index": sentence_index,
                "sentence_start": begin, "sentence_end": end,
                "predicate": verb, "actors": actors, "patients": patients,
                "negation_dependency_candidate": cue_negation,
                "scope": "unresolved-embedded-clause" if verb["dep"] in
                         {"ccomp", "xcomp", "advcl", "acl", "relcl"} else
                         "unresolved-source-assertion",
                "co_sentential_time_candidates": dates,
                "candidate_only": True, "semantic_licence_paid": False,
                "world_event_occurrence_paid": False,
            })

    events.sort(key=lambda e: (e["predicate"]["start_char"], e["event_candidate_ref"]))
    textual_order = [
        {"before": a["event_candidate_ref"], "after": b["event_candidate_ref"],
         "before_start": a["predicate"]["start_char"],
         "after_start": b["predicate"]["start_char"],
         "kind": "source-text-order-only"}
        for a, b in zip(events, events[1:])
        if a["predicate"]["start_char"] < b["predicate"]["start_char"]
    ]
    # The timeline is a *dated mention index*. A DATE phrase in the same
    # sentence as an event is only a candidate association, never event-time
    # identity or world-event chronological truth.
    timeline_candidates = []
    for date in times:
        sentence = next((
            c for c in record["pnf_candidates"]
            if int(c["source_span_start"]) <= date["start_char"]
            and date["end_char"] <= int(c["source_span_end"])
        ), None)
        if sentence is None:
            continue
        idx = int(sentence["sentence_index"])
        local_events = [e["event_candidate_ref"] for e in events
                        if e["sentence_index"] == idx]
        for year in date["year_candidates"]:
            timeline_candidates.append({
                "year_candidate": year,
                "surface": date["surface"],
                "start_char": date["start_char"],
                "end_char": date["end_char"],
                "sentence_index": idx,
                "co_sentential_event_refs": local_events,
                "kind": "source-date-mention-not-event-date",
            })
    timeline_candidates.sort(key=lambda row:
                             (row["year_candidate"], row["start_char"]))
    return {
        "schema": SCHEMA,
        "source_unit_ref": record["source_unit_ref"],
        "source_revision_ref": record["revision_ref"],
        "source_text_sha256": digest(text),
        "wikidata_item_qid": QID,
        "article_url": ARTICLE,
        "sections": sections,
        "people_mentions": mentions,
        "event_candidates": events,
        "time_mentions": times,
        "timeline_candidates": timeline_candidates,
        "text_order_edges": textual_order,
        "source_assertion_is_world_truth": False,
        "parser_carries_semantic_licence": False,
        "text_order_is_event_chronology": False,
        "cross_sentence_identity_paid": False,
        "summary": {
            "sentences": len(record["pnf_candidates"]),
            "people_mentions": len(mentions),
            "event_candidates": len(events),
            "time_mentions": len(times),
            "timeline_candidates": len(timeline_candidates),
            "text_order_edges": len(textual_order),
            "missing_actor_candidates": sum(not e["actors"] for e in events),
            "missing_patient_candidates": sum(not e["patients"] for e in events),
        },
    }


def write_summary(path: Path, projection: dict) -> None:
    s = projection["summary"]
    lines = [
        "# George W. Bush Wikipedia: source-bound candidate extraction",
        "",
        f"Article: {ARTICLE}",
        f"Revision: {projection['source_revision_ref']}",
        f"Source SHA-256: {projection['source_text_sha256']}",
        "",
        f"SLR sentences: {s['sentences']}",
        f"PERSON mentions: {s['people_mentions']}",
        f"Event/action candidates: {s['event_candidates']}",
        f"Temporal mentions: {s['time_mentions']}",
        f"Textual-order edges: {s['text_order_edges']}",
        f"Timeline year-index entries (unlicensed event dates): {s['timeline_candidates']}",
        "",
        "These are parser-supported document observations, not proved event occurrences.",
        "Entity identity, event identity, speaker scope and event-time relations remain",
        "explicitly unlicensed unless separately reviewed and proved.",
        "",
        "## First observed person mentions",
        "",
    ]
    lines += [f"- {r['surface']} at [{r['start_char']},{r['end_char']})"
              for r in projection["people_mentions"][:30]]
    lines += ["", "## First action candidates", ""]
    for e in projection["event_candidates"][:40]:
        a = "/".join(r["surface"] for r in e["actors"]) or "?"
        b = "/".join(r["surface"] for r in e["patients"]) or "?"
        lines.append(f"- [{e['predicate']['start_char']}] {a} / {e['predicate']['lemma']} / {b} "
                     f"({e['scope']})")
    lines += ["", "## Candidate timeline (year-ordered DATE phrases; NOT event chronology)", ""]
    for row in projection["timeline_candidates"][:40]:
        lines.append(f"- {row['year_candidate']}: {row['surface']} "
                     f"[{row['start_char']},{row['end_char']}) "
                     f"(co-sentential events: {len(row['co_sentential_event_refs'])})")
    lines += ["", "## First temporal mentions", ""]
    lines += [f"- {r['surface']} at [{r['start_char']},{r['end_char']})"
              for r in projection["time_mentions"][:40]]
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def self_check() -> int:
    # Fully synthetic parser receipt: validates this projection and its
    # negative controls without substituting a fake parser for a live run.
    import copy
    text = "George W. Bush met Laura Bush in 1977."
    def token(i: int, value: str, dep: str, head: int, pos: str):
        return {"i": i, "idx": text.index(value), "text": value,
                "lemma": value.lower(), "dep": dep, "head_i": head,
                "pos": pos, "tag": pos}
    record = {
        "schema": "slr-source-unit-pnf-record-v1",
        "source_unit_ref": "wikipedia:en:George_W._Bush:fixture",
        "revision_ref": "enwiki-revid:fixture",
        "manifestation": {"source_text_sha256": digest(text)},
        "parser_receipt": {"dependency_capable": True},
        "candidate_only": True, "semantic_promotion": False,
        "named_entities": [
            {"surface": "George W. Bush", "start_char": 0, "end_char": 14,
             "label_ref": "PERSON", "candidate_only": True, "semantic_promotion": False},
            {"surface": "1977", "start_char": text.index("1977"),
             "end_char": text.index("1977") + 4, "label_ref": "DATE",
             "candidate_only": True, "semantic_promotion": False}],
        "pnf_candidates": [{
            "claim_candidate_id": "source:fixture:event",
            "sentence_index": 0, "source_span_start": 0,
            "source_span_end": len(text), "sentence_text_sha256": digest(text),
            "candidate_only": True, "semantic_promotion": False,
            "dependency_rows": [
                token(0, "Bush", "nsubj", 1, "PROPN"),
                token(1, "met", "ROOT", 1, "VERB"),
                token(2, "Laura", "dobj", 1, "PROPN")]}],
    }
    count = 0
    result = derive_projection(record, text,
         [{"kind": "paragraph", "heading": "Fixture",
           "start_char": 0, "end_char": len(text)}])
    assert result["summary"]["people_mentions"] == 1; count += 1
    assert result["summary"]["event_candidates"] == 1; count += 1
    assert result["event_candidates"][0]["actors"][0]["surface"] == "Bush"; count += 1
    assert result["event_candidates"][0]["patients"][0]["surface"] == "Laura"; count += 1
    assert result["timeline_candidates"][0]["year_candidate"] == 1977; count += 1
    assert result["timeline_candidates"][0]["kind"] == "source-date-mention-not-event-date"; count += 1
    assert not result["event_candidates"][0]["world_event_occurrence_paid"]; count += 1
    for mutate in ("bad-hash", "bad-head", "bad-span", "promote"):
        bad = copy.deepcopy(record)
        if mutate == "bad-hash":
            bad["manifestation"]["source_text_sha256"] = "0" * 64
        elif mutate == "bad-head":
            bad["pnf_candidates"][0]["dependency_rows"][0]["head_i"] = 55
        elif mutate == "bad-span":
            bad["named_entities"][0]["end_char"] -= 1
        elif mutate == "promote":
            bad["pnf_candidates"][0]["semantic_promotion"] = True
        try:
            derive_projection(bad, text, [])
        except ValueError:
            count += 1
        else:
            raise AssertionError(f"forged SLR evidence accepted: {mutate}")
    print(f"GWB_ARTICLE_PROJECTION_SELF_CHECK passed={count} "
          "original_slr_rows_reused=true semantic_promotion=false")
    return 0


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--agda-root", type=Path)
    p.add_argument("--output-dir", type=Path)
    p.add_argument("--self-check", action="store_true")
    p.add_argument("--revision", help="Wikipedia oldid for exact replay")
    p.add_argument("--source-text", type=Path, help="offline fixture/plain article text")
    p.add_argument("--source-revision", help="required with --source-text")
    p.add_argument("--slr-record", type=Path, help="reuse an already produced SLR source-unit record")
    args = p.parse_args(argv)
    if args.self_check:
        return self_check()
    if args.agda_root is None or args.output_dir is None:
        p.error("--agda-root and --output-dir are required for a live run")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    if args.source_text:
        if not args.source_revision:
            p.error("--source-revision is required with --source-text")
        source = args.source_text.read_text(encoding="utf-8")
        revision = args.source_revision
        origin = "offline-source-file"
        sections = [{"kind": "paragraph", "heading": "Offline fixture",
                     "start_char": 0, "end_char": len(source)}]
    else:
        revision, html, origin = fetch_article(args.revision)
        (args.output_dir / "article.html").write_text(html, encoding="utf-8")
        source, sections = html_to_source(html)
    (args.output_dir / "article.txt").write_text(source, encoding="utf-8")
    source_ref = f"wikipedia:en:{TITLE}:{revision}"
    revision_ref = f"enwiki-revid:{revision}"
    input_path = args.output_dir / "slr-source-units.jsonl"
    input_path.write_text(json.dumps({
        "source_unit_ref": source_ref, "source_kind": "wikipedia-article",
        "source_role": "external-article-observation", "qid": QID,
        "revision_ref": revision_ref, "language": "en",
        "text_path": str((args.output_dir / "article.txt").resolve()),
    }) + "\n", encoding="utf-8")

    if args.slr_record:
        record = json.loads(args.slr_record.read_text(encoding="utf-8"))
    else:
        root = (args.agda_root / "tools/slr-discourse-reconstruct").resolve()
        if not (root / "slr_source_unit_pnf_batch.py").is_file():
            raise FileNotFoundError(f"existing SLR producer missing: {root}")
        sys.path.insert(0, str(root))
        from slr_source_unit_pnf_batch import run_batch
        manifest = args.output_dir / "slr-manifest.jsonl"
        run_batch(input_path, args.output_dir / "slr-candidates", manifest,
                  max_source_units=1)
        manifest_row = json.loads(manifest.read_text(encoding="utf-8").splitlines()[0])
        record = json.loads(Path(manifest_row["record_path"]).read_text(encoding="utf-8"))
    if record.get("source_unit_ref") != source_ref or record.get("revision_ref") != revision_ref:
        raise ValueError("original SLR record does not match the article revision")
    record_path = args.output_dir / "slr-record.json"
    record_path.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n",
                           encoding="utf-8")
    projection = derive_projection(record, source, sections)
    projection["acquisition_url"] = origin
    proj_path = args.output_dir / "article-candidates.json"
    proj_path.write_text(json.dumps(projection, indent=2, sort_keys=True) + "\n",
                         encoding="utf-8")
    write_summary(args.output_dir / "summary.md", projection)
    print(json.dumps({"source_text": str(args.output_dir / "article.txt"),
                      "slr_record": str(record_path), "projection": str(proj_path),
                      "summary": projection["summary"], "revision": revision_ref},
                     sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
