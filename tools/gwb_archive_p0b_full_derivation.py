#!/usr/bin/env python3
"""Independent, READ-ONLY complete P0b derivation check against GWB TAR.

Uses only the original SLR token/POS observations and the documented P0b
rules. Never loads a parser, queries a model or promotes semantic authority.
The archived JSON-string P0b source hash is intentionally labelled LEGACY.
"""
import bisect
import collections
import hashlib
import json
import sys
import tarfile

def utf8_sha(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()

def object_sha(obj):
    data = json.dumps(obj, ensure_ascii=False, sort_keys=True,
                      separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(data).hexdigest()

def require(condition, name):
    if not condition:
        raise ValueError(name)

STRUCTURAL = set("a an and as at by for from in into of on or the to with".split())
PRIORITY = {"named_entity_shape":10, "eventuality_annotation":20,
            "numeric_literal":30, "alias_hint":40, "grammar_phrase":50,
            "pnf_demand":60, "lexical_token":90}

def lexical_kinds(pos):
    if pos == "NUM": return ("literal",)
    if pos == "PROPN": return ("document_local", "instance")
    if pos == "NOUN": return ("class", "instance", "property", "role")
    if pos in ("VERB", "AUX"): return ("event_type", "property")
    return ("class","document_local","event_type","instance","property","role")

def local_types(pos):
    if pos == "PROPN": return ("proper_name", "lexical_span")
    if pos == "NOUN": return ("common_noun", "lexical_span")
    if pos == "NUM": return ("numeric_expression", "lexical_span")
    if pos in ("VERB", "AUX"): return ("linguistic_eventuality", "lexical_span")
    return ("lexical_span",)

def check(path):
    with tarfile.open(path, "r:*") as archive:
        names = archive.getnames()
        require(len(names) == len(set(names)), "duplicate_tar_members")
        def read(name):
            member = archive.getmember(name)
            require(member.isfile(), "unsafe_member")
            return archive.extractfile(member).read().decode("utf-8")
        text = read("article.txt")
        source = json.loads(read("slr-record.json"))
        carrier = json.loads(read("gwb_sensiblaw_p0b_mention_licences.json"))
    source_hash = utf8_sha(text)
    require(source["manifestation"]["source_text_sha256"] == source_hash,
            "source_sha")
    require(carrier["canonical_text_sha256"] == object_sha(text),
            "legacy_json_string_source_sha")
    require(carrier["canonical_text_sha256"] != source_hash,
            "historical_archive_is_not_new_source_hash")
    rows = []
    sentences = []
    for candidate in source["pnf_candidates"]:
        a, b = candidate["source_span_start"], candidate["source_span_end"]
        require(utf8_sha(text[a:b]) == candidate["sentence_text_sha256"],
                "sentence_sha")
        sentence = []
        index = {r["i"] for r in candidate["dependency_rows"]}
        require(len(index) == len(candidate["dependency_rows"]), "duplicate_head_index")
        for r in candidate["dependency_rows"]:
            start, stop = r["idx"], r["idx"] + len(r["text"])
            require(a <= start < stop <= b and
                    text[start:stop] == r["text"] and
                    r["head_i"] in index, "original_parser_token")
            row = (r["text"], start, stop, r["pos"])
            rows.append(row)
            sentence.append(row)
        sentences.append(sentence)
    rows.sort(key=lambda r: (r[1], r[2]))
    n = len(rows)
    require(n == source["parser_receipt"]["token_count"], "parser_token_count")
    require(all(a[2] <= b[1] for a,b in zip(rows,rows[1:])),
            "original_token_order")
    starts = [r[1] for r in rows]
    ends = [r[2] for r in rows]
    exact = {(a,b):(i,i+1) for i,(_,a,b,_) in enumerate(rows)}

    def interval(start, stop):
        if (start,stop) in exact: return exact[start,stop]
        i = bisect.bisect_left(starts, start)
        j = bisect.bisect_right(ends, stop)
        if i >= j or starts[i] < start or ends[j-1] > stop: return None
        return i,j

    proposed = collections.defaultdict(list)
    suppressed = []
    for i,(surface,a,b,pos) in enumerate(rows):
        if not any(c.isalnum() for c in surface):
            suppressed.append({"start_token":i,"end_token":i+1,
                               "suppression_reason":"punctuation_or_symbol"})
            continue
        if surface.strip().lower() in STRUCTURAL:
            suppressed.append({"start_token":i,"end_token":i+1,
                               "suppression_reason":"structural_lexeme"})
            continue
        proposed[a,b].append(("lexical_token",lexical_kinds(pos),local_types(pos)))
    for sentence in sentences:
        group = []
        for _,a,b,pos in sentence:
            if pos == "PROPN":
                group.append((a,b))
            elif group:
                proposed[group[0][0],group[-1][1]].append(
                    ("named_entity_shape",("document_local","instance"),
                     ("proper_name_phrase",)))
                group = []
        if group:
            proposed[group[0][0],group[-1][1]].append(
                ("named_entity_shape",("document_local","instance"),
                 ("proper_name_phrase",)))
    for _,a,b,pos in rows:
        if pos == "NUM":
            proposed[a,b].append(("numeric_literal",("event_type","literal"),
                                  ("numeric_expression",)))
        if pos in ("VERB","AUX"):
            proposed[a,b].append(("eventuality_annotation",
                                  ("event_type","property"),
                                  ("linguistic_eventuality",)))
    normalized = collections.defaultdict(list)
    for (a,b),specs in sorted(proposed.items()):
        bounds = interval(a,b)
        if bounds is not None:
            i,j = bounds
            normalized[rows[i][1],rows[j-1][2]].extend(specs)
    mentions = []
    licences = []
    document = carrier["document_ref"]
    for (a,b),specs in sorted(normalized.items()):
        bounds = interval(a,b)
        if bounds is None: continue
        i,j = bounds
        a,b = rows[i][1],rows[j-1][2]
        specs = sorted(set(specs), key=lambda spec: PRIORITY[spec[0]])
        kind = specs[0][0]
        ref = f"mention:{document}:{a}:{b}"
        m = {"mention_ref":ref,"source_ref":carrier["source_ref"],
             "document_ref":document,"start_char":a,"end_char":b,
             "canonical_surface":text[a:b],"generation_reason":kind,
             "context_refs":[source["revision_ref"]],
             "start_token":i,"end_token":j}
        if kind == "eventuality_annotation":
            m["grammatical_role"] = "eventuality_predicate"
        mentions.append(m)
        for k,(typ,candidate_kinds,local) in enumerate(specs):
            licences.append({
                "license_ref":f"license:{ref}:{typ}:{k}",
                "mention_ref":ref,"license_kind":typ,
                "expected_candidate_kinds":sorted(set(candidate_kinds)),
                "local_type_hypotheses":sorted(set(local)),
                "priority":PRIORITY[typ],"authority":"candidate_only",
            })
    mentions.sort(key=lambda x:x["mention_ref"])
    licences.sort(key=lambda x:x["license_ref"])
    suppressed.sort(key=lambda x:(x["start_token"],x["end_token"],
                                  x["suppression_reason"]))
    require(mentions == carrier["mentions"], "complete_materialized_mentions")
    require(licences == carrier["licenses"], "complete_mention_licences")
    require(suppressed == carrier["suppressed_spans"], "complete_suppressed_spans")
    identity = {key:carrier[key] for key in (
        "schema_version","authority","source_ref","document_ref",
        "canonical_text_sha256","lattice","mentions","licenses",
        "suppressed_spans")}
    require(carrier["carrier_ref"] == "mention-licensing:" + object_sha(identity),
            "complete_carrier_content_address")
    require(carrier["lattice"]["token_count"] == n and
            carrier["lattice"]["recoverable_contiguous_span_count"] ==
            n*(n+1)//2, "P0b_complete_lattice")
    return {
        "verification":"GWB_P0B_FULL_DERIVATION_PASS",
        "source_utf8_sha256":source_hash,
        "legacy_p0b_json_string_sha256":carrier["canonical_text_sha256"],
        "original_tokens":n,
        "complete_mention_matches":len(mentions),
        "complete_licence_matches":len(licences),
        "complete_suppressed_span_matches":len(suppressed),
        "content_address_match":True,
        "native_rust_m12_certified":False,
        "semantic_fibre_closed":False,
        "lean_kernel_verified":False,
    }

if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: gwb_archive_p0b_full_derivation.py gwb_article_proof.tar")
    print(json.dumps(check(sys.argv[1]), indent=2, sort_keys=True))
