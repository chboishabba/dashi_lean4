#!/usr/bin/env python3
"""Download the Wikidata *terms* of every entity of the downloaded corpus.

In Wikidata's own vocabulary the **terms** of an entity are its labels, its
descriptions and its aliases — the language-dependent names of the entity, as
opposed to its statements.  `scripts/fetch_glossary.py` already downloads the
label and description of every identifier *named anywhere in the project*; this
script is narrower and deeper: it takes exactly the entities of the knowledge
base (`data/all.wdkb`, i.e. the corpus scanned by
`RequestProject/DefectReport.lean`) together with the two properties that carry
its statements, and downloads *all* of their English terms, aliases included.

The script

1. reads the identifiers of `data/all.wdkb`;
2. asks the Wikidata API (`wbgetentities`, `props=labels|descriptions|aliases`)
   for the English (and language-independent `mul`) terms of each of them,
   caching every answer under `data/kb-terms-cache/`;
3. writes `data/kb-terms.tsv`, and
4. generates `RequestProject/Generated/KbTerms.lean`, the term store of the
   corpus as a `Wikidata.TermStore`.

Usage:

    python3 scripts/fetch_kb_terms.py            # fetch what is missing
    python3 scripts/fetch_kb_terms.py --offline  # cache only, no network
    python3 scripts/fetch_kb_terms.py --refresh  # re-download everything
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import time
import urllib.parse
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
KBFILE = os.path.join(ROOT, "data", "all.wdkb")
CACHE = os.path.join(ROOT, "data", "kb-terms-cache")
TSV = os.path.join(ROOT, "data", "kb-terms.tsv")
LEAN = os.path.join(ROOT, "RequestProject", "Generated", "KbTerms.lean")

ID_RE = re.compile(r"^[QP][1-9][0-9]{0,9}$")

# The two properties whose statements make up the corpus.
PROPERTIES = ["P31", "P279"]

API = "https://www.wikidata.org/w/api.php"
UA = "wikidata-lean-formalisation/1.0 (kb term extraction script)"


# --------------------------------------------------------------------------
# 1. the identifiers of the knowledge base


def kb_ids() -> list[str]:
    ids: list[str] = []
    seen: set[str] = set()
    with open(KBFILE, encoding="utf-8") as fh:
        for line in fh:
            parts = line.rstrip("\n").split("\t")
            if not parts:
                continue
            if parts[0] == "item" and len(parts) >= 3 and ID_RE.match(parts[2]):
                q = parts[2]
            elif parts[0] in ("sub", "inst") and len(parts) >= 5:
                for q in (parts[2], parts[4]):
                    if ID_RE.match(q) and q not in seen:
                        seen.add(q)
                        ids.append(q)
                continue
            else:
                continue
            if q not in seen:
                seen.add(q)
                ids.append(q)
    for p in PROPERTIES:
        if p not in seen:
            seen.add(p)
            ids.append(p)
    return sorted(ids, key=sort_key)


def sort_key(eid: str) -> tuple[int, int]:
    return (0 if eid[0] == "P" else 1, int(eid[1:]))


# --------------------------------------------------------------------------
# 2. fetch them from Wikidata


def cache_path(eid: str) -> str:
    return os.path.join(CACHE, eid + ".json")


def load_cached(eid: str):
    try:
        with open(cache_path(eid), encoding="utf-8") as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return None


def store_cached(eid: str, entry) -> None:
    os.makedirs(CACHE, exist_ok=True)
    with open(cache_path(eid), "w", encoding="utf-8") as fh:
        json.dump(entry, fh, ensure_ascii=False, indent=1, sort_keys=True)
        fh.write("\n")


def api_get(ids: list[str]) -> dict:
    params = {
        "action": "wbgetentities",
        "ids": "|".join(ids),
        "props": "labels|descriptions|aliases",
        "languages": "en|mul",
        "format": "json",
    }
    url = API + "?" + urllib.parse.urlencode(params)
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=60) as resp:
        return json.loads(resp.read().decode("utf-8"))


def summarise(eid: str, ent: dict) -> dict:
    """The terms of one entity: label, description and aliases."""
    if ent.get("missing") is not None or "id" not in ent:
        return {"id": eid, "canonical": eid, "label": "", "description": "", "aliases": []}
    labels = ent.get("labels", {})
    label = labels.get("en", {}).get("value", "") or labels.get("mul", {}).get("value", "")
    desc = ent.get("descriptions", {}).get("en", {}).get("value", "")
    al = ent.get("aliases", {})
    aliases: list[str] = []
    for lang in ("en", "mul"):
        for a in al.get(lang, []) or []:
            v = a.get("value", "")
            if v and v != label and v not in aliases:
                aliases.append(v)
    return {
        "id": eid,
        "canonical": ent["id"],
        "label": label,
        "description": desc,
        "aliases": aliases,
    }


def fetch(ids: list[str], offline: bool, refresh: bool) -> dict[str, dict]:
    out: dict[str, dict] = {}
    todo: list[str] = []
    for eid in ids:
        cached = None if refresh else load_cached(eid)
        if cached is not None:
            out[eid] = cached
        else:
            todo.append(eid)
    if todo and offline:
        print(f"offline: {len(todo)} identifiers are not in the cache", file=sys.stderr)
        return out
    for i in range(0, len(todo), 50):
        batch = todo[i : i + 50]
        for attempt in range(8):
            try:
                data = api_get(batch)
                break
            except Exception as exc:  # network hiccup: back off and retry
                print(f"  retry {attempt + 1}: {exc}", file=sys.stderr)
                time.sleep(15 * (attempt + 1))
        else:
            raise SystemExit("could not reach the Wikidata API")
        ents = data.get("entities", {})
        for eid in batch:
            summary = summarise(eid, ents.get(eid, {"missing": True}))
            store_cached(eid, summary)
            out[eid] = summary
        print(f"  fetched {min(i + 50, len(todo))}/{len(todo)}", file=sys.stderr)
        time.sleep(1.0)
    return out


# --------------------------------------------------------------------------
# 3/4. write the table and the Lean module


def lean_string(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def write_tsv(rows: list[dict]) -> None:
    with open(TSV, "w", encoding="utf-8") as fh:
        fh.write("id\tcanonical\tlabel\tdescription\taliases\n")
        for r in rows:
            fh.write(
                "\t".join(
                    [
                        r["id"],
                        r["canonical"],
                        r["label"].replace("\t", " "),
                        r["description"].replace("\t", " "),
                        "|".join(a.replace("\t", " ").replace("|", "/") for a in r["aliases"]),
                    ]
                )
                + "\n"
            )


def terms_literal(r: dict) -> str:
    labels = "[]" if not r["label"] else '[("en", {})]'.format(lean_string(r["label"]))
    descs = "[]" if not r["description"] else '[("en", {})]'.format(lean_string(r["description"]))
    if r["aliases"]:
        aliases = "[" + ", ".join('("en", {})'.format(lean_string(a)) for a in r["aliases"]) + "]"
    else:
        aliases = "[]"
    return "⟨{}, {}, {}⟩".format(labels, descs, aliases)


def write_lean(rows: list[dict]) -> None:
    nlabel = sum(1 for r in rows if r["label"])
    ndesc = sum(1 for r in rows if r["description"])
    nalias = sum(len(r["aliases"]) for r in rows)
    withalias = sum(1 for r in rows if r["aliases"])
    lines: list[str] = []
    w = lines.append
    w("/-")
    w("  RequestProject.Generated.KbTerms")
    w("")
    w("  Machine-generated by `scripts/fetch_kb_terms.py` from the live Wikidata API.")
    w("  Do not edit by hand: re-run the script instead.")
    w("")
    w("  The English terms — label, description and aliases — of every entity of the")
    w("  downloaded corpus `data/all.wdkb`, together with the two properties that")
    w("  carry its statements.")
    w("")
    w(f"  {len(rows)} entities; {nlabel} carry a label and {ndesc} a description;")
    w(f"  {withalias} of them have aliases, {nalias} in total.")
    w("-/")
    w("import RequestProject.Terms")
    w("")
    w("set_option maxRecDepth 1000000")
    w("")
    w("namespace Wikidata")
    w("namespace Generated")
    w("")
    # The table is emitted in chunks: one list literal with 1580 entries
    # overflows the elaborator's stack.
    chunk = 100
    nchunks = (len(rows) + chunk - 1) // chunk
    for c in range(nchunks):
        part = rows[c * chunk : (c + 1) * chunk]
        w(f"/-- Part {c + 1} of the term table of the corpus. -/")
        w(f"def kbTermsPart{c + 1} : List (Qid × Terms) := [")
        w(",\n".join(
            "  ⟨Qid.wd {}, {}⟩".format(lean_string(r["id"]), terms_literal(r)) for r in part))
        w("]")
        w("")
    w("/-- The Wikidata terms of the corpus: for each entity of `data/all.wdkb` its")
    w("English label, its English description and all of its English aliases. -/")
    w("def kbTerms : TermStore :=")
    w("  ⟨" + " ++\n    ".join(f"kbTermsPart{c + 1}" for c in range(nchunks)) + "⟩")
    w("")
    w("end Generated")
    w("end Wikidata")
    w("")
    with open(LEAN, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines))


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--offline", action="store_true")
    ap.add_argument("--refresh", action="store_true")
    args = ap.parse_args()

    ids = kb_ids()
    print(f"{len(ids)} identifiers in {os.path.relpath(KBFILE, ROOT)}", file=sys.stderr)
    entries = fetch(ids, args.offline, args.refresh)
    rows = [entries[i] for i in ids if i in entries]
    write_tsv(rows)
    write_lean(rows)
    nalias = sum(len(r["aliases"]) for r in rows)
    print(
        f"wrote {len(rows)} entities with {nalias} aliases to "
        f"{os.path.relpath(TSV, ROOT)} and {os.path.relpath(LEAN, ROOT)}",
        file=sys.stderr,
    )


if __name__ == "__main__":
    main()
