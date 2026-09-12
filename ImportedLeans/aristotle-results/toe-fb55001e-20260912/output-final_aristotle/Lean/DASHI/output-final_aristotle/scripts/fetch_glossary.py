#!/usr/bin/env python3
"""Ground every Wikidata term used in this development in Wikidata itself.

The script

1. scans the project sources (`RequestProject/`, `data/`, `docs/`, `examples/`,
   `README.md`) for Wikidata entity identifiers — items `Q…` and properties
   `P…`;
2. asks the Wikidata API (`wbgetentities`) for the English label, the English
   description and the English Wikipedia article of each of them, caching every
   answer under `data/glossary-cache/`;
3. writes the result to `data/glossary.tsv`, and
4. generates `RequestProject/Generated/Glossary.lean`, the machine-checked
   glossary table.

Usage:

    python3 scripts/fetch_glossary.py            # fetch what is missing
    python3 scripts/fetch_glossary.py --offline  # cache only, no network
    python3 scripts/fetch_glossary.py --refresh  # re-download everything
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
CACHE = os.path.join(ROOT, "data", "glossary-cache")
TSV = os.path.join(ROOT, "data", "glossary.tsv")
LEAN = os.path.join(ROOT, "RequestProject", "Generated", "Glossary.lean")

SCAN_DIRS = ["RequestProject", "data", "docs", "examples", "scripts"]
SCAN_FILES = ["README.md"]
SKIP_DIRS = {"__pycache__", ".lake", "glossary-cache"}
SKIP_FILES = {"glossary.tsv", "Glossary.lean", "GLOSSARY.md"}
SCAN_EXT = {".lean", ".wdkb", ".skb", ".md", ".sh", ".json", ".py"}

ID_RE = re.compile(r"\b([QP][1-9][0-9]{0,9})\b")

# Identifiers invented for the hand-written illustrations of the library —
# `Q1`, `Q2`, … are the members of the toy families of `Kinship.lean`, the toy
# classes of `Diagnostics.lean` and so on, and `Q999999` is the deliberately
# dangling identifier of the duplicate-detection example.  They are *not*
# references to the Wikidata entities of the same name, so they are left out of
# the glossary.
PLACEHOLDERS = {"Q1", "Q2", "Q3", "Q4", "Q6", "Q7", "Q8", "Q9", "Q999999"}

API = "https://www.wikidata.org/w/api.php"
UA = "wikidata-lean-formalisation/1.0 (glossary grounding script)"


# --------------------------------------------------------------------------
# 1. collect the identifiers used in the project


def scan_ids() -> dict[str, list[str]]:
    """Every entity id occurring in the project, with the files it occurs in."""
    found: dict[str, set[str]] = {}
    paths: list[str] = [os.path.join(ROOT, f) for f in SCAN_FILES]
    for d in SCAN_DIRS:
        for dirpath, dirnames, filenames in os.walk(os.path.join(ROOT, d)):
            dirnames[:] = [x for x in dirnames if x not in SKIP_DIRS]
            for fn in filenames:
                if fn in SKIP_FILES:
                    continue
                if os.path.splitext(fn)[1] in SCAN_EXT:
                    paths.append(os.path.join(dirpath, fn))
    for p in paths:
        try:
            text = open(p, encoding="utf-8").read()
        except (OSError, UnicodeDecodeError):
            continue
        rel = os.path.relpath(p, ROOT)
        for m in ID_RE.finditer(text):
            found.setdefault(m.group(1), set()).add(rel)
    return {k: sorted(v) for k, v in found.items()}


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
        "props": "labels|descriptions|sitelinks",
        # `mul` is Wikidata's language-independent label, used for names that are
        # the same in every language (`Douglas Adams`, `Homo sapiens`, …).
        "languages": "en|mul",
        "sitefilter": "enwiki",
        "format": "json",
    }
    url = API + "?" + urllib.parse.urlencode(params)
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=60) as resp:
        return json.loads(resp.read().decode("utf-8"))


def summarise(eid: str, ent: dict) -> dict:
    """The part of an entity that the glossary records.

    The entry is keyed by the identifier *we* use, `eid`; `canonical` is the
    identifier Wikidata answers with, which differs exactly when `eid` is a
    redirect to another entity.
    """
    if ent.get("missing") is not None or "id" not in ent:
        return {"id": eid, "missing": True}
    labels = ent.get("labels", {})
    label = labels.get("en", {}).get("value", "") or labels.get("mul", {}).get("value", "")
    desc = ent.get("descriptions", {}).get("en", {}).get("value", "")
    link = ent.get("sitelinks", {}).get("enwiki", {})
    article = link.get("title", "")
    return {
        "id": eid,
        "canonical": ent["id"],
        "kind": "property" if eid.startswith("P") else "item",
        "label": label,
        "description": desc,
        "article": article,
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
        time.sleep(1.5)
    return out


# --------------------------------------------------------------------------
# 3/4. write the table and the Lean module


def lean_string(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def write_tsv(rows: list[dict]) -> None:
    with open(TSV, "w", encoding="utf-8") as fh:
        fh.write("id\tcanonical\tkind\tlabel\tdescription\tenwiki\n")
        for r in rows:
            fh.write(
                "\t".join(
                    [
                        r["id"],
                        r["canonical"],
                        r["kind"],
                        r["label"].replace("\t", " "),
                        r["description"].replace("\t", " "),
                        r["article"].replace("\t", " "),
                    ]
                )
                + "\n"
            )


def write_lean(rows: list[dict], usage: dict[str, list[str]]) -> None:
    props = [r for r in rows if r["kind"] == "property"]
    items = [r for r in rows if r["kind"] == "item"]
    withart = [r for r in rows if r["article"]]
    redirects = [r for r in rows if r["canonical"] != r["id"]]
    lines: list[str] = []
    w = lines.append
    w("/-")
    w("  RequestProject.Generated.Glossary")
    w("")
    w("  Machine-generated by `scripts/fetch_glossary.py` from the live Wikidata API.")
    w("  Do not edit by hand: re-run the script instead.")
    w("")
    w(f"  {len(rows)} entities ({len(props)} properties, {len(items)} items);")
    w(f"  {len(withart)} of them have an English Wikipedia article,")
    w("  and {} of the identifiers {} a redirect.".format(len(redirects), "is" if len(redirects) == 1 else "are"))
    w("-/")
    w("import RequestProject.Grounding")
    w("")
    w("set_option maxRecDepth 100000")
    w("")
    w("namespace Wikidata")
    w("namespace Generated")
    w("")
    w("open Wikidata")
    w("")
    w("/-- Every Wikidata entity named anywhere in this development, with the label,")
    w("description and English Wikipedia article Wikidata gives it. -/")
    w("def glossary : Glossary := ⟨[")
    body = []
    for r in rows:
        body.append(
            "  ⟨{}, {}, {}, {}, {}⟩".format(
                lean_string(r["id"]),
                lean_string(r["label"]),
                lean_string(r["description"]),
                lean_string(r["article"]),
                lean_string(r["canonical"]),
            )
        )
    w(",\n".join(body))
    w("]⟩")
    w("")
    w("end Generated")
    w("end Wikidata")
    w("")
    with open(LEAN, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines))


def write_markdown(rows: list[dict], usage: dict[str, list[str]]) -> None:
    props = [r for r in rows if r["kind"] == "property"]
    items = [r for r in rows if r["kind"] == "item"]
    withart = [r for r in rows if r["article"]]
    out = [
        "# The glossary: every Wikidata term of this development",
        "",
        "Every Wikidata identifier that occurs anywhere in this project — in the Lean",
        "sources, in the downloaded corpus under `data/`, in the generated modules and",
        "in the documentation — looked up in Wikidata itself.  For each one the table",
        "gives the English label, the English description and the English Wikipedia",
        "article, all as Wikidata records them.",
        "",
        f"There are **{len(rows)}** of them: {len(props)} properties and {len(items)} items,",
        f"{len(withart)} with an English Wikipedia article.",
        "",
        "The table is downloaded by `scripts/fetch_glossary.py`, which also writes",
        "`data/glossary.tsv` and the Lean module `RequestProject/Generated/Glossary.lean`.",
        "The Lean side re-checks it: `RequestProject/Grounded.lean` proves that the table",
        "is well formed, that it covers every item of every downloaded fragment, and that",
        "every notion the formalisation defines is grounded in one of these entities.",
        "",
        "A few labels come from Wikidata's language-independent `mul` label rather than",
        "its English one, and an identifier written `Qa → Qb` is a redirect to `Qb`.",
        "",
        "Identifiers invented for the hand-written illustrations of the library (`Q1`,",
        "`Q2`, `Q3`, `Q4`, `Q6`, `Q7`, `Q8`, `Q9` and `Q999999`) are *not* references to",
        "Wikidata and are deliberately absent.",
        "",
        "## Properties",
        "",
        "| id | label | description | article |",
        "|---|---|---|---|",
    ]

    def row(r: dict) -> str:
        base = (
            "https://www.wikidata.org/wiki/Property:"
            if r["kind"] == "property"
            else "https://www.wikidata.org/wiki/"
        )
        art = (
            "[{}](https://en.wikipedia.org/wiki/{})".format(
                r["article"], urllib.parse.quote(r["article"].replace(" ", "_"))
            )
            if r["article"]
            else ""
        )
        def esc(s: str) -> str:
            return s.replace("|", "\\|")

        name = r["id"] if r["canonical"] == r["id"] else f"{r['id']} → {r['canonical']}"
        return "| [{}]({}) | {} | {} | {} |".format(
            name, base + r["id"], esc(r["label"]), esc(r["description"]), esc(art)
        )

    for r in props:
        out.append(row(r))
    out += ["", "## Items", "", "| id | label | description | article |", "|---|---|---|---|"]
    for r in items:
        out.append(row(r))
    out.append("")
    with open(os.path.join(ROOT, "docs", "GLOSSARY.md"), "w", encoding="utf-8") as fh:
        fh.write("\n".join(out))


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--offline", action="store_true")
    ap.add_argument("--refresh", action="store_true")
    ap.add_argument("--no-lean", action="store_true")
    ap.add_argument(
        "--check",
        action="store_true",
        help="only report whether every identifier used in the project is in "
        "data/glossary.tsv; write nothing, and exit 1 if one is missing",
    )
    args = ap.parse_args()

    usage = scan_ids()
    ids = sorted((i for i in usage if i not in PLACEHOLDERS), key=sort_key)
    print(f"{len(ids)} identifiers used in the project", file=sys.stderr)

    if args.check:
        have = {l.split("\t", 1)[0] for l in open(TSV, encoding="utf-8")}
        gaps = [i for i in ids if i not in have]
        for i in gaps:
            print(f"not grounded: {i}  (used in {', '.join(usage[i])})")
        print(f"{len(ids) - len(gaps)}/{len(ids)} identifiers grounded", file=sys.stderr)
        raise SystemExit(1 if gaps else 0)
    entries = fetch(ids, args.offline, args.refresh)

    rows = []
    missing = []
    for eid in ids:
        e = entries.get(eid)
        if e is None or e.get("missing"):
            missing.append(eid)
            continue
        rows.append(e)
    if missing:
        print(f"not on Wikidata (skipped): {' '.join(missing)}", file=sys.stderr)
    write_tsv(rows)
    write_markdown(rows, usage)
    if not args.no_lean:
        write_lean(rows, usage)
    print(f"wrote {len(rows)} entries to data/glossary.tsv", file=sys.stderr)


if __name__ == "__main__":
    main()
