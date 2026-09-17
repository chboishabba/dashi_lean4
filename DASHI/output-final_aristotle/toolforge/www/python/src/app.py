"""Wikimedia Toolforge web service for the published Wikidata ontology.

Toolforge runs this with the `python3.11` webservice type:

    toolforge webservice python3.11 start

It serves the *same* files the static mirrors serve — `site/` is copied next to
this file at deploy time — and adds two things a static host cannot:

* `/api/ask/<ontology>/<a>/<b>` — is `a` a subclass of `b`, computed live;
* `/api/verify` — recompute every digest in `manifest.json` on the server, so the
  Toolforge copy can be compared with any other mirror.

The reasoning follows the formalisation: `subclass of` is the reflexive–transitive
closure of the P279 statements, and `instance of` is a P31 statement followed by
any number of P279 steps.
"""
from __future__ import annotations

import json
import os

from flask import Flask, jsonify, send_from_directory

BASE = os.path.dirname(os.path.abspath(__file__))
SITE = os.environ.get("ONTOLOGY_SITE", os.path.join(BASE, "site"))

OFFSET = 0xCBF29CE484222325
PRIME = 0x100000001B3
M64 = (1 << 64) - 1

app = Flask(__name__, static_folder=None)


def fnv1a(text: str) -> str:
    h = OFFSET
    for ch in text:
        h = ((h ^ ord(ch)) * PRIME) & M64
    return f"{h:016x}"


def read_qid(tokens):
    if not tokens:
        return "", []
    head, rest = tokens[0], tokens[1:]
    if head == "wd":
        return rest[0], rest[1:]
    if head in ("ont", "lvl"):
        return f"{head}:{rest[0]}", rest[1:]
    if head == "about":
        inner, rest = read_qid(rest)
        return f"about:{inner}", rest
    return head, rest


def load(slug: str):
    path = os.path.join(SITE, "data", f"{slug}.jsonl")
    sub, inst, items = [], [], []
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            line = line.rstrip("\n")
            if not line:
                continue
            row = json.loads(line)
            tag, rest = row[0], row[1:]
            if tag == "item":
                items.append(read_qid(rest)[0])
            elif tag in ("sub", "inst"):
                a, rest2 = read_qid(rest)
                b, _ = read_qid(rest2)
                (sub if tag == "sub" else inst).append((a, b))
    return items, sub, inst


def supers(sub, q):
    seen, stack = {q}, [q]
    while stack:
        x = stack.pop()
        for a, b in sub:
            if a == x and b not in seen:
                seen.add(b)
                stack.append(b)
    return seen


@app.route("/")
@app.route("/<path:path>")
def static_site(path: str = "index.html"):
    full = os.path.join(SITE, path)
    if os.path.isdir(full):
        path = os.path.join(path, "index.html")
    return send_from_directory(SITE, path)


@app.route("/api/ask/<slug>/subclass/<a>/<b>")
def ask_subclass(slug: str, a: str, b: str):
    _items, sub, _inst = load(slug)
    return jsonify({"ontology": slug, "a": a, "b": b, "subclass_of": b in supers(sub, a)})


@app.route("/api/ask/<slug>/instance/<a>/<c>")
def ask_instance(slug: str, a: str, c: str):
    _items, sub, inst = load(slug)
    answer = any(a == x and c in supers(sub, d) for x, d in inst)
    return jsonify({"ontology": slug, "a": a, "c": c, "instance_of": answer})


@app.route("/api/verify")
def verify():
    manifest = json.load(open(os.path.join(SITE, "manifest.json"), encoding="utf-8"))
    rows = []
    for entry in manifest["files"]:
        path = os.path.join(SITE, entry["path"])
        if not os.path.exists(path):
            rows.append({"path": entry["path"], "ok": False, "why": "missing"})
            continue
        text = open(path, encoding="utf-8").read()
        ok = len(text) == entry["bytes"] and fnv1a(text) == entry["fnv1a64"]
        rows.append({"path": entry["path"], "ok": ok, "fnv1a64": fnv1a(text)})
    return jsonify({"files": rows, "all_ok": all(r["ok"] for r in rows)})


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 8000)))
