"""Hugging Face Space: browse the published Wikidata ontology snapshots.

The Space reads the same JSON Lines files the static site and the archive.org
deposits carry, verifies them against ``manifest.json`` (64-bit FNV-1a over code
points, exactly what the verified tool computed), and answers the two questions
the ontology layer is about: what is this item a subclass of, and what is it an
instance of, following the derived (transitive) relations.
"""
from __future__ import annotations

import glob
import json
import os

import gradio as gr

DATA = os.environ.get("ONTOLOGY_DATA", "data")
MANIFEST = os.environ.get("ONTOLOGY_MANIFEST", "manifest.json")

OFFSET = 0xCBF29CE484222325
PRIME = 0x100000001B3
M64 = (1 << 64) - 1


def fnv1a(text: str) -> str:
    h = OFFSET
    for ch in text:
        h = ((h ^ ord(ch)) * PRIME) & M64
    return f"{h:016x}"


def qid(tokens: list[str]) -> tuple[str, list[str]]:
    """Read one identifier off the front of a record, as `Cli.parseQid?` does."""
    if not tokens:
        return "", []
    head, rest = tokens[0], tokens[1:]
    if head in ("wd", "ont", "lvl"):
        return (rest[0] if head == "wd" else f"{head}:{rest[0]}"), rest[1:]
    if head == "about":
        inner, rest = qid(rest)
        return f"about:{inner}", rest
    return head, rest


class Ontology:
    def __init__(self, name: str) -> None:
        self.name = name
        self.items: list[str] = []
        self.sub: list[tuple[str, str]] = []
        self.inst: list[tuple[str, str]] = []
        self.disj: list[tuple[str, str]] = []

    @classmethod
    def load(cls, path: str) -> "Ontology":
        o = cls(os.path.basename(path).removesuffix(".jsonl"))
        with open(path, encoding="utf-8") as fh:
            for line in fh:
                line = line.rstrip("\n")
                if not line:
                    continue
                row = json.loads(line)
                tag, rest = row[0], row[1:]
                if tag == "name":
                    o.name = rest[0]
                elif tag == "item":
                    o.items.append(qid(rest)[0])
                elif tag in ("sub", "inst", "disj"):
                    a, rest2 = qid(rest)
                    b, _ = qid(rest2)
                    getattr(o, tag).append((a, b))
        return o

    def superclasses(self, q: str) -> list[str]:
        """The reflexive–transitive closure of `subclass of`, from `q`."""
        seen, stack = {q}, [q]
        while stack:
            x = stack.pop()
            for a, b in self.sub:
                if a == x and b not in seen:
                    seen.add(b)
                    stack.append(b)
        return sorted(seen - {q})

    def classes(self, q: str) -> list[str]:
        """`instance of` followed by any number of `subclass of` steps."""
        out: set[str] = set()
        for a, c in self.inst:
            if a == q:
                out.add(c)
                out.update(self.superclasses(c))
        return sorted(out)


def verify() -> str:
    if not os.path.exists(MANIFEST):
        return "no manifest present — the copies below were not checked"
    manifest = json.load(open(MANIFEST, encoding="utf-8"))
    ok = bad = 0
    for entry in manifest["files"]:
        path = entry["path"]
        if not os.path.exists(path):
            continue
        text = open(path, encoding="utf-8").read()
        if len(text) == entry["bytes"] and fnv1a(text) == entry["fnv1a64"]:
            ok += 1
        else:
            bad += 1
    return f"{ok} file(s) match the manifest, {bad} do not"


ONTOLOGIES = {o.name: o for o in (Ontology.load(p) for p in sorted(glob.glob(f"{DATA}/*.jsonl")))}
STATUS = verify()


def lookup(which: str, item: str) -> str:
    o = ONTOLOGIES.get(which)
    if o is None:
        return "no such ontology"
    item = item.strip()
    if not item:
        return "type an item identifier, e.g. Q5"
    sup = o.superclasses(item)
    cls = o.classes(item)
    known = "known item" if item in o.items else "not an item of this ontology"
    return "\n".join(
        [f"**{item}** — {known}", "", "**subclass of (derived):** " + (", ".join(sup) or "—"), "",
         "**instance of (derived):** " + (", ".join(cls) or "—")])


def summary() -> str:
    lines = ["| ontology | items | P279 | P31 | disjoint |", "|---|---:|---:|---:|---:|"]
    for name, o in ONTOLOGIES.items():
        lines.append(f"| {name} | {len(o.items)} | {len(o.sub)} | {len(o.inst)} | {len(o.disj)} |")
    return "\n".join(lines)


with gr.Blocks(title="Wikidata ontology browser") as demo:
    gr.Markdown("# Wikidata ontology, formalised in Lean 4")
    gr.Markdown(
        "The published snapshots of Wikidata's ontology layer. Integrity: " + STATUS + ".")
    gr.Markdown(summary())
    with gr.Row():
        which = gr.Dropdown(sorted(ONTOLOGIES), label="ontology",
                            value=(sorted(ONTOLOGIES)[0] if ONTOLOGIES else None))
        item = gr.Textbox(label="item", placeholder="Q5")
    out = gr.Markdown()
    gr.Button("look up").click(lookup, [which, item], out)
    item.submit(lookup, [which, item], out)

if __name__ == "__main__":
    demo.launch()
