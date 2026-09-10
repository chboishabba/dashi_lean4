---
title: Wikidata Ontology Browser
emoji: 🧭
colorFrom: blue
colorTo: indigo
sdk: gradio
sdk_version: 4.44.0
app_file: app.py
pinned: false
license: cc0-1.0
---

# Wikidata ontology browser

Browses the [Wikidata ontology dataset](https://huggingface.co/datasets/wikidata-ontology-lean/wikidata-ontology):
the snapshots of Wikidata's `subclass of` / `instance of` layer that the Lean 4
formalisation publishes.

The Space loads the published JSON Lines files, checks each of them against the
digest recorded in `manifest.json` — the same check every other mirror performs —
and lets you look up the superclasses and classes of an item, computed with the
same reflexive–transitive closure the formalisation proves the engine implements.
