---
license: cc0-1.0
language:
  - en
pretty_name: Wikidata ontology, formalised in Lean 4
tags:
  - wikidata
  - ontology
  - knowledge-graph
  - formal-methods
  - lean4
size_categories:
  - 1K<n<10K
configs:
  - config_name: default
    data_files:
      - split: train
        path: data/*.jsonl
task_categories:
  - other
---

# Wikidata ontology, formalised in Lean 4

Snapshots of Wikidata's ontology layer — `subclass of` (P279), `instance of` (P31),
disjointness declarations and metaclass levels — as checked by a Lean 4
formalisation of the model described by *Wikidata:WikiProject Ontology*.

Every file here is produced by the project's verified command line tool
(`wikidata publish`), and the properties below are theorems, not conventions.

## Files

| file | what it is |
|------|------------|
| `data/NAME.jsonl` | one JSON array of strings per record: the ontology as published |
| `data/NAME.wdkb` | the same ontology in the project's own tab separated format |
| `manifest.json` | every file with its length and 64-bit FNV-1a digest, plus the content address of each ontology |

## Row format

Each line of a `.jsonl` file is a JSON array of strings — the fields of one record:

```json
["name","upper ontology"]
["item","wd","Q5"]
["level","1","wd","Q5"]
["sub","wd","Q5","wd","Q215627"]
["inst","wd","Q42","wd","Q5"]
["disj","wd","Q5","wd","Q16521"]
```

* `name` — the name of the knowledge base (one header row);
* `item` — an item of the ontology, as a token sequence (`wd Q5`, `ont NAME`,
  `about …`, `lvl N`);
* `level` — the metaclass level of an item: `0` for individuals, `1` for classes
  of individuals, `2` for metaclasses, and so on;
* `sub` — a `subclass of` (P279) statement, subject then object;
* `inst` — an `instance of` (P31) statement;
* `disj` — a declared disjointness between two classes.

## What is guaranteed

* **The rows are the ontology.** Reading a published file back returns exactly the
  knowledge base that was published — nothing invented, nothing dropped
  (`Wikidata.Publish.parseJsonl?_jsonlOfKB`).
* **The row count is pinned down.** One header row plus one row per item, per
  declared level and per statement (`Wikidata.Publish.length_kbRecs`).
* **The content address names the ontology.** Two clean bases with the same
  canonical text are equal, so the `cid` in the manifest identifies the data
  (`Wikidata.Publish.eq_of_renderKB_eq`).
* **Mirrors converge.** This dataset, the web site, the IPFS copy and the
  archive.org deposit are replicas; after one round of exchange all replicas agree
  and none has lost anything (`Wikidata.KB.gossip_pairwise_equiv`,
  `Wikidata.KB.gossip_entails_all`).
* **The archive can be read back.** An archive.org deposit re-imports to the base
  it was made from (`Wikidata.Archive.importKB?_bundleOf`), and its manifest is
  honest (`Wikidata.Archive.checkManifest_bundleOf`).

## Loading

```python
from datasets import load_dataset
ds = load_dataset("wikidata-ontology-lean/wikidata-ontology", split="train")
```

or, without the `datasets` library:

```python
import json
rows = [json.loads(l) for l in open("data/upper-ontology.jsonl", encoding="utf-8")]
subclass_of = [(r[2], r[4]) for r in rows if r[0] == "sub"]
```

## Verifying a copy

```bash
python3 scripts/verify_site.py site      # recompute every length and digest
```

## Licence

The data is derived from Wikidata, which is published under CC0 1.0; this dataset
is CC0 1.0 as well.
