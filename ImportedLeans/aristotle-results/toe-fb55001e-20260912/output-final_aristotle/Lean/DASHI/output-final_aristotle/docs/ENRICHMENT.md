# Auto-enrichment: growing the ontology from its own sources

The corpus of this development used to be assembled by hand: pick identifiers,
download them, import, compile.  This page is about the *automatic* version of
that loop and about the first run of it, over the seven theories of
[`docs/THEORIES.md`](THEORIES.md).

The loop has four stages, and each of them is a Lean function whose behaviour is
proved in [`RequestProject/Enrichment.lean`](../RequestProject/Enrichment.lean):

| stage | command | what it does |
| --- | --- | --- |
| pull | `wikidata sitelinks Q…` | the Wikimedia pages about an item, **in every language** |
| scan | `wikidata scan Q… --langs …` | download those articles; reduce each to the items it links to, the properties of its Wikidata item and the sources it cites |
| rank | `wikidata frontier F.scan --base B.wdkb` | what the sources point at and the library does not have — missing terms, unmodelled properties, uncollected sources — each **ranked by how often it is referred to** |
| grow | `wikidata sources F.scan`, `wikidata enrich F.scan --base B.wdkb` | download the most cited sources and scan them too; download the most referenced missing items and turn their statements into statements of the corpus |

Two more commands turn the result into Lean: `wikidata scanlean` compiles a scan
into a module of data, and `wikidata authority` collects the external
identifiers of a set of items into a module of the `IdKB` layer.

## What is guaranteed

Nothing in the loop is trusted; the parts that could go wrong are theorems.

* **The enrichment step invents nothing and loses nothing.**
  `KB.enrich_wellFormed` — every identifier a candidate statement mentions is
  declared, so the certified queries still apply; `KB.enrich_entails` — the
  enriched base entails the base it came from, hence `KB.enrich_isSubclassOf`
  and `KB.enrich_isInstanceOf`: every fact that was derivable stays derivable;
  `KB.enrich_provenance` — every statement of the enriched base is either a
  statement of the old base or carries the address of the source it was read
  from.
* **The rankings say what they claim.**  `Enrichment.mem_termDemand_iff` — a
  term is listed exactly when a scanned source mentions it and the base does not
  have it; `Enrichment.termDemand_sorted` — the list decreases in reference
  count; `Enrichment.termDemand_head_max` — so its head really is *a most
  referenced missing term*.  The same three theorems hold for the properties
  (`mem_predicateDemand_iff`, …) and for the sources (`mem_sourceDemand_iff`, …).
* **The loop makes progress.**  `Enrichment.termDemand_absorb` — after
  absorbing the demanded terms nothing is missing; `Enrichment.sourceDemand_scan`
  — a source that has been scanned is no longer demanded;
  `Enrichment.frontier_isEmpty_iff_closed` — the to-do list is empty exactly when
  the scan points at nothing new; `Enrichment.State.step_entails` — a whole round
  is conservative.
* **The scan survives the disk.**  `Cli.parseScan?_renderScan`: reading back a
  scan the tool has written returns exactly the scan that was written.

## The first run

Seven items — topology (Q42989), Grothendieck topology (Q1062242), homotopy type
theory (Q5891840), cubical type theory (Q139761564), category theory (Q217413),
field theory (Q903820), group theory (Q874429).  Every number below is a theorem
in [`RequestProject/EnrichmentCorpus.lean`](../RequestProject/EnrichmentCorpus.lean),
decided by computation on the downloaded data.

### 1. All the articles, in all the languages

`wikidata sitelinks` pulled **311 sitelinks over 135 sites** — 282 of them
Wikipedia articles, from Afrikaans to Chinese.  The table is compiled into
[`RequestProject/Generated/TheorySitelinks.lean`](../RequestProject/Generated/TheorySitelinks.lean),
where it is checked to be a *partial bijection*: one page per item and site
(`sites_functional`), one item per page (`sites_pageInjective`), hence
`sites_partialBijection`.  The raw table is `data/enrichment/sitelinks.tsv`.

### 2. Scanning: 76 documents

Ten languages were scanned — en, de, fr, es, it, ru, ja, zh, pt, nl — giving
**51 articles**.  Their most cited external sources were then downloaded and
scanned in two further rounds, giving **25 more documents**: authority records
(GND, NDL, BnF, LoC, NKP), reference works (Britannica, the Stanford
Encyclopedia of Philosophy entry on category theory), and mathematical pages
(the HoTT book and the HoTT repository, a *Plus Magazine* feature, the Geometry
Center zoo, O. Viro's topology manual).  Together the scan mentions **4191 items** and cites **1748 sources**
(`sources_length`, `articles_length`, `external_length`, `mentions_length`,
`cites_length`).  It is stored in `data/enrichment/theories.scan` and compiled to
[`RequestProject/Generated/TheorySources.lean`](../RequestProject/Generated/TheorySources.lean).

An external source is scanned differently from an article: its outgoing
addresses are its citations, and its *mentions* are the glossary terms whose
label occurs in its text.  The Stanford Encyclopedia entry alone named 188
glossary terms and cited 19 further sources.

### 3. What is missing, most referenced first

Against the 191-item theory corpus, **1162 mentioned items were missing**.  The
head of the ranking:

| references | item | |
| --- | --- | --- |
| 27 | Q180969 | algebraic geometry |
| 25 | Q3968 | algebra |
| 23 | Q82571 | linear algebra |
| 23 | Q1166618 | mathematical logic |
| 22 | Q12479 | number theory |
| 22 | Q1260632, Q5165061, Q12488383 | content (three senses) |
| 20 | Q12482 | set theory |
| 20 | Q379825 | element |

So **the most referenced missing term is `algebraic geometry` (Q180969)**, named
by 27 of the 76 documents (`termDemand_top`,
`algebraicGeometry_most_referenced`).

The **properties** the sources use and this development had no Lean predicate
for, most used first, were: `Freebase ID` (P646, 50), `Commons category` (P373,
43), `Microsoft Academic ID` (P6366, 43), **`is the study of` (P2578, 37)**, `on
focus list of Wikimedia project` (P5008, 37), `maintained by WikiProject` (P6104,
37), **`topic's main category` (P910, 37)**, `Stack Exchange tag` (P1482, 36),
`Quora topic ID` (P3417, 36), `nLab ID` (P4215, 33).

The **sources** cited but not yet downloaded number 682 after the second round;
the most cited one left is a Cloudflare challenge script (5), then
`katmat.math.uni-bremen.de/acc/acc.pdf` — *Abstract and Concrete Categories* —
and Euler's E053 at 3 each (`sourceDemand_head`).

### 4. Growing: the terms

`wikidata enrich --top 80` downloaded the eighty most referenced missing items
and turned their `subclass of` and `instance of` statements into 225 candidate
statements, each tagged with the `Special:EntityData` address it was read from.
The corpus went from **191 to 553 items** and from 279 to 504 statements
(`items_grew`), it is still well formed (`enriched_wellFormed`), it still entails
everything the old corpus asserted (`enriched_entails_base`), every absorbed term
is now declared (`enriched_covers_top`), and the missing-term count fell from
1162 to 1061 (`missingTerms_counts`).  The result is `data/enriched.wdkb`,
compiled to
[`RequestProject/Generated/Enriched.lean`](../RequestProject/Generated/Enriched.lean).

### 5. Growing: the predicates, one at a time

The ranking asked for two predicates that are not identifiers, and both are now
in [`RequestProject/FieldsOfStudy.lean`](../RequestProject/FieldsOfStudy.lean):

* **`is the study of` (P2578)** with its inverse **`studied by` (P2579)**.  A
  `StudyKB` is an ontology with study statements in either direction — being an
  inverse pair is not an axiom, a P2579 statement *is* a P2578 statement read
  backwards (`StudyKB.asserted_comm`).  Two rules follow the class hierarchy: a
  subfield studies what its field studies (`studies_mono_field`), and a field
  studies every kind of the thing it studies (`studies_mono_object`); the
  relation they generate is decided by `StudyKB.studiesB` (`studiesB_iff`) and is
  closed under both rules (`studies_idem`).  With Wikidata's own statements —
  topology is the study of topological spaces, category theory of categories,
  functors and natural transformations, group theory of groups, field theory of
  fields, and a Grothendieck topology *is studied by* category theory — the
  fragment derives, for instance, that topology studies Alexandrov topologies
  and that category theory studies Grothendieck topologies, while group theory
  does not study functors.
* **`topic's main category` (P910)** with its inverse **`category's main topic`
  (P301)**.  Both directions are functional, which is the partial-bijection
  situation of `RequestProject/Matching.lean`, so a `TopicKB` is a `KeyTable` and
  `TopicKB.mainCategory_eq_some_iff_mainTopic_eq_some` says the two properties
  are mutually inverse; the four theory categories are checked against it.

The rest of the top of the ranking is **external identifiers**, which this
development already models as a class: an identifier property is a column of an
`IdKB` (`RequestProject/ExternalIds.lean`).  `wikidata authority` collects them
from the downloaded entities —
[`RequestProject/Generated/TheoryAuthority.lean`](../RequestProject/Generated/TheoryAuthority.lean),
**153 identifiers over 74 properties** — and checks the two constraints on the
result.  The distinct-values constraint holds: an identifier identifies its item.
The single-value constraint **fails**, and the counterexamples are real: `Stack
Exchange tag` (P1482) records one tag per Stack Exchange site and `Quora topic
ID` (P3417) two topics for group theory, so those properties are not partial
functions (`authority_not_singleValue`).  With them removed the file is a partial
bijection again (`authoritySingle_partialBijection`).

### 6. Where the run stands

The frontier is not empty (`frontier_not_empty`): 1061 items, 90 properties and
hundreds of sources are still out there, and each round of the loop pulls in the
most referenced of them.  That is the point of the ranking — it says which
single addition buys the most.

## Reproducing it

```
scripts/enrich.sh              # download what is not cached, and rebuild everything
scripts/enrich.sh --offline    # rebuild from the caches only
```

The downloads are cached under `.enrich-cache/` (articles, external sources) and
`.wikidata-cache/` (entities); the outputs — `data/enrichment/*.scan`,
`data/enrichment/sitelinks.tsv`, `data/enriched.wdkb` and the four generated
modules — are checked into the repository, so a reader never has to run the
network at all.
