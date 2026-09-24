# The terms of the corpus, and the periodicity search

Two layers were added to the formalisation: the **terms** Wikidata attaches to
the entities of the downloaded knowledge base, and a **periodicity search** over
the class hierarchy of that knowledge base.  Everything below is either a
theorem about arbitrary knowledge bases or a fact decided by computation on the
downloaded data.

## 1. Extracting the terms

In Wikidata's own vocabulary the *terms* of an entity are its labels, its
descriptions and its aliases — the names of the entity, as opposed to its
statements.  `scripts/fetch_kb_terms.py` downloads all of the English terms of
every entity of the corpus:

```
python3 scripts/fetch_kb_terms.py            # fetch what is missing
python3 scripts/fetch_kb_terms.py --offline  # use the cache only
python3 scripts/fetch_kb_terms.py --refresh  # re-download everything
```

It reads the identifiers of `data/all.wdkb` (the 1578 items of the merged
corpus) together with the two properties that carry its statements, `instance
of` (P31) and `subclass of` (P279), asks the Wikidata API for their English
labels, descriptions and aliases, caches every answer under
`data/kb-terms-cache/`, and writes

* `data/kb-terms.tsv` — the readable table, and
* `RequestProject/Generated/KbTerms.lean` — the same table as a
  `Wikidata.TermStore`, the structure the term layer of
  `RequestProject/Terms.lean` is about.

The result is **1580 entities, all of them labelled, 1519 of them described, and
3515 aliases**.

`RequestProject/KbTerms.lean` then re-checks the table in Lean:

| statement | what it says |
|---|---|
| `kbTerms_size`, `kbTerms_desc_count`, `kbTerms_aliases_count` | 1580 entities, 1519 descriptions, 3515 aliases |
| `kbTerms_covers_corpus`, `corpus_item_has_label` | **every item of the corpus has an English label** |
| `kbTerms_uniqueOk_en` | Wikidata's label/description **uniqueness constraint holds** on the whole corpus |
| `byLabelDesc_subsingleton_kbTerms` | hence a label-plus-description search returns at most one item |
| `kbTerms_aliasOk`, `label_notMem_aliases_kbTerms` | no alias repeats the label of its own item |
| `element_byLabel`, `element_byTerm`, `element_byLabelDesc` | labels do **not** identify items: two items are labelled *element*, and one search string matches two more through their aliases |

The uniqueness check of the term layer compares every pair of items, which is
too slow at this size; `TermStoreAux.uniqueOk_of_nodup_pairsOf` proves that it
is enough to collect the (label, description) pairs in one pass and check that
they are pairwise distinct, and that is what is decided on the data.

## 2. The periodicity search

A `subclass of` cycle is a *periodic point* of the class hierarchy: an item that
the hierarchy walks back to after a fixed number of steps.
`RequestProject/Periodicity.lean` develops the search for such points for an
arbitrary finitely branching step function.

* `ReachIn step n x y` — `y` is reached from `x` in **exactly** `n` steps — with
  the computed `iterate step n x` and the theorem `mem_iterate` that the two
  agree, the composition law `ReachIn.add`, and
  `transGen_iff_exists_reachIn`: a positive-length walk is exactly a step of the
  transitive closure.
* `IsReturn step n x` and `IsPeriodic step x`; the return times of a point are
  closed under addition (`IsReturn.add`).
* `periodOf step bound x` — the **search**: the least return time up to a bound.
  It is sound (`periodOf_isReturn`), minimal (`periodOf_min`) and complete up to
  the bound (`periodOf_eq_none_iff`).
* `IsPeriodDivisor step d x` — `d` divides *every* return time of `x`; the
  largest such `d` is the period of the point in the sense of Markov chains.
  **The period belongs to the component, not to the point**: two points that
  reach each other have the same period divisors
  (`isPeriodDivisor_iff_of_connected`), and periodicity transfers likewise
  (`IsPeriodic.transfer`).
* `isPeriodDivisor_of_phase` — a **phase certificate**: if every step inside the
  strongly connected component of `x` advances a `ZMod d`-valued phase by one,
  then `d` divides every return time.  This is the direction the search cannot
  give, since a search only ever exhibits cycles.
* `isReturn_iff_multiple` — a return time `d` that divides all return times
  makes the return times *exactly* the positive multiples of `d`.

On a knowledge base, `KB.periodicItems` runs the search over the whole class
hierarchy in one pass over the closure table, and `KB.mem_periodicItems` proves
it exactly right: in a well-formed base the items it finds are precisely the
periodic points of the `subclass of` graph.  With no self-loops these are
exactly the cyclic items of the defect report
(`KB.mem_periodicItems_iff_mem_cyclicItems`) — the search refines the existing
cycle detection by attaching a period to each item it finds.  `KB.phaseOkB` is
the decidable form of the phase certificate.

A hand-built fragment (`PeriodicityExample`) shows why the two notions of period
differ: an item on a two-step cycle *and* on a three-step cycle has shortest
cycle 2 but is aperiodic, because only 1 divides both.

## 3. The search applied to the downloaded corpus

`RequestProject/PeriodicityReport.lean` runs all of this over the 1578 items and
2257 `subclass of` statements of the corpus.

* **Eleven items are periodic** (`periodicItems_count`), the other 1567 are not
  (`aperiodicItems_count`); they are exactly the items the cycle detection finds
  (`mem_periodicItems_iff`).
* Named from the downloaded terms (`periodicItems_labels`): *geographical area*,
  *academic professional*, *academic*, *region*, *scientist*, *researcher*,
  *delict*, *violation of law*, *element*, *element of set*, *element*.
* Their shortest cycles (`periods`): 2, 4, 4, 2, 4, 4, 2, 2, 3, 3, 3.
* For each of the four components a phase certificate gives the period
  **exactly**, not just an upper bound:

  | component | items | period | statement |
  |---|---|---|---|
  | *region* | Q82794, Q3622002 | 2 | `region_returns` |
  | *scientist* | Q901, Q1650915, Q66666685, Q3400985 | 4 | `scientist_returns` |
  | *element* | Q379825, Q5358816, Q36808958 | 3 | `element_returns` |
  | *delict* | Q1184244, Q1456832 | 2 | `delict_returns` |

  For instance `scientist_returns` says that a `subclass of` walk returns to
  *scientist* after exactly the positive multiples of four steps.
* The four deletions that the defect report proposes leave a hierarchy with **no
  periodic point at all** (`acyclicCorpus_no_periodic`).

The term layer and the periodicity search meet on the *element* component: two
of its three items carry the same label *element*, and a search for the alias
*element of a set* matches two of them — three items for one notion, which is
what a `subclass of` cycle usually turns out to be.
