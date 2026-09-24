# The periodicity spectrum: every relation as an operator

[`PERIODICITY.md`](PERIODICITY.md) searched **one** transition system, the
`subclass of` successor map, and found eleven periodic items in four components.
This page widens the search in five directions: longer periods, other relations,
words in several relations, the phase structure of each component, the distance
from the hierarchy to acyclicity, and the terminology graph laid against the
topology.

Everything below is either a theorem about arbitrary knowledge bases
(`RequestProject/RelationWords.lean`) or a fact decided by computation on the
downloaded corpus — 1578 items, 2257 `subclass of` and 1169 `instance of`
statements (`RequestProject/SpectrumReport.lean`,
`RequestProject/FeedbackSets.lean`).

## 1. Longer periods find nothing new

The search `periodOf` reports the **shortest return**, and its bound was 20.
Raising the bound cannot find a new item: any return time whatsoever makes the
item a periodic point, and the periodic points are exactly the eleven items
already listed (`subPeriodOf_isSome_imp`, which needs no computation — it is the
characterisation `KB.mem_periodicItems` of the search). So the histogram of
shortest returns is supported on those eleven at *every* bound, and at bound 100
it is

| shortest return | 2 | 3 | 4 |
|---|---|---|---|
| items | 4 | 3 | 4 |

(`periods_100`, `periodHistogram_100`).

## 2. Every relation as an operator, and words in them

The ontology layer carries two relations, so there are two operators

```
T_279 : x ↦ the direct superclasses of x
T_31  : x ↦ the classes x is a direct instance of
```

and a *word* in them — `T_31·T_279`, `T_279·T_31`, `T_279²`, … — is another
transition system.  `KB.wordStep` computes the operator of a word, and
`KB.mem_wordStep` proves it faithful: it computes exactly the property path
`wordExpr w` of the path layer, so a word really is a composition of steps in
the relation algebra of `RequestProject/Paths.lean`.

`word_spectrum` runs the periodicity search over the fourteen words of length at
most three and counts the items each word returns to itself within six
applications:

| word | items returned |
|---|---|
| `P279` | 11 |
| `P31` | 1 |
| `P279·P31` | 8 |
| `P31·P279` | 9 |
| `P279²` | 11 |
| `P31²` | 1 |
| `P279·P31·P279` | 10 |
| `P31·P279·P31` | 4 |
| `P279²·P31` | 6 |
| `P31·P279²` | 8 |
| `P279·P31²` | 4 |
| `P31²·P279` | 5 |
| `P279³` | 11 |
| `P31³` | 1 |

The interesting rows are the mixed ones.  **The items they find are disjoint
from the eleven that `subclass of` finds** (`mixed_disjoint_from_p279`): these
are cycles that no single-relation search can see.

* Along `instance of` alone exactly one item closes: *variable-order class*
  (Q23958852) is **an instance of itself** (`variableOrderClass_selfInstance`).
* Along `instance of ∘ subclass of` nine items close (`instSub_periodicItems`):
  *Wikidata entity*, *depicting object*, *object*, *artificial object*,
  *concept*, *abstract entity*, *representation*, *class*, *type*.
* Along `subclass of ∘ instance of` eight close (`subInst_periodicItems`):
  *wikibase data model possible value for a claim*, *self-depicting entity*,
  *type of object*, *fundamental Wikidata entity*, *concept*, *variable-order
  class*, *metaclass*, *philosophical concept*.

Two of them, in the statements Wikidata actually makes: *class* (Q16889133) is
an instance of *metaclass* (Q19478619), which is a subclass of *class*; and
*representation* (Q1272626) is an instance of *concept* (Q151885), which is a
subclass of *representation*.

## 3. A mixed cycle is a defect, and a worse one than a subclass cycle

The abstract reason is the metaclass level.  In an ontology a `subclass of` step
keeps the level and an `instance of` step raises it by one, so along a word the
level rises by exactly the number of `instance of` letters it spells
(`Ontology.level_of_eval_wordExpr`).  A closed walk returns to its own level,
hence:

> **In a genuine ontology no word containing an `instance of` letter can close**
> (`Ontology.instCount_eq_zero_of_closed`).

Applied to the corpus (`no_ontology_over_corpus_links`), and — since the repair
of the defect report deletes `subclass of` statements only — also to the
repaired corpus:

> **The four deletions that make the class hierarchy acyclic still leave a
> knowledge base that no abstract ontology models**
> (`no_ontology_over_acyclicCorpus_links`), because *variable-order class* is
> still an instance of itself.

## 4. Component, period, phase

The distinction the search cannot see by itself is between the **shortest
return** it reports and the **fundamental period** of the component, the largest
number dividing *every* return time.

For the four `subclass of` components the two agree, and the phase certificates
of `PERIODICITY.md` prove it: their periods are exactly 2, 4, 3, 2.
`SpectrumReport.region_periodDivisor'` re-derives the *region* case through the
new certificate `KB.subPhaseCertB`, which decides the check with one forward and
one backward reachability computation instead of a closure table
(`Periodicity.isPeriodDivisor_of_phaseCertB` is the general statement, for an
arbitrary transition system).

For the mixed word `instance of ∘ subclass of` they differ sharply.  All nine
of its periodic items lie in one strongly connected component; *Wikidata entity*
has shortest return 3 there, but *representation* is a **fixed point** of the
same component, so the fundamental period is 1
(`entity_instSub_periodDivisor_eq_one`) and no phase of modulus greater than one
can exist for it (`entity_instSub_no_phase`).  The mixed component is cyclic but
not coordinatisable by a finite cyclic phase; the `subclass of` components are
both.

| object | transition system | component | shortest return | fundamental period | phase |
|---|---|---|---|---|---|
| *region* | `P279` | 2 items | 2 | 2 | `ZMod 2` |
| *scientist* | `P279` | 4 items | 4 | 4 | `ZMod 4` |
| *element* | `P279` | 3 items | 3 | 3 | `ZMod 3` |
| *delict* | `P279` | 2 items | 2 | 2 | `ZMod 2` |
| *variable-order class* | `P31` | 1 item | 1 | 1 | trivial |
| *Wikidata entity* | `P31·P279` | 9 items | 3 | 1 | none non-trivial |
| *representation* | `P31·P279` | same component | 1 | 1 | none non-trivial |

## 5. The distance to acyclicity

`RequestProject/FeedbackSets.lean` turns the binary question into a number.  A
*feedback edge set* is a set of `subclass of` statements whose deletion leaves no
periodic point; a *feedback vertex set* does the same by removing items.

* The four statements of the defect report are a feedback edge set
  (`corpus_isFeedbackEdgeSet_cycleBreak`), and **every** feedback edge set has at
  least four statements (`four_le_card_of_isFeedbackEdgeSet`) — the four cycles
  are pairwise disjoint, so no statement can break two of them.  The minimum is
  therefore exactly four (`min_feedbackEdgeSet_card`).
* The same holds item by item: one item from each cycle suffices
  (`corpus_isFeedbackVertexSet_hubs`) and three never do
  (`min_feedbackVertexSet_card`).

The lower bounds need no new computation over the corpus, and the upper bounds
reuse the acyclicity already proved, through the monotonicity lemma
`KB.isPeriodic_of_sub_subset`: deleting statements can only destroy cycles.

## 6. Ambiguous names against structural periodicity

55 of the 1578 items share their English label with another item
(`collidingItems_count`).  Among the eleven items on a `subclass of` cycle,
three do (`periodicItems_colliding`): *region* (Q82794), whose label is carried
by two further items, and the two items labelled *element*.

So the collision rate inside the periodic part of the hierarchy — 3 of 11 — is
about eight times the rate over the corpus as a whole — 55 of 1578 — and two of
the four cycles are duplicated notions visible from the term side as well.  The
*scientist* and *delict* cycles are not: they are ordinary mis-directed
`subclass of` statements between differently named items.
