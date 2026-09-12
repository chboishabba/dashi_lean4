# Wikidata facts, compiled to Lean

`wikidata lean` turns a downloaded knowledge base into an ordinary Lean module:
the statements as a `Wikidata.KB` literal, everything they entail as an explicit
list, and theorems connecting the two.  Nothing in a generated module is trusted
— Lean re-checks all of it on every build.

Rebuild the whole corpus with

```
scripts/refresh-corpus.sh              # query Wikidata, import, merge, compile, check
scripts/refresh-corpus.sh --offline    # the same from the download cache
```

## The fragments

Each fragment was obtained by `wikidata fetch` from the seeds listed below,
following `instance of` / `subclass of` links one or two further steps, and stored in
`data/*.wdkb`.  Data downloaded 16 August 2026; the frontier, vocabulary and
related fragments 17 August 2026; `Frontier3`, `Frontier4`, `RelatedStructures2`
and `KnowledgeRepresentation` 18 August 2026; `Theories` and `Enriched` with the
enrichment run of [`ENRICHMENT.md`](ENRICHMENT.md).

| module (`RequestProject/Generated/`) | seeds | items | P279 / P31 | entailed `⊑` | entailed `:` | checked by |
|---|---|---|---|---|---|---|
| `DouglasAdams` | Q42 | 21 | 12 / 9 | 19 | 22 | kernel (`decide`) |
| `UpperOntology` | Q35120 entity, Q16889133 class, Q19478619 metaclass, … | 44 | 50 / 44 | 135 | 225 | kernel (`decide`) |
| `Geography` | Q515 city, Q6256 country, Q64 Berlin, Q90 Paris, Q30 USA, … | 178 | 203 / 130 | 1618 | 594 | compiled (`native_decide`) |
| `CreativeWorks` | Q11424 film, Q571 book, Q25169 The Hitchhiker's Guide…, … | 94 | 93 / 60 | 273 | 200 | compiled |
| `Science` | Q937 Einstein, Q1035 Darwin, Q7259 Lovelace, Q901 scientist, … | 104 | 82 / 65 | 211 | 226 | compiled |
| `Technology` | Q7397 software, Q68 computer, Q9143 programming language, Q28865 Python, Q11660 AI, … | 132 | 137 / 118 | 424 | 404 | compiled |
| `Mathematics` | Q395 mathematics, Q65943 theorem, Q11348 pi, Q12503 axiom, … | 84 | 77 / 49 | 180 | 169 | compiled |
| `LifeSciences` | Q7239 organism, Q16521 taxon, Q729 animal, Q756 plant, Q7187 gene, Q8054 protein | 86 | 85 / 77 | 225 | 252 | compiled |
| `Society` | Q43229 organization, Q4830453 business, Q3918 university, Q7278 political party, … | 92 | 102 / 91 | 319 | 389 | compiled |
| `Chemistry` | Q11344 chemical element, Q11173 chemical compound, Q12136 disease, Q8386 drug, … | 62 | 59 / 40 | 153 | 125 | compiled |
| `Events` | Q1190554 occurrence, Q1656682 event, Q198 war, Q13418847 historical event, … | 82 | 76 / 55 | 195 | 149 | compiled |
| `Core` | the eleven fragments above, merged and deduplicated | 588 | 725 / 477 | 4511 | 3148 | compiled |
| `Structures` | Q1397439 pullback, Q2141963 retract, Q208237 monoid, Q1425985 preorder, Q357858 adjoint functor, … | 163 | 166 / 66 | 502 | 245 | compiled |
| `Frontier` | the 144 items of `Core` that had no P31/P279 statement of their own | 477 | 536 / 317 | 1843 | 1267 | compiled |
| `Frontier2` | the 70 items of the extended corpus that had no P31/P279 statement of their own | 328 | 318 / 201 | 883 | 669 | compiled |
| `VocabularyCorpus` | the 77 notions named in `Vocabulary.lean` that no earlier download covered | 571 | 642 / 337 | 3096 | 1948 | compiled |
| `RelatedStructures` | Q595298 sheaf, Q7241077 presheaf, Q1442189 natural transformation, Q1148924 Kolmogorov space, Q202906 homeomorphism, … | 145 | 146 / 35 | 427 | 85 | compiled |
| `Frontier3` | the 42 items of the corpus of round two that had no P31/P279 statement of their own | 204 | 172 / 91 | 375 | 216 | compiled |
| `Frontier4` | the 18 items of the corpus of round three that had no P31/P279 statement of their own | 95 | 69 / 32 | 121 | 50 | compiled |
| `RelatedStructures2` | Q2143621 topos, Q1725874 cartesian closed category, Q1224487 equaliser, Q5140810 coequalizer, Q1633079 pushout, Q692689 coproduct, Q1575634 concrete category, … | 63 | 53 / 34 | 190 | 89 | compiled |
| `KnowledgeRepresentation` | Q826165 OWL, Q1751819 RDF Schema, Q2288360 SKOS, Q54871 SPARQL, Q387196 description logic, Q3929429 semantic reasoner, Q1045785 semantic network, … | 150 | 142 / 77 | 477 | 327 | compiled |
| `Theories` | Q217413 category theory, Q42989 topology, Q1062242 Grothendieck topology, Q5891840 homotopy type theory, Q139761564 cubical type theory, Q874429 group theory, Q903820 field theory | 191 | 212 / 67 | 923 | 284 | compiled |
| `Enriched` | the theory corpus, grown by the enrichment loop: the eighty most referenced items its sources named and it did not have | 553 | 339 / 165 | 1944 | 1547 | compiled |

The fragments after `Core` are of a different kind: their seeds are the
mathematical articles of Wikidata that name the notions **this development is
itself made of**, and the items the corpus had mentioned without ever asking
about them.  `RequestProject/Vocabulary.lean` matches each of them with the
construction of the library that instantiates it, and
`RequestProject/MathResonance.lean` proves the match in Mathlib's vocabulary
(see [`MATH.md`](MATH.md)).  Because it is about the notions rather than about a
domain, `Structures` is compiled on its own and is not merged into `Core`; so are
`VocabularyCorpus`, `RelatedStructures` and `RelatedStructures2`, which continue
it, `KnowledgeRepresentation`, which is about knowledge representation itself,
the four `Frontier` fragments, which are about the corpus, and `Theories` with
`Enriched`, which are about the seven theories that meet the pullback
([`THEORIES.md`](THEORIES.md)) and about what the enrichment loop
([`ENRICHMENT.md`](ENRICHMENT.md)) added to them.

`data/all.wdkb` is the union of every fragment above — 1578 items, 2257
`subclass of` and 1169 `instance of` statements.  It is the base the defect
report (`RequestProject/DefectReport.lean`), the term table
(`RequestProject/KbTerms.lean`) and the periodicity search
(`RequestProject/PeriodicityReport.lean`) run over.

## The frontier: what a crawl of bounded depth misses

The eleven downloads followed links **two steps** from their seeds, so the items
reached on the last step were recorded but never asked about themselves.  There
were 144 of them (`Wikidata.Corpus.core_rootless_card`), and asking Wikidata
about those 144 items is `data/frontier.wdkb`.  The result, proved in
`RequestProject/CorpusFrontier.lean` against the compiled data:

* only **one** of the 144 is a genuine root of the hierarchy — `Q16003513`; every
  other one does have a `subclass of` or an `instance of` statement that the
  corpus was simply missing (`Corpus.frontier_leaves_one_root`);
* **131** of them become subclasses of *entity* (Q35120), the top of the Wikidata
  ontology, only once the missing layer is in
  (`Corpus.frontier_gained_entity_card`, with `Corpus.frontier_gained_entity_meaning`
  saying what the count means on the abstract relations);
* the extended corpus — `Corpus.coreExtended`, 749 items — still derives every
  statement of the old corpus and of the new download
  (`Corpus.coreExtended_entails_core`, `Corpus.coreExtended_entails_frontier`);
* and asking the same question of the extended corpus moves the frontier without
  making it vanish, but shrinks it: 144 items with nothing said about them, then
  70, then — after the second round, `data/frontier2.wdkb` — 42
  (`Corpus.coreExtended_rootless_card`, `Corpus.coreExtended2_rootless_card`),
  with `Q16003513` again the only item of the round that turned out to be a
  genuine root.

Two further rounds — `data/frontier3.wdkb` and `data/frontier4.wdkb`, proved in
`RequestProject/CorpusRounds.lean` — continue the loop: the corpora have 588,
749, 847, 889 and 918 items (`Corpus.corpus_sizes`) and the numbers of items they
say nothing about are

**144 → 70 → 42 → 18 → 14**

(`Corpus.frontier_sizes`, `Corpus.frontier_sizes_decreasing`).  In round three
and again in round four, `Q16003513` is the only item asked about that comes back
with no statement of its own (`Corpus.round_three_leaves_one_root`,
`Corpus.round_four_leaves_one_root`, `Corpus.q16003513_still_rootless`), and the
corpus of round four still derives every statement of the original corpus and of
all four downloads (`Corpus.coreExtended4_entails_core`,
`Corpus.coreExtended4_derives_sub`).

## The notions the library names, and the ones next door

`RequestProject/Vocabulary.lean` names a Wikidata entity for every notion the
development defines, but naming is not downloading: of the 160 items the
vocabulary and the new table `Wikidata.relatedNotions` mention, **93** had never
been queried (`Wikidata.Notions.notions_needing_new_downloads_card`).
`data/vocabulary.wdkb` and `data/related.wdkb` close that gap, and
`Wikidata.Notions.notions_all_downloaded` checks that every item either table
names is now declared by a downloaded fragment.  The second of the two also
brings in the structures the later layers of the library needed — sheaf,
presheaf, natural transformation, Kolmogorov space, specialization order,
homeomorphism, monomorphism, epimorphism, initial and terminal object — each
matched with the declaration of the library that realises it.

Two more neighbourhoods were added afterwards, and read in
`RequestProject/RelatedCorpus.lean`.  `data/related2.wdkb` covers the categorical
structures the later layers use and the first batch had missed — equaliser,
coequalizer, pushout, coproduct, colimit, comma category, functor category,
monoidal and cartesian closed category, topos, subobject classifier, concrete
category — so the library can record, from the downloaded statements, that a
topos is a cartesian closed category and hence a monoidal category, that an
equaliser is a limit and a pushout a colimit, and that a sheaf is a presheaf.
`data/knowledge.wdkb` covers the family Wikidata itself belongs to — OWL, RDF
Schema, SKOS, SPARQL, description logic, ontology language, semantic reasoner,
semantic network, controlled vocabulary, thesaurus, class hierarchy, meronymy —
and yields, again from the statements, that OWL is an ontology language, SKOS an
ontology, SPARQL a programming language, a thesaurus a controlled vocabulary, a
semantic network a knowledge graph and a semantic reasoner software.

## What each generated module proves

For a fragment `F`:

* `F.kb_wellFormed` — every statement mentions a declared item, so the certified
  queries of `RequestProject.Engine` apply;
* `F.kb_levelsOk`, `F.kb_acyclic`, `F.kb_disjointOk`, `F.kb_valid` — the verdict
  of the validator on the real data, whatever it is;
* `F.derivedSub`, `F.derivedInst` — the entailed facts, as explicit lists;
* `F.derivedSub_eq`, `F.derivedInst_eq` — those lists are exactly `Cli.subFacts`
  and `Cli.instFacts` of the base;
* `F.derivedSub_sound`, `F.derivedInst_sound` — every listed fact really follows
  from the downloaded statements: a chain of P279 statements, resp. a P31
  statement followed by P279 statements;
* `F.derivedSub_complete`, `F.derivedInst_complete` — and nothing that follows is
  missing from the list;
* a handful of individually named facts, e.g. `sub_Q5_Q215627`, with the labels
  in their doc strings;
* for a fragment that passes the validator, `F.onto : Ontology Qid`, so every
  theorem of `RequestProject.Core` applies to the downloaded data.

The two soundness/completeness theorems are instances of
`Wikidata.Cli.subFacts_sound` / `subFacts_complete` / `instFacts_sound` /
`instFacts_complete`, proved once in `RequestProject/Cli/Codegen.lean`.

## What the real data looks like

The compiled verdicts are the interesting part, because live Wikidata does not
always fit the ontology discipline the WikiProject describes.

* **The Douglas Adams fragment is a genuine ontology.** `DouglasAdams.kb_valid`
  is `true`, so `DouglasAdams.onto` exists and the general theory applies:
  `Compiled.adams_instanceOf_naturalPerson`,
  `Compiled.naturalPerson_not_instanceOf_adams`, `Compiled.level_naturalPerson`.
* **The geography fragment contains a `subclass of` cycle.** Wikidata states both
  `Q82794 region ⊑ Q3622002 geographical area` and
  `Q3622002 geographical area ⊑ Q82794 region`.  Hence
  `Geography.kb_acyclic = false`, and — proved in
  `RequestProject/CompiledFacts.lean` — *no* `Wikidata.Ontology` can have exactly
  these P279 statements (`Compiled.no_ontology_over_geography`), since the class
  hierarchy of an ontology is antisymmetric.
* **Inferred metaclass levels rarely survive contact with the data.** Only the
  smallest fragment satisfies `levelsOk`; the merged corpus reports 988 level
  violations.  Levels are not part of the Wikidata data model, so the tool
  guesses them (`Cli.inferLevels`) and then reports honestly what the validator
  finds.  Nothing about the compiled `subclass of` / `instance of` facts depends
  on levels.
* **Merging fragments really adds knowledge.** The merged corpus entails 1178
  `subclass of` and 1044 `instance of` facts that no single fragment entails;
  `Compiled.core_knows_more_than_adams` proves one such fact together with the
  fact that the smaller base does not derive it.  The cross-domain example is
  `Compiled.adams_organism_needs_both_downloads`: in the corpus Douglas Adams is
  an instance of *organism* (Q7239), by a chain that uses `Q5 human ⊑ Q729
  animal` from the biography download and `Q729 animal ⊑ Q7239 organism` from the
  life-sciences download; neither download derives it alone.
* **And merging loses nothing.** `Corpus.core_entails_fragments` in
  `RequestProject/CorpusEntailment.lean` checks the corpus against each of the
  eleven compiled fragments: every statement of every fragment is still
  derivable after the merge and the deduplication
  (`Corpus.core_derives_fragment_sub`, `Corpus.core_derives_fragment_inst`).

## Cost

Compiled evaluation (`native_decide`) is what makes the larger fragments
practical, and it is why the generated modules for them depend on
`Lean.ofReduceBool` in addition to Lean's standard axioms.  The two small
fragments are checked entirely by the kernel and depend only on `propext`,
`Classical.choice` and `Quot.sound`; `#print axioms` shows this.

Evaluating a base of a few hundred items used to be hopeless because
`KB.isSubclassOf` recomputes the transitive closure on every call.
`RequestProject/FastEval.lean` computes the closure once as a table and proves
every fast check equal to the original (`KB.validFast_eq`, `KB.errorsFast_eq`,
`KB.saturateFast_eq`, …), which is what both the tool and the generator use:
checking the 178-item geography fragment went from about 90 seconds to about one.
