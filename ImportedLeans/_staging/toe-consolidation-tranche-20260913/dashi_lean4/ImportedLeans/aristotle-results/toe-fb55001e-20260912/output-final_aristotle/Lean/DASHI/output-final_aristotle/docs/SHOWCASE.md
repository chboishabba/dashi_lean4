# Showcase: the ontology and the tools

`showcase.svg` is the poster version of this page; `status.svg` is the shorter
status report.  Both are generated from the sources — see [below](#regenerating-the-images).

Every claim on the poster is a named theorem of the library.  This page lists
them, so nothing on the image has to be taken on trust, and
[`RequestProject/Showcase.lean`](../RequestProject/Showcase.lean) is the same
list in Lean: it `#check`s each result, so the build fails if a name or a
statement quoted here ever changes.

![the showcase poster](showcase.svg)

## 1. The ontology: five hierarchies, kept apart

Wikidata layers several different hierarchies over the same items, and
`Wikidata:WikiProject Ontology` insists they are not the same hierarchy.  Each
one is modelled as a computable layer over a knowledge base, each has an engine
proved to decide exactly the reflexive–transitive closure of the asserted
statements, and each is proved to stay out of the others' way.

| hierarchy | properties | the engine is exact | the order | separation |
|---|---|---|---|---|
| taxonomy | `instance of` P31, `subclass of` P279 | `KB.isSubclassOf_iff`, `KB.isInstanceOf_iff` | `KB.subclass_antisymm`, `KB.isSubclassOf_trans` | `Examples.instanceOf_not_transitive` |
| meronomy | `part of` P361, `has parts of the class` P2670 | `MKB.isPartOfB_iff` | `MKB.isPartOfB_antisymm`, `MKB.properWhole_wf` | `MKB.part_not_subclass`, `MKB.part_not_instance` |
| kinship | `father` P22, `mother` P25, `spouse` P26 | `FKB.descendsFromB_iff` | `FKB.descendsFromB_antisymm`, `FKB.properAncestor_wf` | `FKB.parent_not_subclass`, `FKB.parent_not_instance` |
| series | `follows` P155, `followed by` P156, `part of the series` P179, `series ordinal` P1545 | `SKB.isAfterB_iff` | `SKB.after_antisymm`, `SKB.predecessor_wf` | `SKB.strictlyAfter_asymm` |
| biological taxa | `parent taxon` P171, `taxon rank` P105, `taxon name` P225 | `TKB.isDescendantB_iff` | `TKB.descent_antisymm`, `TKB.parent_wf` | `TKB.parentTaxon_not_taxonomic` |

All names live in the `Wikidata` namespace.

Further headline results, one per hierarchy:

* **Taxonomy.** Instances inherit upwards (`Ontology.instanceOf_trans_subclassOf`),
  metaclass levels drop by exactly one across `instance of` and are constant
  across `subclass of` (`Ontology.level_instanceOf`, `Ontology.level_subclassOf`),
  and `instance of` is not transitive — a decided counterexample
  (`Examples.instanceOf_not_transitive`).
* **Meronomy.** The parts hierarchy is atomistic: every item has a part with no
  proper parts of its own (`MKB.exists_atom_part`).  Two classical mereological
  principles are shown *not* to follow from the Wikidata data model — weak
  supplementation and extensionality of parthood — by valid fragments that
  refute them.
* **Kinship.** With at most one father and one mother recorded, nobody has more
  than two parents (`FKB.card_parents_le_two`); siblinghood is symmetric and
  irreflexive (`FKB.sibling_symm`, `FKB.sibling_irrefl`); relatedness — having a
  common ancestor — is symmetric and reflexive but **not** transitive
  (`FKB.related_not_transitive`).
* **Alternative parenting.** A second, wider layer (`ParentingKB`) tags every parenthood
  statement with a role — biological, gamete donor, surrogate, adoptive, step,
  foster, legal guardian, godparent — and with the Wikidata property that
  carries it (`father` P22, `mother` P25, the gender-neutral `parent` P8810).
  A person may then have any number of parents (`ParentingKB.rainbow_four_parents`,
  `ParentingKB.blended_five_parents`), while *genetic* parenthood is still limited to
  two (`ParentingKB.card_geneticParentsF_le_two`); legal, social and genetic parenthood
  can be pulled apart by adoption (`ParentingKB.adoption_legal_disjoint_genetic`) and by
  surrogacy, where the person who gave birth is not a genetic parent
  (`ParentingKB.surrogacy_birth_not_genetic`).  Ancestry stays well founded
  (`ParentingKB.properAncestor_wf`), both engines are exact (`ParentingKB.descendsFromB_iff`,
  `ParentingKB.geneticDescendsFromB_iff`), and the classical kinship layer embeds into
  the new one, validity and all (`FKB.pValid_toParentingKB`).  The layer has its
  own diagnostic report, sound and complete
  (`ParentingKB.report_eq_nil_iff_pValid`), which reports several parents,
  adoptive parents, surrogates and donors as perfectly fine and keeps
  unsupported step-parenthood as a warning (`ParentingKB.stepWarnings`).
* **Series.** Every item has an origin (`SKB.exists_origin`); walking the chain
  out enumerates exactly the items that come after, each once
  (`SKB.mem_chainFrom_iff`, `SKB.chainFrom_nodup`); consistent `series ordinal`
  values are a purely local check that already rules out cycles.
* **Biological taxa.** Every taxon descends from a root (`TKB.exists_root`);
  ranks that strictly increase along `parent taxon` certify acyclicity
  (`TKB.no_cycle_of_ranks`); one parent per taxon makes a tree with a unique
  root (`TKB.descent_total_of_functional`, `TKB.exists_unique_root`); `taxon
  name` is injective (`TKB.taxon_of_name_unique`).

## 2. The data model around the hierarchies

Statements are more than pairs of items, and the layers below them are
formalised too: metaclass levels, disjointness and disjoint unions (P2738,
P2737), equivalent classes (P1709), statement ranks, qualifiers, some-value and
no-value snaks, references and provenance, terms, sitelinks, external
identifiers, quantities with units, time values with precision, validity
intervals, property paths, property constraints, `properties for this type`
(P1963), entity schemas, lexemes and senses, the RDF export, item merges,
redundant-statement clean-up, conjunctive queries and witnessed diagnostics.
The modules are listed in the "where the results sit" chart of the poster.

## 3. The tools

Each stage of the pipeline is a command of the `wikidata` executable whose
guarantee is a theorem ([`docs/CLI.md`](CLI.md) documents the commands
themselves).

| stage | command | the guarantee | theorem |
|---|---|---|---|
| download | `wikidata fetch` / `import` | a P279/P31 statement is asserted exactly when the source JSON carries that claim, and the result is well formed | `Cli.sub_kbOfEntities_iff`, `Cli.inst_kbOfEntities_iff`, `Cli.kbOfEntities_wellFormed` |
| validate | `wikidata check` | the report is empty exactly when the base is valid, and every issue comes with a witness | `KB.errors_eq_nil_iff_valid`, `KB.mem_cycleIssues_iff` |
| construct facts | `wikidata derive` / `ask` | every reported fact follows, and adding them all changes nothing that is derivable | `KB.newSubL_sound`, `KB.newInstL_sound`, `KB.saturate_isSubclassOf`, `KB.saturate_valid` |
| explain | `wikidata why` | the printed chain really is a derivation, and only checked chains are returned | `KB.checkSubChain_sound`, `KB.subChain?_sound` |
| query | `wikidata query` | the evaluator returns exactly the satisfying bindings | `Query.eval_sound`, `Query.eval_complete`, `Query.evalT_eq_eval` |
| merge | `wikidata merge --dedup` | nothing is lost: every statement of every fragment is still derivable after the merge | `Corpus.core_entails_fragments` |
| tidy | `wikidata normalize`, redundancy pruning | pruning is lossless and keeps the base valid, and strictly shrinks it | `KB.dropSub_isSubclassOf`, `KB.dropSub_valid`, `KB.dropSub_length_lt` |
| store | the `.wdkb` file format | reading back a file the tool wrote returns exactly the base written | `Cli.parseKB?_renderKB` |
| compile | `wikidata lean` | the generated list of facts is exactly the set of entailed facts | `Cli.subFacts_sound`, `Cli.subFacts_complete`, `Cli.instFacts_sound`, `Cli.instFacts_complete` |

## 4. Wikidata itself, compiled to Lean

Twenty-two fragments were queried from the live API, stored in `data/*.wdkb` and
compiled into `RequestProject/Generated/`: eleven domain downloads, the merged
and deduplicated `Core`, four rounds of the frontier of the crawl, the notions
the vocabulary itself names and the structures around them, the vocabulary of
knowledge representation, the seven theories of [`THEORIES.md`](THEORIES.md),
and the corpus the enrichment loop grew out of them.  `data/all.wdkb` merges
them all into one base of 1578 items, 2257 `subclass of` and 1169 `instance of`
statements — the base the defect report, the term table and the periodicity
search run over.  The counts on the poster are read off those files.
[`docs/CORPUS.md`](CORPUS.md) has the full table and what each generated module
proves.  Three findings:

* **A genuine ontology.** The Douglas Adams fragment passes every check, so the
  abstract theory applies to the downloaded data
  (`Compiled.adams_instanceOf_naturalPerson`, `Compiled.level_naturalPerson`).
* **A real cycle in live Wikidata.** Geography states both
  `region ⊑ geographical area` and `geographical area ⊑ region`, so no ontology
  can have exactly those P279 statements (`Compiled.geography_subclass_cycle`,
  `Compiled.no_ontology_over_geography`, and the same for the corpus in
  `Compiled.no_ontology_over_core`).
* **Merging adds knowledge and loses none.** The corpus derives facts no single
  fragment derives (`Compiled.core_knows_more_than_adams`,
  `Compiled.adams_organism_needs_both_downloads`), and every fragment statement
  survives the merge (`Corpus.core_entails_fragments`).

## 5. Every term grounded in Wikidata

* **The glossary.** All 1610 Wikidata entities the development names — 51
  properties and 1559 items, 926 of them with an English Wikipedia article — are
  downloaded from the Wikidata API by `scripts/fetch_glossary.py` into
  `RequestProject/Generated/Glossary.lean` (`docs/GLOSSARY.md` and
  `data/glossary.tsv` are the readable copies).
* **It is a table one can trust.** `Grounded.glossary_wellFormed`: well-shaped
  identifiers, no missing label, no identifier listed twice; hence
  `Grounded.lookup_unique`, each identifier gets exactly one entry.
* **Nothing is unexplained.** `Grounded.corpus_covered`: every item of every one
  of the twenty-two downloaded fragments has an entry.
  `Grounded.handwritten_covered`: so does every item of the hand-built
  ontologies of the library.
* **The notions are grounded too.** `RequestProject/Vocabulary.lean` pairs 174
  declarations of the library with the Wikidata entity each formalises, written
  as name literals so Lean rejects a declaration that does not exist;
  `Grounded.vocabulary_grounded` says each of those entities is in the glossary
  *carrying exactly the label claimed for it*.
* **The mathematics is grounded too.** The last block of the vocabulary matches
  the mathematical articles of Wikidata — `pullback` (Q1397439), `retract`
  (Q2141963), `monoid` (Q208237), `preorder` (Q1425985), `adjoint functor`
  (Q357858), `partition of a set` (Q381060), `quotient set` (Q3966112), … —
  with the constructions of this library that instantiate them, and
  `RequestProject/MathResonance.lean` proves each match in Mathlib's own
  vocabulary (`GaloisConnection`, `IsIdempotentElem`, `Function.fixedPoints`,
  `Submonoid`, `Preorder`, `Setoid.ker`, `Set.PairwiseDisjoint`, …); see
  [`MATH.md`](MATH.md).
* **From the shell.** `wikidata gloss Q64 P279` prints what Wikidata says about
  an identifier, and `wikidata gloss FILE.wdkb` does it for every item of a base.

## 6. The ontology inside the ontology

Wikidata describes itself in its own vocabulary, so the development also
formalises the *operation* that puts an ontology inside itself, and identifies it
with four standard constructions.  [`META.md`](META.md) is the full review;
in brief:

* **Reduction.** Reading an ontology through an injective renaming is a reduct
  that invents nothing (`Ontology.comap`, `Ontology.comap_subclassOf`), and at
  the executable level such a renaming preserves *and reflects* the whole engine
  and validator (`KB.valid_rename_iff`).
* **Retraction.** The meta lift and the reduction form a retraction
  (`KB.metaRetract`), so the meta copy is a conservative extension:
  `KB.metaLift_subclassOf_iff`, `KB.metaLift_instanceOf_iff`,
  `KB.metaLift_isMetaclass_iff`.  Its idempotent has the meta-written knowledge
  bases as fixed points (`KB.metaCore_eq_self_iff`).
* **Pullback.** Ontologies have fibre products with the expected universal
  property (`Ontology.pullback`, `Ontology.pullback.lift`,
  `Ontology.pullback.lift_unique`), and the meta copy *is* one of them:
  `KB.metaLift_isPullback`.
* **Frobenius.** Class extensions push forward and pull back along an alignment,
  with the adjunction and the projection formula
  (`Ontology.Alignment.push_subset_iff`,
  `Ontology.Alignment.projection_formula`, `Ontology.Retract.preimage_extension`);
  and the meta lift behaves like a Frobenius endomorphism — injective, a
  homomorphism for merging and entailment, fixing no non-empty base, and an
  isomorphism onto the meta-written bases (`KB.metaEquiv`).

## 7. The ontology as a mathematical object

The construction that says what it means to align two vocabularies over a third
— the **pullback** of ontologies — is met by seven theories, each its own module
and each grounded in the Wikidata article that names it
([`THEORIES.md`](THEORIES.md) is the full page).

| theory | Wikidata | headline results |
|---|---|---|
| category theory | Q217413 | `Ontology.ontCategory`, `Ontology.isPullback_pbOnt`, `Ontology.instHasPullbacksOnt`, `Ontology.forgetOnt_isPullback` |
| topology | Q42989 | `Ontology.subclassTopology`, `Ontology.continuous_iff_subclass`, `Ontology.isPullback_topCat`, `Ontology.specializes_iff_subclassOf` |
| Grothendieck topology | Q1062242 | `Ontology.surjectivePretopology`, `Ontology.ontologyTopology_pullback_stable`, and labellings as a sheaf: `Ontology.isSheaf_funPresheaf`, `Ontology.funSheaf` |
| homotopy type theory | Q5891840 | `Ontology.pullbackEquivSigma`, `Ontology.fibPbFstEquiv`, `Ontology.pullbackPasteEquiv` |
| cubical type theory | Q139761564 | `Ontology.cubePullbackEquiv`, `Ontology.Iv.deMorgan_meet` |
| group theory | Q874429 | `Ontology.autPerm`, `Ontology.autOverSubgroup`, `Ontology.pbAut`, `Ontology.pbAut_fst` |
| field theory | Q903820 | `Ontology.ExtSpace` over `GF(2)`, `Ontology.chi_symmDiff`, `Ontology.comapLin_pb_comm` |

Beyond the pullback, the shape of the category itself: monomorphisms are exactly
the injections (`Ontology.mono_iff_injective`), the empty ontology is initial
(`Ontology.isInitial_emptyOnt`) and there is **no** terminal one
(`Ontology.not_hasTerminal`), while the disjoint union is a coproduct
(`Ontology.isColimit_sumCofan`, `Ontology.instHasBinaryCoproductsOnt`).
Idempotents split (`Ontology.splitRetract`), so `Ont` is idempotent complete
(`Ontology.isIdempotentComplete_Ont`) and "retract" and "split idempotent" are
the same notion; retracts are stable under base change
(`Ontology.Retract.baseChange`).  Topologically, a retract of ontologies is a
retract of item spaces (`Ontology.Retract.isEmbedding_sec`,
`Ontology.Retract.isQuotientMap_ret`) — but the retraction need not be an open
map (`Ontology.exists_retract_ret_not_isOpenMap`).

## 8. Periodicity: the cycles of the downloaded class hierarchy

A `subclass of` cycle is a defect, so it is worth knowing exactly where they are.
`RequestProject/Periodicity.lean` develops the general theory — bounded
reachability, return times, a computable shortest-period search proved correct
and minimal (`Periodicity.periodOf_min`), periods as a property of a strongly
connected component (`Periodicity.isPeriodDivisor_iff_of_connected`), and phase
certificates that make a component period exact rather than an upper bound
(`Periodicity.isPeriodDivisor_of_phase`, `Periodicity.isReturn_iff_multiple`).

Run over the whole corpus (`PeriodicityReport`), exactly **eleven items are
periodic points** of the class hierarchy and the remaining 1567 are not
(`PeriodicityReport.periodicItems_eq`, with `PeriodicityReport.periodicItems_labels`
for what Wikidata calls them); the shortest cycles have lengths 2, 3 and 4
(`PeriodicityReport.periods`), a phase certificate pins each of the four
components down exactly (`PeriodicityReport.scientist_returns`), and the
repaired hierarchy of the defect report has no periodic point left
(`PeriodicityReport.acyclicCorpus_no_periodic`).

[`SPECTRUM.md`](SPECTRUM.md) widens the search to every relation of the ontology
layer read as an operator: which words close (`SpectrumReport.word_spectrum`),
an item that is an instance of itself
(`SpectrumReport.variableOrderClass_selfInstance`), nine items on a
mixed-relational cycle that no `subclass of` cycle contains
(`SpectrumReport.instSub_periodicItems`, `SpectrumReport.mixed_disjoint_from_p279`),
and how far the hierarchy is from acyclic — four statements, or four items
(`FeedbackSets.min_feedbackEdgeSet_card`, `FeedbackSets.min_feedbackVertexSet_card`).

## 9. The transformations, as an algebra

[`PROGRAM-ALGEBRA.md`](PROGRAM-ALGEBRA.md) reads the transformations of the
ontology layer as programs.  Words in the relations *are* the natural numbers,
by a Gödel numbering (`RelWord.equivNat`, `RelWord.decode_encode`); concatenation
of words is composition of the operators they denote (`KB.wordStep_append`); and
the metaclass level grades them by an integer (`RelWord.degree_append`,
`Ontology.level_add_degree`).  Allowing a letter to be run backwards, as an
inverse property path, makes the grading honest: a forward and a backward
`instance of` step cancel (`sdegree_append`, `Ontology.level_add_sdegree`), a
closed signed walk has degree zero, and so a closing word of non-zero degree
refutes every ontology model of a base — while with inverses *every* statement
closes a loop, which is why the corpus searches use forward words only
(`KB.roundTrip_isReturn`).

On a finite carrier the powers of a relation are eventually periodic
(`RelAlg.exists_eventually_periodic`); the cyclic part of the corpus has order
exactly twelve (`CyclicAlgebra.cyclicRel_order_twelve`), which the Chinese
remainder theorem splits into its prime fibres
(`CyclicAlgebra.cyclicPhaseCRT`).  The compiler stages act on all of this by
morphisms (`CompilerPipeline.wordStep_compiled_mono`,
`CompilerPipeline.compiled_answers_subclass`).  Nothing above the integer
grading — no quaternions, no Clifford algebra, no Bott periodicity — is claimed;
`PROGRAM-ALGEBRA.md` says so rung by rung.

## 10. Growing the corpus from its own sources

[`ENRICHMENT.md`](ENRICHMENT.md) is the loop: pull every Wikimedia page of an
item in every language, scan the articles and the sources they cite, rank what
is missing by how often it is referred to, and absorb the most referenced of it.
Every stage is guarded by a theorem — an enriched base is still well formed and
entails the base it came from, and every statement it adds carries the address
it was read from (`KB.enrich_wellFormed`, `KB.enrich_entails`,
`KB.enrich_provenance`); the head of a ranking really is a most referenced
missing term (`Enrichment.termDemand_head_max`); the to-do list is empty exactly
when the scan points at nothing new (`Enrichment.frontier_isEmpty_iff_closed`);
a whole round is conservative (`Enrichment.State.step_entails`); and a scan
survives the disk (`Cli.parseScan?_renderScan`).  The first run, over the seven
theories, is `EnrichmentRun.enriched_entails_base` and
`EnrichmentRun.missingTerms_shrank`.

The same idea applied to the crawl itself: a download of bounded depth leaves
items it never asked about, and asking about them is a *frontier round*.  Four
rounds take the frontier from 144 items to 14 — 144, 70, 42, 18, then 14
(`Corpus.frontier_sizes`, `Corpus.frontier_sizes_decreasing`) — each of them
losing nothing (`Corpus.coreExtended_entails_core`).

## 11. Extracting a module about a few items

Nobody reasons about all of Wikidata at once, so the library can carve out the
part that matters.  `Wikidata.KB.moduleOf kb seeds` keeps the items reachable
from the seeds along `subclass of` and `instance of`, with the statements out of
them (`KB.mem_moduleItemsF_iff` says exactly what that is), and the extraction is
proved to be safe in both directions: it derives nothing the base does not
(`KB.moduleOf_isSubclassOf_le`, `KB.moduleOf_isInstanceOf_le`) and, about an item
it keeps, it derives everything the base does
(`KB.moduleOf_isSubclassOf`, `KB.moduleOf_isInstanceOf`).  A module of a valid
base is valid (`KB.moduleOf_valid`), extraction is monotone in the seeds and
idempotent (`KB.moduleItemsF_mono`, `KB.moduleOf_moduleItemsF`), and taking all
the items back gives the base itself (`KB.moduleOf_items_self`).

On the downloaded corpus of 1578 items the module about *mathematics* (`Q395`)
has 279 items, 405 `subclass of` and 266 `instance of` statements
(`ModulesCorpus.mathModule_size`) — a fifth of the corpus that answers every
question about `Q395` exactly as the whole of it
(`ModulesCorpus.mathModule_subclass_conservative`).  The tool exposes it as
`wikidata module FILE.wdkb Q395`.

## 12. Publishing the findings: mirrors, peers and archives

The findings do not stay in the repository.  `Wikidata.Publish` writes a
knowledge base as JSON Lines and proves that reading the file back gives exactly
what was written (`Publish.parseJsonl?_jsonlOfKB`), that the file has one row per
fact (`Publish.length_kbRecs`), and that the canonical text determines the base,
so a content address identifies it (`Publish.eq_of_renderKB_eq`,
`Publish.cid_eq_of_renderKB_eq`).

`Wikidata.Sync` is the peer-to-peer layer.  Two replicas that heard different
halves of the story are merged by `KB.sync`, which is the least upper bound for
entailment: it keeps everything either peer knew (`KB.sync_entails_left`,
`KB.sync_entails_right`) and invents nothing (`KB.sync_least`).  Because merging
is commutative, associative and idempotent up to equivalence
(`KB.sync_comm_equiv`, `KB.sync_assoc_equiv`, `KB.sync_idem_equiv`), one round of
gossip leaves every peer in the same state (`KB.gossip_pairwise_equiv`) and no
peer's contribution is lost (`KB.gossip_entails_all`) — strong eventual
consistency, proved rather than assumed.

`Wikidata.Archive` is the deposit format for archive.org: a bundle re-imports to
the base it was made from (`Archive.importKB?_bundleOf`), the public JSON Lines
file alone suffices (`Archive.importKB?_rows_only`), the two copies in a bundle
agree (`Archive.bundle_copies_agree`), and the manifest of lengths and digests is
honest (`Archive.checkManifest_bundleOf`).

`RequestProject/PublishExamples.lean` runs all of it on the Douglas Adams
fragment: 64 published rows (`PublishExamples.douglas_rows`), the content address
`wdkb1-d85a9bb9e764ac9a` (`PublishExamples.douglas_cid`), a deposit that
re-imports (`PublishExamples.douglas_archive_roundTrip`), and two replicas that
provably disagree (`PublishExamples.replicas_disagree`) and then provably converge
(`PublishExamples.gossip_converges`, `PublishExamples.gossip_keeps_everything`).

The tool turns this into files: `wikidata publish data/*.wdkb --out site` builds
the static site and JSON API that the GitHub Pages, Vercel, Cloudflare, Hugging
Face and Toolforge deployments all serve, `wikidata archive` and
`wikidata unarchive` make and read the archive.org deposits in `archive/`, and
`wikidata sync` merges peers.  [`PUBLISHING.md`](PUBLISHING.md) is the operator's
guide.

## Regenerating the images

```
python3 docs/make_showcase_svg.py     # rewrites docs/showcase.svg
python3 docs/make_status_svg.py       # rewrites docs/status.svg
python3 docs/stats.py                 # the figures both use, as JSON
```

`docs/stats.py` counts the modules, theorems, definitions, lines, `decide`
checks and `#eval` demos in `RequestProject/`, the items and statements in
`data/*.wdkb`, the entailed facts listed in `RequestProject/Generated/` — and
how many of them no single fragment entails — the commands documented in
`docs/CLI.md`, and the glossary in `data/glossary.tsv`.  It also holds the one
layering of the development that both images draw, so they cannot disagree.
Nothing on either image is typed in by hand except the prose, and the layer
charts fail to build if a module is left out or counted twice.
