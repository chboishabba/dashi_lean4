# The mathematics articles of Wikidata that this library is made of

Wikidata has an article for nearly every notion a formalisation uses.  This page
is about the ones that describe **this** formalisation: `pullback`, `retract`,
`monoid`, `preorder`, `adjoint functor`, `partition of a set`, `quotient set`,
`well-founded relation`, … Each of them is matched here with the construction of
the library that instantiates it, and each match is a theorem — stated in
Mathlib's own vocabulary, so that "this really is a pullback" is checked and not
claimed.

Three files carry the layer.

* `RequestProject/MathResonance.lean` — the theorems: the constructions of the
  library, restated as instances of the standard notions.
* `RequestProject/Vocabulary.lean` — the table: which Wikidata entity names each
  of them.  `RequestProject/Grounded.lean` checks every entry against the
  downloaded glossary, under the exact label Wikidata records
  (`Grounded.vocabulary_grounded`, 174 notions).
* `RequestProject/MathCorpus.lean` — the data: `data/structures.wdkb` was
  downloaded from Wikidata with exactly these articles as its seeds (163 items,
  166 `subclass of` and 66 `instance of` statements, entailing 502 and 245
  facts), compiled to `RequestProject/Generated/Structures.lean`, and the file
  proves that the list of articles, the vocabulary and the fragment agree.

## The matches

| Wikidata article | the construction here | the theorem |
|---|---|---|
| [monoid](https://www.wikidata.org/wiki/Q208237) | the structure-preserving self-maps of an ontology | `Ontology.endoSubmonoid` — a `Submonoid (Function.End I)`; `Morphism.map_mem_endoSubmonoid`, `Morphism.ofEndo`, `Morphism.endo_mul` |
| [homomorphism](https://www.wikidata.org/wiki/Q215111) | a strict morphism of ontologies | `Ontology.Morphism`, `Morphism.subclassOf`, `Morphism.instanceOf` |
| [preorder](https://www.wikidata.org/wiki/Q1425985) | entailment between well-formed knowledge bases | `WellFormedKB.instPreorder`, a Mathlib `Preorder`; `WellFormedKB.not_antisymm` shows it is not a partial order |
| [strict order](https://www.wikidata.org/wiki/Q11077412) | proper `subclass of` | `Ontology.properSubclassOf_isStrictOrder`, an `IsStrictOrder` |
| [well-founded relation](https://www.wikidata.org/wiki/Q338021) | recorded ancestry | `FKB.properAncestor_wf`, `FKB.properAncestorWellFoundedRelation` |
| [pullback](https://www.wikidata.org/wiki/Q1397439) | the fibre product of two ontologies over a third | `Ontology.pullback`, with projections `fst`, `snd` |
| [limit](https://www.wikidata.org/wiki/Q1322614) | the same, as a limit | `Ontology.pullback.lift` |
| [universal property](https://www.wikidata.org/wiki/Q1417809) | the mediating morphism is unique | `Ontology.pullback.lift_unique` |
| [commutative diagram](https://www.wikidata.org/wiki/Q621542) | the pullback square commutes | `Ontology.pullback.comm` |
| [retract](https://www.wikidata.org/wiki/Q2141963) | an ontology sitting inside a larger one | `Ontology.Retract`, `KB.metaRetract` |
| [Conservative extension](https://www.wikidata.org/wiki/Q864213) | the larger ontology proves nothing new about the smaller | `Ontology.Retract.subclassOf_iff`, `KB.metaLift_subclassOf_iff` |
| [idempotent function](https://www.wikidata.org/wiki/Q44106280) | the split idempotent of a retract | `Ontology.Retract.idem_isIdempotentElem`, an `IsIdempotentElem` in `Function.End` |
| [idempotence](https://www.wikidata.org/wiki/Q368988) | the meta core | `KB.metaCore_isIdempotentElem` |
| [fixed point](https://www.wikidata.org/wiki/Q217608) | what those idempotents fix | `Ontology.Retract.fixedPoints_idem` (the image of the section), `KB.fixedPoints_metaCore` (the meta-written bases) |
| [adjoint functor](https://www.wikidata.org/wiki/Q357858) | pushforward ⊣ pullback of class extensions | `Ontology.Alignment.pushPull_gc`, a Mathlib `GaloisConnection`; unit and counit `le_pull_push`, `push_pull_le` |
| [Frobenius reciprocity](https://www.wikidata.org/wiki/Q48998319) | the projection formula of that adjunction | `Ontology.Alignment.projection_formula` |
| [partition of a set](https://www.wikidata.org/wiki/Q381060) | a disjoint union of classes | `Ontology.IsDisjointUnion.extension_eq_iUnion` and `pairwiseDisjoint_extension` |
| [injection](https://www.wikidata.org/wiki/Q182003) | the meta lift | `KB.metaLift_injective` |
| [surjective function](https://www.wikidata.org/wiki/Q229102) | the meta lift onto the meta-written bases | `KB.metaLift_surjective_onto_allMeta` |
| [bijection](https://www.wikidata.org/wiki/Q180907) | the two together | `KB.metaEquiv_bijective` |
| [isomorphism](https://www.wikidata.org/wiki/Q189112) | the meta lift with its inverse, the reduction | `KB.metaEquiv : KB ≃ {kb // kb.allMetaB = true}` |
| [equivalence relation](https://www.wikidata.org/wiki/Q130998) | what an item merge identifies | `KB.renameSetoid`, the kernel `Setoid.ker` of the renaming |
| [quotient set](https://www.wikidata.org/wiki/Q3966112) | the merged vocabulary | `KB.renameQuotientEquiv : Quotient (renameSetoid f) ≃ Set.range f` |
| [decidability](https://www.wikidata.org/wiki/Q430001) | the certified engine | `KB.isSubclassOf` |
| [soundness](https://www.wikidata.org/wiki/Q693083) | it decides the right relation | `KB.isSubclassOf_iff` |
| [completeness](https://www.wikidata.org/wiki/Q15846555) | the query evaluator returns every answer | `Query.mem_eval_iff` |
| [Least fixed point](https://www.wikidata.org/wiki/Q6134913) | the reachable set of the saturation engine | `Reach.reach_isLeast`, an `IsLeast` |
| [upper bound](https://www.wikidata.org/wiki/Q42866132) | a common superclass of two classes | `Ontology.IsCommonSuperclass`; the least one is `Ontology.IsLCS` |
| [intransitivity](https://www.wikidata.org/wiki/Q54980267) | being related is not transitive | `FKB.related_not_transitive`, a decided counterexample |
| [Herbrand structure](https://www.wikidata.org/wiki/Q1609475) | the model built out of the identifiers themselves | `Ontology.canonicalModel`, with `Ontology.semSubclassOf_iff` |
| [restriction](https://www.wikidata.org/wiki/Q1308999) | an ontology read on a sub-vocabulary | `Ontology.subVocabulary`, `Ontology.comap` |
| [directed graph](https://www.wikidata.org/wiki/Q1137726) | the `subclass of` graph the engine walks | `KB.supersL`, `KB.acyclic` |

## What Wikidata says about these notions, checked here

The downloaded fragment is an ontology like any other, so its own statements can
be checked and compared with the theorems above
(`RequestProject/MathCorpus.lean`).

* `bijection ⊑ injection` and `bijection ⊑ surjective function` — and here the
  meta lift is injective, surjective onto the meta-written bases, and a
  bijection.
* `pullback ⊑ limit` — and here the fibre product has the universal property, in
  both halves.
* `equivalence relation ⊑ preorder` — and here entailment is a preorder which is
  neither an equivalence relation (`WellFormedKB.not_symm`) nor a partial order
  (`WellFormedKB.not_antisymm`).
* `preorder ⊑ transitive relation` and `strict order ⊑ transitive relation` —
  where `transitive relation` (Q64861) is the entity already grounded in
  `Ontology.subclassOf_trans`.
* `adjoint functor ⊑ functor` — and here pushforward and pullback are monotone
  and adjoint.
* `idempotent function ⊑ idempotent element` — which is literally how the two
  idempotents of this library are stated, as `IsIdempotentElem` in the monoid
  `Function.End`.

## The theories attached to the pullback

Seven further theories — topology, Grothendieck topology, homotopy and cubical
type theory, category theory, field theory and group theory — are matched with
the constructions around the fibre product of ontologies in the same way; see
[`THEORIES.md`](THEORIES.md).

## Rebuilding

```sh
scripts/refresh-corpus.sh          # re-fetches data/structures.wdkb and recompiles it
python3 scripts/fetch_glossary.py  # re-downloads the labels the vocabulary claims
python3 scripts/wd_search.py "quotient set" "well-founded relation"   # find more articles
```
