# The ontology inside the ontology

Wikidata describes itself in its own vocabulary. *Entity* (`Q35120`), *class*
(`Q16889133`), *metaclass* (`Q19478619`), *fixed-order class* and
*variable-order class* are ordinary items; the statements that classify them use
the same two properties, `instance of` (`P31`) and `subclass of` (`P279`), as
statements about volcanoes and violinists. `Wikidata:WikiProject Ontology` is
therefore a document *about* a structure written *inside* that structure.

This page reviews the four notions the request named — **reduction**,
**pullback**, **retraction**, **Frobenius** — says what each one means in
general, and shows exactly which theorem of the development realises it. The
Lean sources are
[`RequestProject/Reflection.lean`](../RequestProject/Reflection.lean) (the
abstract layer),
[`RequestProject/Renaming.lean`](../RequestProject/Renaming.lean) (the technical
transport lemmas) and
[`RequestProject/MetaFrobenius.lean`](../RequestProject/MetaFrobenius.lean) (the
meta level itself), on top of the existing
[`RequestProject/SelfDescription.lean`](../RequestProject/SelfDescription.lean).

## The operation being modelled

Identifiers in this development are `Qid`s, and one of the constructors is
`Qid.about x` — "the item that, at the meta level, names `x`". The operation
that puts an ontology inside itself is the **meta lift**

```
KB.metaLift kb = kb.rename Qid.about
```

which re-reads every identifier as its own meta-level name, and its inverse is
the **reduction**

```
KB.metaReduce kb = kb.rename Qid.deMeta,      Qid.deMeta (about x) = x
```

which strips one meta level and leaves ground identifiers alone.

Everything below is about this pair.

## 1. Reduction

*In general.* A **reduct** of a structure is the same structure read through
less data: fewer symbols, fewer statements, or a renaming of the carrier. The
reduct must not create anything: whatever it derives, the original derived
already.

*Here.* Two reducts appear.

* Along a renaming: `Ontology.comap O f hf` reads an ontology through an
  injective renaming `f` of identifiers. It is an ontology again — the level
  discipline and the antisymmetry of the class hierarchy survive, the latter
  because `f` is injective — and the renaming is a morphism into the original
  (`Ontology.comapMorphism`), so `Ontology.comap_subclassOf` and
  `Ontology.comap_instanceOf` say that the reduct invents nothing.
* Along an inclusion: `Ontology.subVocabulary O S` is the sub-ontology carried by
  a sub-vocabulary `S`, the special case `f = Subtype.val`. (The other kind of
  reduct — same items, fewer statements — is `Ontology.restrict` in
  [`Provenance.lean`](../RequestProject/Provenance.lean).)

The executable counterpart is the point of `Renaming.lean`: for an **injective**
renaming, membership, metaclass levels, asserted statements, their
reflexive–transitive closures, the certified engine and every clause of the
validator all transport in both directions, ending in

```
KB.valid_rename_iff : (kb.rename f).valid = true ↔ kb.valid = true
```

So renaming along an injection is a pure change of names — in sharp contrast to
the item merges of [`ItemMerge.lean`](../RequestProject/ItemMerge.lean), where
the map identifies two identifiers and the ontology genuinely changes (and may
even stop being valid).

`KB.metaReduce_metaLift : kb.metaLift.metaReduce = kb` is the reduction of the
meta copy: passing to the meta level loses nothing at all. Hence
`KB.metaLift_injective`.

## 2. Retraction

*In general.* A **retraction** of a space or structure onto a part of it is a map
`r` back that undoes an embedding `i`: `r ∘ i = id`. The embedded part is a
*retract*; the composite `i ∘ r` is an idempotent, and the retract is exactly its
fixed-point set. Retractions are how one says "this larger object contains this
smaller one, faithfully".

*Here.* `Ontology.Retract` is a section–retraction pair of strict morphisms, and
`KB.metaRetract` is the instance: an ontology is a retract of its own meta copy,
with the lift as section and the reduction as retraction. The value of that is
conservativity — the theorems

* `Ontology.Retract.subclassOf_iff`, `Ontology.Retract.instanceOf_iff`,
  `Ontology.Retract.hasInstance_iff`, `Ontology.Retract.isMetaclass_iff`,

specialised to the meta level as

* `KB.metaLift_subclassOf_iff`, `KB.metaLift_instanceOf_iff`,
  `KB.metaLift_isMetaclass_iff`,

which say: the meta copy derives a fact about `about a` and `about b` **exactly
when** the original derives the corresponding fact about `a` and `b`. Talking
about an ontology adds no knowledge of it, and destroys none. The executable
version, `KB.metaLift_isSubclassOf_iff` and `KB.metaLift_isInstanceOf_iff`, says
the same about the Boolean engine, and `KB.metaLift_valid_iff` says the meta copy
is valid exactly when the original is.

The idempotent is `KB.metaCore = metaLift ∘ metaReduce`, and
`KB.metaCore_eq_self_iff` identifies its fixed points: the knowledge bases every
one of whose identifiers is a meta name (`KB.allMetaB`).

*Further.* [`PullbackRetraction.lean`](../RequestProject/PullbackRetraction.lean)
develops the notion itself: retracts contain the isomorphisms and compose
(`Ontology.Retract.refl`, `Ontology.Retract.comp`, `Ontology.Retract.ofIso`); a
section is a split monomorphism and a retraction a split epimorphism in `Ont`;
retracts are stable under base change (`Ontology.Retract.baseChange`), so
conservativity survives alignment against a third ontology; and the converse of
the idempotent construction holds — **idempotents split**
(`Ontology.splitRetract`), so `Ont` is idempotent complete
(`Ontology.isIdempotentComplete_Ont`) and "retract" and "split idempotent" name
the same thing. Two worked examples are included: merging a duplicated item is
the splitting of an idempotent, and hence loses nothing
(`Ontology.Duplicate.mergeRetract`); and an extension that asserts a new
`subclass of` statement is not a retract at all
(`Ontology.exists_no_retract`), so conservativity is a real constraint and not a
formality. [`RetractTopology.lean`](../RequestProject/RetractTopology.lean) adds
the topological reading: the section is an embedding of item spaces
(`Ontology.Retract.isEmbedding_sec`), specialization between embedded items is
the `subclass of` order of the small ontology
(`Ontology.Retract.specializes_iff`), and the retraction is a quotient map
(`Ontology.Retract.isQuotientMap_ret`) but need not be open
(`Ontology.exists_retract_ret_not_isOpenMap`).

## 3. Pullback

*In general.* The **pullback** (fibre product) of `f : A → C` and `g : B → C` is
the object of matched pairs `{(a, b) | f a = g b}`, with two projections making a
commuting square, and universal among such squares. It is the categorical form
of "align two things over a third".

*Here.* `Ontology.pullback F G` is the fibre product of two strict morphisms of
ontologies: its items are the pairs the two morphisms identify, and a statement
holds of a pair exactly when it holds of both components. It really is an
ontology (the level discipline comes from the first component, antisymmetry
componentwise), it comes with projections `Ontology.pullback.fst`,
`Ontology.pullback.snd`, a commuting square `Ontology.pullback.comm`, and the
universal property in two halves: `Ontology.pullback.lift` (existence) and
`Ontology.pullback.lift_unique` (uniqueness).

The reason to have it here is `KB.metaLift_isPullback`: the meta copy of an
ontology, together with the reduction back to it, **is** the pullback of the
reduction along the identity — the comparison morphism `KB.metaPullbackLift` and
the projection are mutually inverse. So "the ontology inside the ontology" is not
merely an embedding; it is a pullback square, the universal way of pairing an
identifier with the item it names.

Note which notion of morphism this needs. Ontology *alignments*
([`Alignment.lean`](../RequestProject/Alignment.lean)) are deliberately lax: an
asserted statement may be matched by a *derived* fact, which is what ontology
matching in the wild does. Limits need the strict notion, `Ontology.Morphism`,
which sends direct statements to direct statements; every strict morphism is an
alignment (`Ontology.Morphism.toAlignment`).

*Further.* The same file gives the fibre product's calculus: it is symmetric
(`Ontology.pullback.symmIso`), trivial along the identity
(`Ontology.pullback.idIso`), associative — an iterated fibre product is a fibre
product along the composite (`Ontology.pullback.assocIso`) — and the fibre
product of an injective morphism with itself is its source
(`Ontology.pullback.diagonalIso`). Its items are exactly the matched ones
(`Ontology.pullback.range_fst`), so the fibre product of two sub-vocabularies of
one ontology is the sub-vocabulary of their intersection
(`Ontology.pullback.subVocabularyIso`), and monomorphisms are stable under base
change (`Ontology.mono_pbSnd_of_mono`).

## 4. Frobenius

Two different things go by this name, and both appear.

### 4a. Frobenius reciprocity (the projection formula)

*In general.* Along a map `f`, sets (or representations, or sheaves) can be
pushed forward and pulled back, pushforward is left adjoint to pullback, and the
two interact by the projection formula `f_*(A ⊓ f^*B) = f_*A ⊓ B`.

*Here.* Class extensions are the sets in question: `Ontology.extension c` is the
set of instances of `c`. Along an alignment, `Alignment.push` is the image and
`Alignment.pull` the preimage, and

* `Ontology.Alignment.push_subset_iff` — pushforward is left adjoint to pullback;
* `Ontology.Alignment.projection_formula` — `f_*(A ∩ f^*B) = f_*A ∩ B`;
* `Ontology.Alignment.push_extension_subset` — an alignment maps instances of a
  class to instances of the aligned class;
* `Ontology.Retract.preimage_extension` — for a retract the pullback of an
  extension is *exact*: the instances of an embedded class are precisely the
  embedded instances, so passing to the larger ontology adds no members. At the
  meta level this is `KB.metaLift_extension`.

### 4b. A Frobenius-like endomorphism

*In general.* The Frobenius endomorphism `x ↦ x^p` of a ring of characteristic
`p` is an injective, structure-preserving self-map which is usually not
surjective; it fixes the prime field; and on a *perfect* ring it is an
automorphism, with the `p`-th root map as inverse. Its iterates give a tower.

*Here.* The meta lift behaves the same way.

| Frobenius | meta lift |
|---|---|
| `x ↦ x^p` is injective | `KB.metaLift_injective` |
| a ring homomorphism | `KB.metaLift_merge` (joins), `KB.metaLift_entails_iff` (entailment), `KB.valid_rename_iff` (validity) |
| moves almost everything | `KB.metaLift_ne_self`: no non-empty knowledge base is its own meta copy |
| fixes the prime field | `Qid.deMeta_eq_self_iff`: the reduction fixes exactly the ground identifiers |
| an automorphism of the perfect part, with inverse the `p`-th root | `KB.metaEquiv : KB ≃ {kb // kb.allMetaB = true}`, with inverse `KB.metaReduce` |
| iterates give a tower | `KB.metaReduce_iterate_metaLift_iterate`, `KB.valid_metaLift_iterate` |

The "perfect part" is exactly the fixed-point set of the idempotent
`KB.metaCore` (`KB.metaCore_eq_self_iff`), i.e. the knowledge bases already
written in meta-vocabulary — the ones that are *about* ontologies rather than
about the world.

## What this adds to the self-description already there

[`SelfDescription.lean`](../RequestProject/SelfDescription.lean) builds, for any
knowledge base, a valid meta-ontology naming it, its items and its metaclass
levels, with the tower `lvl n` `instance of` `lvl (n+1)`
(`KB.selfDescription_valid`, `KB.selfDescription_lvl_tower`). That is the
*object*. This layer is about the *operation* that produces such objects, and it
places that operation: it is a reduction with a section, hence a retraction,
hence a conservative extension; it is a pullback square; and it is a
Frobenius-like endomorphism which restricts to an automorphism of the meta-written
knowledge bases.

A worked three-item fragment at the end of `MetaFrobenius.lean` checks all of it
by computation (`decide`), including the two-step tower
`about (about (Q42))`.
