# Topology, Grothendieck, homotopy and cubical type theory, categories, fields, groups — around the pullback

`RequestProject/Reflection.lean` builds the **pullback** of ontologies: two
ontologies aligned into a common reference one have a fibre product, the
ontology of *matched pairs*, with two projections, a commuting square and a
universal property.  It is the operation that says what it means to align two
vocabularies over a third.

This page is about the seven theories that meet that construction, each added as
its own module and each grounded in the Wikidata article that names it.  The
common thread is deliberate: every layer below is a statement *about the
pullback*.

| layer | Wikidata | module | what is proved |
| --- | --- | --- | --- |
| category theory | [Q217413](https://www.wikidata.org/wiki/Q217413) | `RequestProject/CategoryOfOntologies.lean` | ontologies and strict morphisms form a category `Ont`; the fibre product **is** a `CategoryTheory.IsPullback` square, so `Ont` has all pullbacks; the forgetful functor takes it to the pullback of sets |
| topology | [Q42989](https://www.wikidata.org/wiki/Q42989) | `RequestProject/OntologyTopology.lean` | a class hierarchy is a space (the Alexandrov topology of `subclass of`); a strict morphism is exactly a continuous map; the matched pairs are the pullback of the item spaces **in `TopCat`** |
| Grothendieck topology | [Q1062242](https://www.wikidata.org/wiki/Q1062242) | `RequestProject/GrothendieckSite.lean` | jointly surjective families of alignments are a `Pretopology` on `Ont`, hence a Grothendieck topology; its pullback-stability axiom *is* the fibre product |
| homotopy type theory | [Q5891840](https://www.wikidata.org/wiki/Q5891840) | `RequestProject/HomotopyTypes.lean` | the fibre product is the type of triples `(x, y, p : F x = G y)`; base change of fibrations; base change of an equivalence; homotopy invariance; the pasting lemma |
| cubical type theory | [Q139761564](https://www.wikidata.org/wiki/Q139761564) | `RequestProject/CubicalTypes.lean` | the De Morgan interval and cubes; a cube in the fibre product is a pair of cubes agreeing over the reference ontology, compatibly with faces and degeneracies |
| group theory | [Q874429](https://www.wikidata.org/wiki/Q874429) | `RequestProject/OntologyGroups.lean` | the automorphism group of an ontology; the subgroup of compatible triples of symmetries; the homomorphism to the symmetries of the pullback, with equivariant projections |
| field theory | [Q903820](https://www.wikidata.org/wiki/Q903820) | `RequestProject/OntologyFields.lean` | class extensions as a `GF(2)`-vector space (symmetric difference is addition, intersection is multiplication); the pullback square, linearly; the fibre product of extension spaces |

## The pullback, seven times over

* **Categorically.** `Ontology.isPullback_pbOnt` says the hand-built fibre
  product is a limit of the cospan `X ⟶ Z ⟵ Y`, and
  `Ontology.instHasPullbacksOnt` that every cospan has one.  Everything below is
  stated over this category.
* **Topologically.** Items carry the Alexandrov topology of the class hierarchy
  (`Ontology.subclassTopology`); continuity is monotonicity for `subclass of`
  (`Ontology.continuous_iff_subclass`).  The matched pairs, as a subspace of the
  product, are the pullback in `TopCat` (`Ontology.isPullback_topCat`), and the
  ontology-level fibre product maps onto it by a continuous bijection
  (`Ontology.continuous_pbCompare`, `Ontology.bijective_pbCompare`) — its own
  topology is finer, because inside the fibre product a subclass step has to be
  taken on both sides at once.  `RequestProject/PullbackComparison.lean` settles
  how much finer: specialization in an item space *is* the subclass order
  (`Ontology.specializes_iff_subclassOf`), the comparison map is a homeomorphism
  exactly when componentwise subclass chains can be run simultaneously
  (`Ontology.isHomeomorph_pbCompare_of_componentwise`), and
  `Ontology.exists_not_isHomeomorph_pbCompare` exhibits a cospan where they
  cannot, so the two pullbacks really do differ.
* **As a site.** A family of alignments *covers* when every item of the target
  is named by one of them.  That covers are stable under base change is exactly
  `Ontology.pbSnd_surjective_of_surjective`: given a cover of the reference
  ontology and any second alignment, the projection of the fibre product covers.
  So `Ontology.surjectivePretopology` is a pretopology and
  `Ontology.ontologyTopology` a Grothendieck topology.
* **Homotopically.** `Ontology.pullbackEquivSigma` reads a matched pair as a
  triple `(x, y, p)` with `p` a path; `Ontology.fibPbFstEquiv` is base change of
  fibrations, `Ontology.pbFstEquivOfBijective` base change of an equivalence,
  and `Ontology.pullbackPasteEquiv` / `Ontology.isPullback_paste` the pasting
  lemma.  (Lean's identity types satisfy UIP, so this is the `h`-set fragment of
  the homotopy reading; univalence is not available.)
* **Cubically.** `Ontology.cubePullbackEquiv`: a cube in the fibre product is a
  pair of cubes agreeing over the reference ontology — the universal property in
  cubical clothing, with faces and degeneracies computed componentwise.  The
  file also records honestly that a two-point interval made of *points* is
  indiscrete (`Ontology.pathEquivUnit`), which is why the content lies in the
  cubes and not in one-dimensional paths.
* **Group-theoretically.** A symmetry of the fibre product can be assembled from
  a compatible triple of symmetries of the two ontologies and the reference one:
  `Ontology.autOverSubgroup` is the subgroup of such triples and
  `Ontology.pbAut` the homomorphism to `Aut` of the pullback, with equivariant
  projections (`Ontology.pbAut_fst`, `Ontology.pbAut_snd`).
* **Field-theoretically.** Over `GF(2)`, sets of items are vectors
  (`Ontology.ExtSpace`), symmetric difference is addition
  (`Ontology.chi_symmDiff`) and intersection is multiplication
  (`Ontology.chi_inter`).  Restriction along an alignment is linear
  (`Ontology.comapLin`), the pullback square induces a commuting square of
  linear maps (`Ontology.comapLin_pb_comm`), and the map into the fibre product
  of the two extension spaces is injective as soon as one alignment covers the
  reference ontology (`Ontology.injective_toExtPullback`).

## Grounded in Wikidata

Each of these notions is a Wikidata article, matched in
`RequestProject/Vocabulary.lean` with the declaration that instantiates it, and
checked against the downloaded glossary under the exact label Wikidata records
(`Grounded.vocabulary_grounded`).  The articles themselves were then queried into
`data/theories.wdkb` (191 items, 923 entailed `subclass of` facts) and compiled to
`RequestProject/Generated/Theories.lean`, so what Wikidata *says* about them can
be compared with what the library *proves* (`RequestProject/TheoryCorpus.lean`):

* `group ⊑ monoid` — and here the automorphisms of an ontology are the
  invertible part of the monoid of its structure-preserving self-maps;
* `subgroup ⊑ group` and `automorphism group ⊑ group` — `autOverSubgroup`,
  `autPerm`;
* `group action ⊑ homomorphism` — `pbAut` and the action it induces on matched
  pairs;
* `field ⊑ vector space` and `vector space ⊑ free module` — `GF(2)` and
  `ExtSpace`;
* `linear map ⊑ function` — `comapLin`;
* `Alexandrov topology ⊑ topology` — the topology of a class hierarchy;
* `topological space ⊑ mathematical structure`, `Grothendieck topology ⊑
  mathematical object`;
* `homotopy type theory ⊑ type theory ⊑ formal system`, `fibration ⊑ bundle`,
  `De Morgan algebra ⊑ distributive lattice`;
* `topology ⊑ mathematics` and `group theory ⊑ mathematics`.

## Rebuilding

```sh
./.lake/build/bin/wikidata fetch Q42989 Q1062242 Q5891840 Q139761564 Q217413 \
    Q903820 Q874429 --depth 2 --name "theories-of-the-pullback" --out data/theories.wdkb
./.lake/build/bin/wikidata lean data/theories.wdkb --module RequestProject.Generated.Theories
python3 scripts/fetch_glossary.py
lake build
```
