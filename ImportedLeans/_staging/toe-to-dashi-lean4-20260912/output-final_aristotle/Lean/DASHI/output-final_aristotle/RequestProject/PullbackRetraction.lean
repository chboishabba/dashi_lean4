import RequestProject.OntologyLimits

/-!
# Pullbacks and retractions, continued

*Wikidata: pullback (Q1397439), fibre product (Q1397439), retract (Q2914389),
section (Q7442885), idempotent function (Q44106280), monomorphism (Q1954661),
isomorphism (Q189112), Karoubi envelope (Q6371155).*

`RequestProject.Reflection` builds the fibre product `Ontology.pullback` of two
ontologies over a third and the notion of a `Ontology.Retract`;
`RequestProject.CategoryOfOntologies` identifies the fibre product as a genuine
pullback square in the category `Ont`.  This file continues both stories.

## Isomorphisms

`Ontology.Isomorphism` is a strict morphism with a strict inverse.  It is the
common language for the results below: every isomorphism is a retract in both
directions (`Ontology.Isomorphism.toRetract`).

## Pullback calculus

* `Ontology.pullback.symmIso` — the fibre product is symmetric: matching `O₁`
  with `O₂` over `O₃` gives the same ontology as matching `O₂` with `O₁`.
* `Ontology.pullback.idIso` — matching an ontology with the reference ontology
  along the identity changes nothing.
* `Ontology.pullback.diagonalIso` — the fibre product of an *injective* morphism
  with itself is the source: an injective alignment matches each item with
  itself and nothing else.
* `Ontology.mono_pbSnd_of_mono` — **monomorphisms are stable under base
  change**, the categorical reading of
  `Ontology.pbSnd_injective_of_injective`, together with the missing companion
  `Ontology.pbFst_injective_of_injective` of the base change results of
  `RequestProject.CategoryOfOntologies`.

## Retraction calculus

* `Ontology.Retract.refl`, `Ontology.Retract.comp`, `Ontology.Retract.ofIso` —
  retracts contain the isomorphisms and are closed under composition.
* `Ontology.Retract.ret_surjective`, `Ontology.Retract.isSplitMono_sec`,
  `Ontology.Retract.isSplitEpi_ret` — a section is a split monomorphism and a
  retraction a split epimorphism in `Ont`.
* `Ontology.splitRetract` — **idempotents split**: an idempotent strict
  endomorphism of an ontology is the section–retraction composite of the retract
  onto its sub-vocabulary of fixed items, and
  `Ontology.isIdempotentComplete_Ont` records that `Ont` is therefore an
  idempotent complete (Karoubian) category.  Together with
  `Ontology.Retract.idem_idempotent` this makes "retracts = split idempotents"
  precise.
* `Ontology.Retract.pullbackIso` — a section is itself a pullback: the fibre
  product of `sec` with `sec` is the small ontology.
* `Ontology.Retract.baseChange` — **retracts are stable under base change**: a
  retract over the reference ontology induces a retract of the two fibre
  products, and hence (`Ontology.Retract.baseChange_subclassOf_iff`,
  `Ontology.Retract.baseChange_instanceOf_iff`) the base changed extension is
  still conservative.

## What the fibre product contains

* `Ontology.pullback.range_fst`, `Ontology.pullback.range_snd`,
  `Ontology.pullback.image_range_fst` — the items of the fibre product are
  exactly the matched ones, and inside the reference ontology they are the
  intersection of the two images.
* `Ontology.pullback.subVocabularyIso` — **aligning two fragments of one
  ontology along their inclusions gives the fragment they share**: the fibre
  product of two sub-vocabularies is the sub-vocabulary of the intersection.
* `Ontology.pullback.homEquiv` — the universal property as a bijection: a strict
  morphism into the fibre product *is* a compatible pair of strict morphisms.
* `Ontology.pullback.assocIso` — the pasting law: an iterated fibre product is a
  fibre product along the composite.
* `Ontology.Retract.isKernelPair_sec` — a section is its own kernel pair.

## Worked examples

* `Ontology.Duplicate` — a three-item ontology with a duplicated class, the
  merge that identifies the duplicate, and the resulting retract of the
  deduplicated fragment (`Ontology.Duplicate.mergeRetract`): merging duplicates
  is the splitting of an idempotent, and conservativity says the merge loses
  nothing.
* `Ontology.Gap`, `Ontology.exists_no_retract` — conservativity is a real
  constraint: two classes with nothing said about them are *not* a retract of
  the same two classes with a `subclass of` statement between them, even though
  the inclusion is an injective strict morphism.
* `Ontology.exists_bijective_not_isIso` — the same cospan shows that the
  converse of `Ontology.bijective_of_isIso` fails: a strict morphism can be a
  bijection on items without being an isomorphism of ontologies
  (`Ontology.ontIso`, `Ontology.isoToIsomorphism` identify the two readings of
  "isomorphism" that this compares).
-/

open CategoryTheory CategoryTheory.Limits

namespace Wikidata
namespace Ontology

universe u

variable {I J K L : Type*}

/-! ## Isomorphisms of ontologies -/

/-- An **isomorphism of ontologies**: a strict morphism with a strict inverse.
Both ontologies then assert literally the same statements, up to the renaming of
items. -/
structure Isomorphism (O₁ : Ontology I) (O₂ : Ontology J) where
  /-- The morphism. -/
  hom : Morphism O₁ O₂
  /-- Its inverse. -/
  inv : Morphism O₂ O₁
  /-- The inverse undoes the morphism. -/
  inv_hom : ∀ a, inv.map (hom.map a) = a
  /-- The morphism undoes the inverse. -/
  hom_inv : ∀ b, hom.map (inv.map b) = b

namespace Isomorphism

variable {O₁ : Ontology I} {O₂ : Ontology J} {O₃ : Ontology K}

/-- The identity isomorphism. -/
def refl (O : Ontology I) : Isomorphism O O where
  hom := Morphism.id O
  inv := Morphism.id O
  inv_hom _ := rfl
  hom_inv _ := rfl

/-- The inverse isomorphism. -/
def symm (E : Isomorphism O₁ O₂) : Isomorphism O₂ O₁ where
  hom := E.inv
  inv := E.hom
  inv_hom := E.hom_inv
  hom_inv := E.inv_hom

/-- Isomorphisms compose. -/
def trans (E : Isomorphism O₁ O₂) (D : Isomorphism O₂ O₃) : Isomorphism O₁ O₃ where
  hom := E.hom.comp D.hom
  inv := D.inv.comp E.inv
  inv_hom a := by simp [Morphism.comp, D.inv_hom, E.inv_hom]
  hom_inv c := by simp [Morphism.comp, E.hom_inv, D.hom_inv]

/-- The underlying map of an isomorphism is a bijection. -/
theorem bijective (E : Isomorphism O₁ O₂) : Function.Bijective E.hom.map :=
  ⟨Function.LeftInverse.injective E.inv_hom, fun b => ⟨E.inv.map b, E.hom_inv b⟩⟩

/-- The underlying bijection of an isomorphism. -/
def toEquiv (E : Isomorphism O₁ O₂) : I ≃ J where
  toFun := E.hom.map
  invFun := E.inv.map
  left_inv := E.inv_hom
  right_inv := E.hom_inv

/-- **An isomorphism is a retract**, in either direction. -/
def toRetract (E : Isomorphism O₁ O₂) : Retract O₁ O₂ where
  sec := E.hom
  ret := E.inv
  ret_sec := E.inv_hom

/-- Isomorphic ontologies derive the same `subclass of` facts. -/
theorem subclassOf_iff (E : Isomorphism O₁ O₂) {a b : I} :
    O₂.SubclassOf (E.hom.map a) (E.hom.map b) ↔ O₁.SubclassOf a b :=
  E.toRetract.subclassOf_iff

/-- Isomorphic ontologies derive the same `instance of` facts. -/
theorem instanceOf_iff (E : Isomorphism O₁ O₂) {a c : I} :
    O₂.InstanceOf (E.hom.map a) (E.hom.map c) ↔ O₁.InstanceOf a c :=
  E.toRetract.instanceOf_iff

end Isomorphism

/-! ## Pullback calculus -/

namespace pullback

variable {O₁ : Ontology I} {O₂ : Ontology J} {O₃ : Ontology K}

/-- Swapping the two factors of a fibre product. -/
def swap (F : Morphism O₁ O₃) (G : Morphism O₂ O₃) :
    Morphism (pullback F G) (pullback G F) where
  map p := ⟨(p.1.2, p.1.1), p.2.symm⟩
  map_P279 h := ⟨h.2, h.1⟩
  map_P31 h := ⟨h.2, h.1⟩

/-- **The fibre product is symmetric**: matching `O₁` with `O₂` over the
reference ontology gives the same ontology as matching `O₂` with `O₁`. -/
def symmIso (F : Morphism O₁ O₃) (G : Morphism O₂ O₃) :
    Isomorphism (pullback F G) (pullback G F) where
  hom := swap F G
  inv := swap G F
  inv_hom _ := rfl
  hom_inv _ := rfl

/-- **Matching along the identity changes nothing**: the fibre product of
`F : O₁ ⟶ O₃` with the identity of `O₃` is `O₁` itself. -/
def idIso (F : Morphism O₁ O₃) : Isomorphism (pullback F (Morphism.id O₃)) O₁ where
  hom :=
    { map := fun p => p.1.1
      map_P279 := fun h => h.1
      map_P31 := fun h => h.1 }
  inv :=
    { map := fun a => ⟨(a, F.map a), rfl⟩
      map_P279 := fun h => ⟨h, F.map_P279 h⟩
      map_P31 := fun h => ⟨h, F.map_P31 h⟩ }
  inv_hom p := Subtype.ext (Prod.ext rfl p.2)
  hom_inv _ := rfl

/-- **The fibre product of an injective morphism with itself is its source**:
an injective alignment matches each item with itself and with nothing else. -/
def diagonalIso (F : Morphism O₁ O₃) (hF : Function.Injective F.map) :
    Isomorphism (pullback F F) O₁ where
  hom :=
    { map := fun p => p.1.1
      map_P279 := fun h => h.1
      map_P31 := fun h => h.1 }
  inv :=
    { map := fun a => ⟨(a, a), rfl⟩
      map_P279 := fun h => ⟨h, h⟩
      map_P31 := fun h => ⟨h, h⟩ }
  inv_hom p := Subtype.ext (Prod.ext rfl (hF p.2))
  hom_inv _ := rfl

end pullback

/-! ## Base change -/

variable {X Y Z : Ont.{u}}

/-- **Base change preserves injectivity**, first projection version (the
companion of `Ontology.pbSnd_injective_of_injective`). -/
theorem pbFst_injective_of_injective (F : X ⟶ Z) (G : Y ⟶ Z)
    (hG : Function.Injective G.map) : Function.Injective (pbFst F G).map := by
  rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ h
  have ha : a = a' := h
  subst ha
  have : b = b' := hG (by rw [← hab, ← hab'])
  subst this
  rfl

/-- **Monomorphisms are stable under base change** in `Ont`. -/
theorem mono_pbSnd_of_mono (F : X ⟶ Z) (G : Y ⟶ Z) [Mono F] : Mono (pbSnd F G) :=
  (mono_iff_injective _).2
    (pbSnd_injective_of_injective F G ((mono_iff_injective F).1 inferInstance))

/-! ## Retraction calculus -/

namespace Retract

variable {O₁ : Ontology I} {O₂ : Ontology J} {O₃ : Ontology K}

/-- Every ontology is a retract of itself. -/
def refl (O : Ontology I) : Retract O O where
  sec := Morphism.id O
  ret := Morphism.id O
  ret_sec _ := rfl

/-- **Retracts compose.** -/
def comp (R : Retract O₁ O₂) (S : Retract O₂ O₃) : Retract O₁ O₃ where
  sec := R.sec.comp S.sec
  ret := S.ret.comp R.ret
  ret_sec a := by simp [Morphism.comp, S.ret_sec, R.ret_sec]

/-- An isomorphism is a retract; this is `Ontology.Isomorphism.toRetract` under
another name. -/
def ofIso (E : Isomorphism O₁ O₂) : Retract O₁ O₂ := E.toRetract

/-- The retraction of a retract is surjective. -/
theorem ret_surjective (R : Retract O₁ O₂) : Function.Surjective R.ret.map :=
  fun a => ⟨R.sec.map a, R.ret_sec a⟩

/-- **A section is a pullback**: the fibre product of the embedding of a retract
with itself is the small ontology, because the embedding matches each item with
itself only. -/
def pullbackIso (R : Retract O₁ O₂) :
    Isomorphism (pullback R.sec R.sec) O₁ :=
  pullback.diagonalIso R.sec R.sec_injective

/-! ### Base change -/

variable {O₄ : Ontology L}

/-- A retract **over a reference ontology** `O₃`: the ambient ontology `O₄` and
its retract `O₂` both sit over `O₃`, compatibly with the section and the
retraction. -/
structure Over (G : Morphism O₂ O₃) (H : Morphism O₄ O₃) (R : Retract O₂ O₄) : Prop where
  /-- The section commutes with the two structure morphisms. -/
  sec_comm : ∀ y, H.map (R.sec.map y) = G.map y
  /-- The retraction commutes with the two structure morphisms. -/
  ret_comm : ∀ z, G.map (R.ret.map z) = H.map z

/-- **Retracts are stable under base change.** If `O₂` is a retract of `O₄` over
the reference ontology `O₃`, then matching a further ontology `O₁` against them
over `O₃` gives a retract of fibre products. -/
def baseChange (F : Morphism O₁ O₃) {G : Morphism O₂ O₃} {H : Morphism O₄ O₃}
    {R : Retract O₂ O₄} (hR : R.Over G H) : Retract (pullback F G) (pullback F H) where
  sec :=
    { map := fun p => ⟨(p.1.1, R.sec.map p.1.2), by rw [hR.sec_comm]; exact p.2⟩
      map_P279 := fun h => ⟨h.1, R.sec.map_P279 h.2⟩
      map_P31 := fun h => ⟨h.1, R.sec.map_P31 h.2⟩ }
  ret :=
    { map := fun p => ⟨(p.1.1, R.ret.map p.1.2), by rw [hR.ret_comm]; exact p.2⟩
      map_P279 := fun h => ⟨h.1, R.ret.map_P279 h.2⟩
      map_P31 := fun h => ⟨h.1, R.ret.map_P31 h.2⟩ }
  ret_sec p := Subtype.ext (Prod.ext rfl (R.ret_sec p.1.2))

/-- **Base change of a retract is conservative for the class hierarchy**: the
larger fibre product derives a `subclass of` fact between matched pairs coming
from the smaller one only if the smaller fibre product already does. -/
theorem baseChange_subclassOf_iff (F : Morphism O₁ O₃) {G : Morphism O₂ O₃}
    {H : Morphism O₄ O₃} {R : Retract O₂ O₄} (hR : R.Over G H)
    (p q : PullbackCarrier F G) :
    (pullback F H).SubclassOf ((baseChange F hR).sec.map p) ((baseChange F hR).sec.map q)
      ↔ (pullback F G).SubclassOf p q :=
  (baseChange F hR).subclassOf_iff

/-- **Base change of a retract is conservative for the instance relation.** -/
theorem baseChange_instanceOf_iff (F : Morphism O₁ O₃) {G : Morphism O₂ O₃}
    {H : Morphism O₄ O₃} {R : Retract O₂ O₄} (hR : R.Over G H)
    (p q : PullbackCarrier F G) :
    (pullback F H).InstanceOf ((baseChange F hR).sec.map p) ((baseChange F hR).sec.map q)
      ↔ (pullback F G).InstanceOf p q :=
  (baseChange F hR).instanceOf_iff

end Retract

/-! ## Splitting idempotents -/

/-- The sub-vocabulary of items **fixed** by a strict endomorphism. -/
def fixedVocabulary {O : Ontology I} (e : Morphism O O) : Set I := {x | e.map x = x}

/-- **Idempotents split.** An idempotent strict endomorphism `e` of an ontology
exhibits the sub-ontology of its fixed items as a retract; the associated
idempotent (`Ontology.Retract.idem`) is `e` again
(`Ontology.splitRetract_idem`). -/
def splitRetract {O : Ontology I} (e : Morphism O O) (he : ∀ x, e.map (e.map x) = e.map x) :
    Retract (O.subVocabulary (fixedVocabulary e)) O where
  sec := O.subVocabularyMorphism _
  ret :=
    { map := fun x => ⟨e.map x, he x⟩
      map_P279 := fun h => e.map_P279 h
      map_P31 := fun h => e.map_P31 h }
  ret_sec a := Subtype.ext a.2

@[simp] theorem splitRetract_idem {O : Ontology I} (e : Morphism O O)
    (he : ∀ x, e.map (e.map x) = e.map x) : (splitRetract e he).idem.map = e.map := rfl

/-- The fixed items of the idempotent of a retract are exactly the embedded
items: `Ontology.splitRetract` recovers the retract it came from. -/
theorem fixedVocabulary_idem {O₁ : Ontology I} {O₂ : Ontology J} (R : Retract O₁ O₂) :
    fixedVocabulary R.idem = Set.range R.sec.map := by
  ext x
  simpa [fixedVocabulary, eq_comm] using R.idem_fixed_iff x

/-- **`Ont` is idempotent complete** (Karoubian): every idempotent strict
endomorphism of an ontology splits, by `Ontology.splitRetract`. -/
instance isIdempotentComplete_Ont : IsIdempotentComplete Ont.{u} where
  idempotents_split X p hp := by
    have he : ∀ x, p.map (p.map x) = p.map x := fun x =>
      congrFun (congrArg Morphism.map hp) x
    refine ⟨⟨fixedVocabulary p, X.str.subVocabulary (fixedVocabulary p)⟩,
      (splitRetract p he).sec, (splitRetract p he).ret, ?_, ?_⟩
    · exact Morphism.ext' (funext fun a => (splitRetract p he).ret_sec a)
    · exact Morphism.ext' rfl

/-- A strict morphism between the underlying ontologies of two objects of `Ont`,
read as a morphism of `Ont`. -/
def toOntHom {X Y : Ont.{u}} (F : Morphism X.str Y.str) : X ⟶ Y := F

@[simp] theorem toOntHom_map {X Y : Ont.{u}} (F : Morphism X.str Y.str) :
    (toOntHom F).map = F.map := rfl

/-- An isomorphism of ontologies is an isomorphism of `Ont`. -/
def ontIso {X Y : Ont.{u}} (E : Isomorphism X.str Y.str) : X ≅ Y where
  hom := toOntHom E.hom
  inv := toOntHom E.inv
  hom_inv_id := Morphism.ext' (funext E.inv_hom)
  inv_hom_id := Morphism.ext' (funext E.hom_inv)

/-- Conversely, an isomorphism of `Ont` is an isomorphism of ontologies. -/
def isoToIsomorphism {X Y : Ont.{u}} (e : X ≅ Y) : Isomorphism X.str Y.str where
  hom := e.hom
  inv := e.inv
  inv_hom a := congrFun (congrArg Morphism.map e.hom_inv_id) a
  hom_inv b := congrFun (congrArg Morphism.map e.inv_hom_id) b

/-- The embedding of a retract is a **split monomorphism** in `Ont`. -/
def isSplitMono_sec (R : Retract X.str Y.str) : IsSplitMono (toOntHom R.sec) :=
  IsSplitMono.mk' { retraction := toOntHom R.ret, id := Morphism.ext' (funext R.ret_sec) }

/-- The retraction of a retract is a **split epimorphism** in `Ont`. -/
def isSplitEpi_ret (R : Retract X.str Y.str) : IsSplitEpi (toOntHom R.ret) :=
  IsSplitEpi.mk' { section_ := toOntHom R.sec, id := Morphism.ext' (funext R.ret_sec) }

/-- The embedding of a retract is a monomorphism. -/
theorem mono_sec (R : Retract X.str Y.str) : Mono (toOntHom R.sec) :=
  (mono_iff_injective _).2 R.sec_injective

/-- The retraction of a retract is an epimorphism. -/
theorem epi_ret (R : Retract X.str Y.str) : Epi (toOntHom R.ret) :=
  epi_of_surjective _ R.ret_surjective

/-! ## What the fibre product contains -/

namespace pullback

variable {O₁ : Ontology I} {O₂ : Ontology J} {O₃ : Ontology K} {O₄ : Ontology L}

/-- **The items of the fibre product are the matched items**: an item of `O₁`
comes from the fibre product exactly when the reference ontology sees it as an
item coming from `O₂` as well. -/
theorem range_fst (F : Morphism O₁ O₃) (G : Morphism O₂ O₃) :
    Set.range (fst F G).map = F.map ⁻¹' Set.range G.map := by
  ext a
  constructor
  · rintro ⟨p, rfl⟩; exact ⟨p.1.2, p.2.symm⟩
  · rintro ⟨b, hb⟩; exact ⟨⟨(a, b), hb.symm⟩, rfl⟩

/-- Symmetrically for the second projection. -/
theorem range_snd (F : Morphism O₁ O₃) (G : Morphism O₂ O₃) :
    Set.range (snd F G).map = G.map ⁻¹' Set.range F.map := by
  ext b
  constructor
  · rintro ⟨p, rfl⟩; exact ⟨p.1.1, p.2⟩
  · rintro ⟨a, ha⟩; exact ⟨⟨(a, b), ha⟩, rfl⟩

/-- **The fibre product of two sub-ontologies is their intersection**, at the
level of items: the matched items sit in the reference ontology exactly where
the two images meet. -/
theorem image_range_fst (F : Morphism O₁ O₃) (G : Morphism O₂ O₃) :
    F.map '' Set.range (fst F G).map = Set.range F.map ∩ Set.range G.map := by
  rw [range_fst, Set.image_preimage_eq_inter_range, Set.inter_comm]

/-- **The fibre product of two sub-vocabularies is the sub-vocabulary of their
intersection**: aligning two fragments of one ontology along their inclusions
keeps exactly the items they share, with exactly the statements they share. -/
def subVocabularyIso (O : Ontology I) (S T : Set I) :
    Isomorphism (pullback (O.subVocabularyMorphism S) (O.subVocabularyMorphism T))
      (O.subVocabulary (S ∩ T)) where
  hom :=
    { map := fun p => ⟨p.1.1.1, p.1.1.2, by
        have h : (p.1.1 : I) = (p.1.2 : I) := p.2
        rw [h]; exact p.1.2.2⟩
      map_P279 := fun h => h.1
      map_P31 := fun h => h.1 }
  inv :=
    { map := fun x => ⟨(⟨x.1, x.2.1⟩, ⟨x.1, x.2.2⟩), rfl⟩
      map_P279 := fun h => ⟨h, h⟩
      map_P31 := fun h => ⟨h, h⟩ }
  inv_hom p := Subtype.ext (Prod.ext (Subtype.ext rfl) (Subtype.ext p.2))
  hom_inv _ := rfl

/-- **The universal property as a bijection of morphism sets**: a strict
morphism into the fibre product *is* a compatible pair of strict morphisms.
This packages `Ontology.pullback.lift` and `Ontology.pullback.lift_unique`. -/
def homEquiv (F : Morphism O₁ O₃) (G : Morphism O₂ O₃) (O₀ : Ontology L) :
    Morphism O₀ (pullback F G) ≃
      {p : Morphism O₀ O₁ × Morphism O₀ O₂ // ∀ x, F.map (p.1.map x) = G.map (p.2.map x)} where
  toFun M := ⟨(M.comp (fst F G), M.comp (snd F G)), fun x => (M.map x).2⟩
  invFun p := lift F G p.1.1 p.1.2 p.2
  left_inv _ := Morphism.ext' rfl
  right_inv _ := Subtype.ext (Prod.ext (Morphism.ext' rfl) (Morphism.ext' rfl))

/-! ### Associativity -/

/-- **Iterated fibre products are fibre products** (the pasting law): matching
`O₄` against the fibre product of `O₁` and `O₂` over `O₃` is the same as matching
`O₄` directly against `O₁` over `O₃`, along the composite. -/
def assocIso (F : Morphism O₁ O₃) (G : Morphism O₂ O₃) (H : Morphism O₄ O₂) :
    Isomorphism (pullback (snd F G) H) (pullback F (H.comp G)) where
  hom :=
    { map := fun q => ⟨(q.1.1.1.1, q.1.2), by
        have h := q.1.1.2
        have h2 : q.1.1.1.2 = H.map q.1.2 := q.2
        simpa [Morphism.comp, h2] using h⟩
      map_P279 := fun h => ⟨h.1.1, h.2⟩
      map_P31 := fun h => ⟨h.1.1, h.2⟩ }
  inv :=
    { map := fun p => ⟨(⟨(p.1.1, H.map p.1.2), p.2⟩, p.1.2), rfl⟩
      map_P279 := fun h => ⟨⟨h.1, H.map_P279 h.2⟩, h.2⟩
      map_P31 := fun h => ⟨⟨h.1, H.map_P31 h.2⟩, h.2⟩ }
  inv_hom q := Subtype.ext (Prod.ext (Subtype.ext (Prod.ext rfl q.2.symm)) rfl)
  hom_inv _ := rfl

end pullback

/-- **A section is a kernel pair of itself**: the embedding of a retract is a
monomorphism, so the square with two identities on top is a pullback. -/
theorem Retract.isKernelPair_sec (R : Retract X.str Y.str) :
    IsKernelPair (toOntHom R.sec) (𝟙 X) (𝟙 X) :=
  have : Mono (toOntHom R.sec) := mono_sec R
  IsKernelPair.id_of_mono _

/-! ## Building small ontologies -/

/-- A `subclass of` relation that strictly decreases a natural-number rank has
no cycles, so it satisfies the antisymmetry law of an ontology.  (This is the
general form of the ad-hoc argument used for the counterexample of
`RequestProject.PullbackComparison`.) -/
theorem p279_antisymm_of_rank {P : I → I → Prop} (r : I → ℕ)
    (hr : ∀ a b, P a b → r b < r a) {a b : I} (hab : Relation.ReflTransGen P a b)
    (hba : Relation.ReflTransGen P b a) : a = b := by
  have key : ∀ {x y : I}, Relation.ReflTransGen P x y → r y ≤ r x := by
    intro x y hxy
    induction hxy with
    | refl => exact le_rfl
    | tail _ hcd ih => exact le_trans (le_of_lt (hr _ _ hcd)) ih
  rcases Relation.ReflTransGen.cases_tail hab with hba' | ⟨c, hac, hcb⟩
  · exact hba'.symm
  · exact absurd (key hba) (not_le.2 (lt_of_lt_of_le (hr _ _ hcb) (key hac)))

/-! ## Worked example: deduplicating an item is a retraction -/

namespace Duplicate

/-- The ontology of the example: item `0` is a class, and items `1` and `2` are
two *duplicate* subclasses of it — the same class entered twice, as happens
before a Wikidata item merge. -/
def dup : Ontology ℕ where
  P279 a b := (a = 1 ∨ a = 2) ∧ b = 0
  P31 _ _ := False
  level _ := 1
  level_P31 h := h.elim
  level_P279 _ := rfl
  P279_isClass _ := Nat.zero_lt_one
  P279_antisymm := p279_antisymm_of_rank (fun a => if a = 0 then 0 else 1)
    (by rintro a b ⟨ha | ha, rfl⟩ <;> subst ha <;> norm_num)

/-- **The merge**: the duplicate `2` is identified with `1`, everything else is
left alone.  It is a strict endomorphism of the ontology. -/
def merge : Morphism dup dup where
  map a := if a = 2 then 1 else a
  map_P279 := by
    rintro a b ⟨ha | ha, rfl⟩ <;> subst ha <;> exact ⟨Or.inl rfl, rfl⟩
  map_P31 h := h.elim

theorem merge_idem (x : ℕ) : merge.map (merge.map x) = merge.map x := by
  by_cases h : x = 2 <;> simp [merge, h]

/-- The items surviving the merge are exactly the non-duplicates. -/
theorem fixedVocabulary_merge : fixedVocabulary merge = {a : ℕ | a ≠ 2} := by
  ext a
  by_cases h : a = 2 <;> simp [fixedVocabulary, merge, h]

/-- **The deduplicated ontology is a retract of the ontology with the
duplicate.** -/
def mergeRetract : Retract (dup.subVocabulary (fixedVocabulary merge)) dup :=
  splitRetract merge merge_idem

/-- The class `1` survives the merge. -/
def one : (fixedVocabulary merge : Set ℕ) := ⟨1, by simp [fixedVocabulary, merge]⟩

/-- The class `0` survives the merge. -/
def zero : (fixedVocabulary merge : Set ℕ) := ⟨0, by simp [fixedVocabulary, merge]⟩

/-- The retraction sends the duplicate to the item it duplicates. -/
theorem ret_two : mergeRetract.ret.map 2 = one := rfl

/-- The surviving fragment says what it said before: `1` is a subclass of `0`
there exactly as in the ontology with the duplicate.  This is conservativity
(`Ontology.Retract.subclassOf_iff`) in a concrete case. -/
theorem subclassOf_one_zero :
    (dup.subVocabulary (fixedVocabulary merge)).SubclassOf one zero := by
  exact Relation.ReflTransGen.single (⟨Or.inl rfl, rfl⟩ : dup.P279 1 0)

/-- Nothing is lost: the duplicate `2` and its image `1` are subclasses of `0`
alike. -/
theorem subclassOf_two_zero : dup.SubclassOf 2 0 :=
  Relation.ReflTransGen.single ⟨Or.inr rfl, rfl⟩

end Duplicate

/-! ## Not every extension is a retract -/

namespace Gap

/-- Two classes, and nothing said about them. -/
def discrete : Ontology Bool where
  P279 _ _ := False
  P31 _ _ := False
  level _ := 1
  level_P31 h := h.elim
  level_P279 h := h.elim
  P279_isClass h := h.elim
  P279_antisymm := p279_antisymm_of_rank (fun _ => 0) (fun _ _ h => h.elim)

/-- The same two classes, with `true ⊂ false` asserted. -/
def linked : Ontology Bool where
  P279 x y := x = true ∧ y = false
  P31 _ _ := False
  level _ := 1
  level_P31 h := h.elim
  level_P279 _ := rfl
  P279_isClass _ := Nat.zero_lt_one
  P279_antisymm := p279_antisymm_of_rank (fun x => if x then 1 else 0)
    (by rintro a b ⟨rfl, rfl⟩; norm_num)

/-- The inclusion of the discrete ontology into the linked one. -/
def incl : Morphism discrete linked where
  map x := x
  map_P279 h := h.elim
  map_P31 h := h.elim

theorem discrete_subclassOf {a b : Bool} (h : discrete.SubclassOf a b) : a = b := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, -, hc⟩
  · exact h.symm
  · exact hc.elim

/-- **The linked ontology is not a retract of the discrete one**, in any way:
a retract would have to be conservative, but the linked ontology asserts a
`subclass of` statement that the discrete one does not. -/
theorem no_retract : IsEmpty (Retract discrete linked) := by
  refine ⟨fun R => ?_⟩
  have hbij : Function.Bijective R.sec.map :=
    (Finite.injective_iff_bijective).1 R.sec_injective
  obtain ⟨a, ha⟩ := hbij.2 true
  obtain ⟨b, hb⟩ := hbij.2 false
  have h : linked.SubclassOf (R.sec.map a) (R.sec.map b) := by
    rw [ha, hb]
    exact Relation.ReflTransGen.single ⟨rfl, rfl⟩
  have : a = b := discrete_subclassOf (R.subclassOf_iff.1 h)
  rw [this, hb] at ha
  exact Bool.noConfusion ha

/-- Since an isomorphism would in particular be a retract, the two ontologies
are not isomorphic either, although the inclusion is a bijection on items. -/
theorem no_iso : IsEmpty (Isomorphism discrete linked) :=
  ⟨fun E => no_retract.elim E.toRetract⟩

/-- The discrete ontology as an object of `Ont`. -/
abbrev discreteOnt : Ont.{0} := ⟨Bool, discrete⟩

/-- The linked ontology as an object of `Ont`. -/
abbrev linkedOnt : Ont.{0} := ⟨Bool, linked⟩

end Gap

/-- **A bijective strict morphism need not be an isomorphism**: the inclusion of
the discrete ontology into the linked one is the identity on items, but its
inverse map does not send the statement `true ⊂ false` anywhere, so it is not a
strict morphism.  This is the converse of `Ontology.bijective_of_isIso`, and it
fails. -/
theorem exists_bijective_not_isIso :
    ∃ (X Y : Ont.{0}) (F : X ⟶ Y), Function.Bijective F.map ∧ ¬ IsIso F := by
  refine ⟨Gap.discreteOnt, Gap.linkedOnt, Gap.incl, Function.bijective_id, fun h => ?_⟩
  exact Gap.no_iso.elim (isoToIsomorphism (X := Gap.discreteOnt) (Y := Gap.linkedOnt)
    (asIso (Gap.incl : Gap.discreteOnt ⟶ Gap.linkedOnt)))

/-- **Conservativity is a real constraint**: there is an injective strict
morphism of ontologies whose target is not a retract of its source, because the
larger ontology derives a `subclass of` fact that the smaller one does not. -/
theorem exists_no_retract :
    ∃ (I J : Type) (O₁ : Ontology I) (O₂ : Ontology J) (F : Morphism O₁ O₂),
      Function.Injective F.map ∧ IsEmpty (Retract O₁ O₂) :=
  ⟨Bool, Bool, Gap.discrete, Gap.linked, Gap.incl, fun _ _ h => h, Gap.no_retract⟩

end Ontology
end Wikidata
