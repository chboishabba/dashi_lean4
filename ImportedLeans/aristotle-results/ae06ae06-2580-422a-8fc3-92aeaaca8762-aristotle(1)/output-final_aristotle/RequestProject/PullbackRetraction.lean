import RequestProject.CategoryOfOntologies

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
* `Ontology.mono_iff_injective`, `Ontology.epi_of_surjective` — the categorical
  and the set-theoretic readings of "no two items are merged" agree, so
  `Ontology.pbSnd_injective_of_injective` really is the statement that
  monomorphisms are stable under base change.
* `Ontology.pbFst_injective_of_injective` — the missing companion of the base
  change results of `RequestProject.CategoryOfOntologies`.

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
  ⟨Function.LeftInverse.injective E.inv_hom, Function.RightInverse.surjective E.inv_hom⟩

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
  inv_hom p := Subtype.ext (Prod.ext rfl p.2.symm)
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

/-! ## Monomorphisms, epimorphisms and base change -/

/-- The **discrete one-item ontology**: a single item and no statements. -/
def point : Ontology PUnit.{u + 1} where
  P279 _ _ := False
  P31 _ _ := False
  level _ := 0
  level_P31 h := h.elim
  level_P279 h := h.elim
  P279_isClass h := h.elim
  P279_antisymm _ _ := rfl

/-- Every choice of an item is a strict morphism out of the one-item ontology. -/
def pointMorphism {O : Ontology I} (a : I) : Morphism point O where
  map _ := a
  map_P279 h := h.elim
  map_P31 h := h.elim

variable {X Y Z : Ont.{u}}

/-- **A strict morphism is a monomorphism exactly when it is injective on
items.** -/
theorem mono_iff_injective (F : X ⟶ Y) : Mono F ↔ Function.Injective F.map := by
  constructor
  · intro _ a b hab
    have h : (pointMorphism (O := X.str) a : Morphism point X.str).comp F
        = (pointMorphism (O := X.str) b).comp F := Morphism.ext' (by funext _; exact hab)
    have := (cancel_mono (f := F) (g := (⟨PUnit, point⟩ : Ont.{u}) ⟶ X)
      (h := pointMorphism (O := X.str) a) (i := pointMorphism (O := X.str) b)).1 h
    exact congrFun (congrArg Morphism.map this) PUnit.unit
  · intro hF
    refine ⟨fun {W} G H hGH => Morphism.ext' ?_⟩
    funext x
    exact hF (congrFun (congrArg Morphism.map hGH) x)

/-- A morphism surjective on items is an epimorphism. -/
theorem epi_of_surjective (F : X ⟶ Y) (hF : Function.Surjective F.map) : Epi F := by
  refine ⟨fun {W} G H hGH => Morphism.ext' ?_⟩
  funext y
  obtain ⟨x, rfl⟩ := hF y
  exact congrFun (congrArg Morphism.map hGH) x

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

/-- The embedding of a retract is a **split monomorphism** in `Ont`. -/
def isSplitMono_sec (R : Retract X.str Y.str) : IsSplitMono (R.sec : X ⟶ Y) :=
  IsSplitMono.mk' { retraction := R.ret, id := Morphism.ext' (funext R.ret_sec) }

/-- The retraction of a retract is a **split epimorphism** in `Ont`. -/
def isSplitEpi_ret (R : Retract X.str Y.str) : IsSplitEpi (R.ret : Y ⟶ X) :=
  IsSplitEpi.mk' { section_ := R.sec, id := Morphism.ext' (funext R.ret_sec) }

/-- The embedding of a retract is a monomorphism. -/
theorem mono_sec (R : Retract X.str Y.str) : Mono (R.sec : X ⟶ Y) :=
  (mono_iff_injective _).2 R.sec_injective

/-- The retraction of a retract is an epimorphism. -/
theorem epi_ret (R : Retract X.str Y.str) : Epi (R.ret : Y ⟶ X) :=
  epi_of_surjective _ R.ret_surjective

end Ontology
end Wikidata
