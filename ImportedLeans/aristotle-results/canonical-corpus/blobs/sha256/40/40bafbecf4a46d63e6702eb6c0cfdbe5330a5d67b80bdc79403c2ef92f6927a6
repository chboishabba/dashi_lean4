import RequestProject.PullbackRetraction
import RequestProject.PullbackComparison

/-!
# Retractions, topologically

*Wikidata: retract (Q2914389), retraction (Q7317797), topological embedding
(Q1191129), quotient map (Q1264701), Alexandrov topology (Q3532117).*

`RequestProject.OntologyTopology` gives every ontology the Alexandrov topology of
its `subclass of` order — the item space — and makes strict morphisms continuous.
`RequestProject.PullbackRetraction` develops retracts of ontologies.  This file
puts the two together: **a retract of ontologies is a retract of item spaces**.

* `Ontology.Retract.isEmbedding_sec` — the section is a topological embedding, so
  the item space of the small ontology carries exactly the subspace topology of
  its image;
* `Ontology.Retract.specializes_iff` — under that embedding, specialization in
  the big item space is exactly the `subclass of` order of the small one: the
  topological form of conservativity;
* `Ontology.Retract.isQuotientMap_ret` — the retraction is a quotient map;
* `Ontology.exists_retract_ret_not_isOpenMap` — but it need not be an *open* map,
  so "retract" is strictly weaker than the open-quotient picture: an isolated
  item of the big ontology may be sent to a class that has a subclass;
* `Ontology.Retract.isSplitMono_ontTop_sec`,
  `Ontology.Retract.isSplitEpi_ontTop_ret` — the images under the functor
  `Ontology.ontTop : Ont ⥤ TopCat` are a split monomorphism and a split
  epimorphism of spaces.
-/

open CategoryTheory Topology

namespace Wikidata
namespace Ontology
namespace Retract

universe u

variable {I J : Type*} {O₁ : Ontology I} {O₂ : Ontology J} (R : Retract O₁ O₂)

/-- The section of a retract, as a map of item spaces, is continuous. -/
theorem continuous_sec : Continuous R.sec.toItemMap := R.sec.continuous_toItemMap

/-- The retraction of a retract, as a map of item spaces, is continuous. -/
theorem continuous_ret : Continuous R.ret.toItemMap := R.ret.continuous_toItemMap

/-- The retraction undoes the section on item spaces. -/
theorem leftInverse_ret_sec : Function.LeftInverse R.ret.toItemMap R.sec.toItemMap :=
  R.ret_sec

/-- **The item space of a retract is a topological retract**: the section is a
topological embedding, so the small item space is the subspace of the big one
carried by the embedded items. -/
theorem isEmbedding_sec : IsEmbedding R.sec.toItemMap :=
  IsEmbedding.of_leftInverse R.leftInverse_ret_sec R.continuous_ret R.continuous_sec

/-- **Conservativity, topologically**: between embedded items, specialization in
the big item space is exactly the `subclass of` order of the small ontology. -/
theorem specializes_iff (a b : I) :
    R.sec.toItemMap b ⤳ R.sec.toItemMap a ↔ O₁.SubclassOf b a := by
  rw [show R.sec.toItemMap b = toItemSpace O₂ (R.sec.map b) from rfl,
    show R.sec.toItemMap a = toItemSpace O₂ (R.sec.map a) from rfl,
    specializes_iff_subclassOf]
  exact R.subclassOf_iff

/-- **The retraction is a quotient map** of item spaces: it is continuous and has
a continuous section. -/
theorem isQuotientMap_ret : IsQuotientMap R.ret.toItemMap :=
  IsQuotientMap.of_inverse R.continuous_sec R.continuous_ret R.leftInverse_ret_sec

variable {X Y : Ont.{u}}

/-- The section of a retract becomes a split monomorphism of spaces. -/
def isSplitMono_ontTop_sec (R : Retract X.str Y.str) :
    IsSplitMono (ontTop.map (toOntHom R.sec)) :=
  IsSplitMono.mk' ((isSplitMono_sec R).exists_splitMono.some.map ontTop)

/-- The retraction of a retract becomes a split epimorphism of spaces. -/
def isSplitEpi_ontTop_ret (R : Retract X.str Y.str) :
    IsSplitEpi (ontTop.map (toOntHom R.ret)) :=
  IsSplitEpi.mk' ((isSplitEpi_ret R).exists_splitEpi.some.map ontTop)

end Retract

/-! ## A retraction need not be an open map -/

namespace Orphan

/-- An ontology with one `subclass of` statement, `1 ⊂ 0`, and an isolated item
`2` about which nothing is said. -/
def big : Ontology ℕ where
  P279 a b := a = 1 ∧ b = 0
  P31 _ _ := False
  level _ := 1
  level_P31 h := h.elim
  level_P279 _ := rfl
  P279_isClass _ := Nat.zero_lt_one
  P279_antisymm := p279_antisymm_of_rank (fun a => if a = 0 then 0 else 1)
    (by rintro a b ⟨rfl, rfl⟩; norm_num)

/-- The idempotent that absorbs the isolated item `2` into the class `0`. -/
def absorb : Morphism big big where
  map a := if a = 2 then 0 else a
  map_P279 := by rintro a b ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
  map_P31 h := h.elim

theorem absorb_idem (x : ℕ) : absorb.map (absorb.map x) = absorb.map x := by
  by_cases h : x = 2 <;> simp [absorb, h]

/-- The retract it splits into: the items other than `2`. -/
def retract : Retract (big.subVocabulary (fixedVocabulary absorb)) big :=
  splitRetract absorb absorb_idem

theorem mem_fixed {a : ℕ} (h : a ≠ 2) : a ∈ fixedVocabulary absorb := by
  simp [fixedVocabulary, absorb, h]

/-- Nothing is a subclass of the isolated item `2`. -/
theorem subclassOf_two {b : ℕ} (h : big.SubclassOf b 2) : b = 2 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, -, hc⟩
  · exact h.symm
  · exact absurd hc.2 (by norm_num)

/-- `{2}` is open in the big item space: the isolated item has no subclasses. -/
theorem isOpen_singleton_two : IsOpen ({toItemSpace big 2} : Set (ItemSpace big)) := by
  rw [isOpen_itemSpace_iff]
  rintro a b ha hba
  simp only [Set.mem_singleton_iff] at ha ⊢
  subst ha
  exact subclassOf_two hba

/-- Its image under the retraction is the singleton `{0}` of the small item
space. -/
theorem image_singleton_two :
    retract.ret.toItemMap '' ({toItemSpace big 2} : Set (ItemSpace big))
      = {(⟨0, mem_fixed (by norm_num)⟩ : (fixedVocabulary absorb : Set ℕ))} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    exact Subtype.ext rfl
  · intro hx
    simp only [Set.mem_singleton_iff] at hx
    exact ⟨toItemSpace big 2, rfl, by rw [hx]; exact Subtype.ext rfl⟩

/-- But `{0}` is not open in the small item space: `1` is a subclass of `0` and
survives the retraction. -/
theorem not_isOpen_image :
    ¬ IsOpen (retract.ret.toItemMap '' ({toItemSpace big 2} : Set (ItemSpace big))) := by
  rw [image_singleton_two, isOpen_itemSpace_iff]
  intro h
  have h1 : (big.subVocabulary (fixedVocabulary absorb)).SubclassOf
      ⟨1, mem_fixed (by norm_num)⟩ ⟨0, mem_fixed (by norm_num)⟩ :=
    Relation.ReflTransGen.single ⟨rfl, rfl⟩
  have := h (Set.mem_singleton _) h1
  simp only [Set.mem_singleton_iff] at this
  exact absurd (congrArg Subtype.val this) (by norm_num)

end Orphan

/-- **A retraction of ontologies need not be an open map of item spaces**, even
though it is always a continuous quotient map: absorbing an item about which
nothing is said into a class that has a subclass turns an open singleton into a
non-open one. -/
theorem exists_retract_ret_not_isOpenMap :
    ∃ (I J : Type) (O₁ : Ontology I) (O₂ : Ontology J) (R : Retract O₁ O₂),
      ¬ IsOpenMap R.ret.toItemMap :=
  ⟨_, _, _, _, Orphan.retract, fun h =>
    Orphan.not_isOpen_image (h _ Orphan.isOpen_singleton_two)⟩

end Ontology
end Wikidata
