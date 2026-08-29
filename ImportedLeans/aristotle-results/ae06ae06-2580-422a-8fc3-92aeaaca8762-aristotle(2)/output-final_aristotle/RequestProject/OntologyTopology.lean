import RequestProject.CategoryOfOntologies

/-!
# Topology: the class hierarchy as a space, and the pullback as a fibre product of spaces

*Wikidata: topology (Q42989), topological space (Q179899), Alexandrov topology
(Q3532117), open set (Q213363), continuous function (Q170058), pullback
(Q1397439).*

A `subclass of` hierarchy is a partial order (`Ontology.subclassPartialOrder`),
and every partial order carries a topology: a set of items is **open** when it
is closed under passing to subclasses.  So an ontology *is* a space,
`Ontology.ItemSpace`, whose points are its items, whose open sets are the
downward-closed families of classes, and whose smallest open neighbourhood of a
class `a` is the set `Ontology.downSet` of all subclasses of `a`.  Arbitrary
intersections of open sets are open, so the space is Alexandrov-discrete.

The point of the file is the pullback.  A strict morphism of ontologies is
exactly a continuous map of item spaces (`Ontology.continuous_iff_subclass`), so
the fibre product of `RequestProject.Reflection` has a topological shadow, and
the two are compared here:

* `Ontology.isPullback_topCat` — the matched pairs, topologized as a subspace of
  the product, are the pullback of the item spaces **in `TopCat`**;
* `Ontology.continuous_pbCompare`, `Ontology.bijective_pbCompare` — the item
  space of the ontology-level fibre product has the same points, and its
  topology refines the subspace topology (`Ontology.isOpen_of_isOpen_subspace`):
  a matched pair has *fewer* subclasses inside the fibre product than the two
  components have separately, because a subclass step must be taken on both
  sides at once.  `RequestProject.PullbackComparison` shows the refinement is
  strict in general: the comparison map is a homeomorphism exactly when
  componentwise chains can be run simultaneously, and there is a cospan where
  they cannot.

Also proved: item spaces are `T0` (`Ontology.instT0SpaceItemSpace`), which is the
topological face of the antisymmetry axiom `P279_antisymm` of `Wikidata.Ontology`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Wikidata
namespace Ontology

universe u

variable {I J K : Type*}

/-! ## The Alexandrov topology of a class hierarchy -/

/-- **The topology of an ontology.** A set of items is open when every subclass
of a member is a member: the Alexandrov topology of the `subclass of` order. -/
def subclassTopology (O : Ontology I) : TopologicalSpace I where
  IsOpen U := ∀ ⦃a b⦄, a ∈ U → O.SubclassOf b a → b ∈ U
  isOpen_univ := by intro a b _ _; trivial
  isOpen_inter := by
    intro s t hs ht a b hab hba
    exact ⟨hs hab.1 hba, ht hab.2 hba⟩
  isOpen_sUnion := by
    rintro S hS a b ⟨t, ht, hat⟩ hba
    exact ⟨t, ht, hS t ht hat hba⟩

/-- **The item space of an ontology**: its items, topologized by
`Ontology.subclassTopology`. -/
def ItemSpace (_O : Ontology I) : Type _ := I

instance instTopologicalSpaceItemSpace (O : Ontology I) : TopologicalSpace (ItemSpace O) :=
  subclassTopology O

/-- An item, viewed as a point of the item space. -/
def toItemSpace (O : Ontology I) (a : I) : ItemSpace O := a

theorem isOpen_itemSpace_iff {O : Ontology I} (U : Set (ItemSpace O)) :
    IsOpen U ↔ ∀ ⦃a b⦄, a ∈ U → O.SubclassOf b a → b ∈ U := Iff.rfl

/-- Arbitrary intersections of open sets are open: the item space is
Alexandrov-discrete. -/
instance instAlexandrovDiscreteItemSpace (O : Ontology I) : AlexandrovDiscrete (ItemSpace O) where
  isOpen_sInter S hS := by
    intro a b ha hba t ht
    exact hS t ht (ha t ht) hba

/-- The subclasses of a class, as a subset of the item space. -/
def downSet (O : Ontology I) (a : I) : Set (ItemSpace O) := {b | O.SubclassOf b a}

@[simp] theorem mem_downSet {O : Ontology I} {a b : I} :
    b ∈ downSet O a ↔ O.SubclassOf b a := Iff.rfl

theorem isOpen_downSet (O : Ontology I) (a : I) : IsOpen (downSet O a) :=
  fun _ _ hx hyx => subclassOf_trans hyx hx

theorem self_mem_downSet (O : Ontology I) (a : I) : a ∈ downSet O a := subclassOf_refl a

/-- `downSet O a` is the smallest open set containing `a`. -/
theorem downSet_subset_of_isOpen {O : Ontology I} {U : Set (ItemSpace O)} (hU : IsOpen U)
    {a : I} (ha : a ∈ U) : downSet O a ⊆ U := fun _ hb => hU ha hb

/-- **Continuity is monotonicity for the class hierarchy.** -/
theorem continuous_iff_subclass {O₁ : Ontology I} {O₂ : Ontology J}
    (f : ItemSpace O₁ → ItemSpace O₂) :
    Continuous f ↔ ∀ ⦃a b : I⦄, O₁.SubclassOf b a → O₂.SubclassOf (f b) (f a) := by
  constructor
  · intro hf a b hba
    have hopen : IsOpen (f ⁻¹' downSet O₂ (f a)) := (isOpen_downSet O₂ (f a)).preimage hf
    exact hopen (self_mem_downSet O₂ (f a)) hba
  · intro hf
    constructor
    intro U hU a b ha hba
    exact hU ha (hf hba)

/-- The map of item spaces underlying a strict morphism. -/
def Morphism.toItemMap {O₁ : Ontology I} {O₂ : Ontology J} (F : Morphism O₁ O₂) :
    ItemSpace O₁ → ItemSpace O₂ := F.map

/-- **A strict morphism of ontologies is a continuous map of item spaces.** -/
theorem Morphism.continuous_toItemMap {O₁ : Ontology I} {O₂ : Ontology J} (F : Morphism O₁ O₂) :
    Continuous F.toItemMap :=
  (continuous_iff_subclass F.toItemMap).2 fun _ _ h => F.subclassOf h

/-- The continuous map of item spaces underlying a strict morphism. -/
def Morphism.toContinuousMap {O₁ : Ontology I} {O₂ : Ontology J} (F : Morphism O₁ O₂) :
    C(ItemSpace O₁, ItemSpace O₂) := ⟨F.toItemMap, F.continuous_toItemMap⟩

/-- **Item spaces are `T0`** — the topological reading of the antisymmetry of the
class hierarchy. -/
instance instT0SpaceItemSpace (O : Ontology I) : T0Space (ItemSpace O) := by
  refine ⟨fun a b hab => ?_⟩
  have h₁ : (b : ItemSpace O) ∈ downSet O a :=
    (hab.mem_open_iff (isOpen_downSet O a)).1 (self_mem_downSet O a)
  have h₂ : (a : ItemSpace O) ∈ downSet O b :=
    (hab.mem_open_iff (isOpen_downSet O b)).2 (self_mem_downSet O b)
  exact subclassOf_antisymm h₂ h₁

/-! ## The topological functor -/

/-- Ontologies and strict morphisms, seen as topological spaces and continuous
maps. -/
def ontTop : Ont.{u} ⥤ TopCat.{u} where
  obj X := TopCat.of (ItemSpace X.str)
  map F := TopCat.ofHom F.toContinuousMap
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem ontTop_map_apply {X Y : Ont} (F : X ⟶ Y) (a : ItemSpace X.str) :
    (ontTop.map F).hom a = F.map a := rfl

/-! ## The pullback, topologically -/

variable {X Y Z : Ont.{u}}

/-- **The pullback of item spaces**: matched pairs, as a subspace of the product
of the two item spaces. -/
def PullbackSpace (F : X ⟶ Z) (G : Y ⟶ Z) : Type u :=
  {p : ItemSpace X.str × ItemSpace Y.str // F.map p.1 = G.map p.2}

instance instTopologicalSpacePullbackSpace (F : X ⟶ Z) (G : Y ⟶ Z) :
    TopologicalSpace (PullbackSpace F G) := instTopologicalSpaceSubtype

/-- **The topological fibre product is a pullback in `TopCat`.** -/
theorem isPullback_topCat (F : X ⟶ Z) (G : Y ⟶ Z) :
    IsPullback (TopCat.pullbackFst (ontTop.map F) (ontTop.map G))
      (TopCat.pullbackSnd (ontTop.map F) (ontTop.map G)) (ontTop.map F) (ontTop.map G) :=
  IsPullback.of_isLimit (TopCat.pullbackConeIsLimit (ontTop.map F) (ontTop.map G))

/-- The comparison map: an item of the ontology-level fibre product is a point of
the topological fibre product. -/
def pbCompare (F : X ⟶ Z) (G : Y ⟶ Z) : ItemSpace (pullback F G) → PullbackSpace F G :=
  fun p => ⟨(p.1.1, p.1.2), p.2⟩

/-- The comparison map is a bijection: both sides have the matched pairs as
points. -/
theorem bijective_pbCompare (F : X ⟶ Z) (G : Y ⟶ Z) : Function.Bijective (pbCompare F G) := by
  constructor
  · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ h
    have h1 : a = a' := congrArg (fun q => q.1.1) h
    have h2 : b = b' := congrArg (fun q => q.1.2) h
    subst h1; subst h2; rfl
  · rintro ⟨⟨a, b⟩, hab⟩
    exact ⟨⟨(a, b), hab⟩, rfl⟩

/-- **The comparison map is continuous**: the topology of the ontology-level
fibre product refines the topology of the topological fibre product. -/
theorem continuous_pbCompare (F : X ⟶ Z) (G : Y ⟶ Z) : Continuous (pbCompare F G) := by
  refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
  · exact (pullback.fst F G).continuous_toItemMap
  · exact (pullback.snd F G).continuous_toItemMap

/-- Spelled out: every set that is open in the subspace topology of the matched
pairs is open in the topology of the fibre-product ontology. -/
theorem isOpen_of_isOpen_subspace (F : X ⟶ Z) (G : Y ⟶ Z) {U : Set (PullbackSpace F G)}
    (hU : IsOpen U) : IsOpen (pbCompare F G ⁻¹' U) := hU.preimage (continuous_pbCompare F G)

/-- The two projections of the topological fibre product are continuous, and the
square commutes. -/
theorem pullbackSpace_comm (F : X ⟶ Z) (G : Y ⟶ Z) (p : PullbackSpace F G) :
    F.map p.1.1 = G.map p.1.2 := p.2

end Ontology
end Wikidata
