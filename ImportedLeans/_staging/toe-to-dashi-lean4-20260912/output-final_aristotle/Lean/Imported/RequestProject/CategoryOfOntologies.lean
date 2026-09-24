import RequestProject.Reflection

/-!
# Category theory: the category of ontologies, and its pullbacks

*Wikidata: category theory (Q217413), category (Q719395), functor (Q864475),
pullback (Q1397439), limit (Q1322614), isomorphism (Q189112).*

`RequestProject.Reflection` builds the fibre product `Ontology.pullback` of two
ontologies over a third by hand, together with its two projections, the
commuting square and the universal property.  This file says what that
construction *is*: `Ont`, the category whose objects are ontologies (an item
type together with its `subclass of` / `instance of` structure) and whose
morphisms are the strict morphisms of `RequestProject.Reflection`, has pullbacks,
and `Ontology.pullback` is one — a `CategoryTheory.IsPullback` square in
Mathlib's own sense, hence a limit of the cospan.

Everything else in this development that is attached to the pullback —
the topology of `RequestProject.OntologyTopology`, the Grothendieck topology of
`RequestProject.GrothendieckSite`, the homotopy-theoretic reading of
`RequestProject.HomotopyTypes`, the cubes of `RequestProject.CubicalTypes`, the
automorphism groups of `RequestProject.OntologyGroups` and the `GF(2)`-linear
algebra of `RequestProject.OntologyFields` — is stated over this category.

Contents:

* `Ont` and `Ontology.ontCategory` — the category of ontologies and strict
  morphisms;
* `Ontology.forgetOnt` — the forgetful functor `Ont ⥤ Type`;
* `Ontology.isPullback_pbOnt` — the fibre product is a pullback square in `Ont`;
* `Ontology.hasPullback_ont`, `Ontology.instHasPullbacksOnt` — so `Ont` has all
  pullbacks;
* `Ontology.forgetOnt_isPullback` — the forgetful functor takes it to the
  pullback square of *sets*, so the items of the fibre product really are the
  matched pairs;
* `Ontology.pbSnd_injective_of_injective`, `Ontology.pbSnd_surjective_of_surjective`
  — base change along a pullback preserves injectivity and surjectivity of the
  underlying maps (the second is what makes the Grothendieck topology of
  `RequestProject.GrothendieckSite` a topology).
-/

open CategoryTheory CategoryTheory.Limits

namespace Wikidata
namespace Ontology

universe u v

/-- An **object of the category of ontologies**: a type of items together with
an ontology structure on it. -/
structure Ont : Type (u + 1) where
  /-- The type of items. -/
  carrier : Type u
  /-- The `subclass of` / `instance of` structure carried by those items. -/
  str : Ontology carrier

namespace Morphism

variable {I J : Type*} {O₁ : Ontology I} {O₂ : Ontology J}

/-- A strict morphism is determined by its underlying map: the remaining fields
are proofs. -/
theorem ext' {F G : Morphism O₁ O₂} (h : F.map = G.map) : F = G := by
  cases F; cases G; cases h; rfl

theorem ext_iff' {F G : Morphism O₁ O₂} : F = G ↔ F.map = G.map :=
  ⟨fun h => h ▸ rfl, ext'⟩

end Morphism

/-- **The category of ontologies.** Objects are ontologies, morphisms are the
strict morphisms of `RequestProject.Reflection`. -/
instance ontCategory : Category.{u, u + 1} Ont.{u} where
  Hom X Y := Morphism X.str Y.str
  id X := Morphism.id X.str
  comp F G := F.comp G
  id_comp _ := Morphism.ext' rfl
  comp_id _ := Morphism.ext' rfl
  assoc _ _ _ := Morphism.ext' rfl

@[simp] theorem ont_comp_map {X Y Z : Ont} (F : X ⟶ Y) (G : Y ⟶ Z) :
    (F ≫ G).map = G.map ∘ F.map := rfl

@[simp] theorem ont_id_map (X : Ont) : (𝟙 X : X ⟶ X).map = _root_.id := rfl

/-- **The forgetful functor** from ontologies to sets: an ontology has an
underlying type of items, and a strict morphism an underlying map. -/
def forgetOnt : Ont.{u} ⥤ Type u where
  obj X := X.carrier
  map F := F.map

@[simp] theorem forgetOnt_obj (X : Ont) : forgetOnt.obj X = X.carrier := rfl
@[simp] theorem forgetOnt_map {X Y : Ont} (F : X ⟶ Y) : forgetOnt.map F = F.map := rfl

/-- An isomorphism of ontologies has a bijective underlying map. -/
theorem bijective_of_isIso {X Y : Ont} (F : X ⟶ Y) [IsIso F] : Function.Bijective F.map := by
  have : IsIso (forgetOnt.map F) := inferInstance
  simpa [forgetOnt] using (isIso_iff_bijective (forgetOnt.map F)).1 this

/-! ## The fibre product as an object of `Ont` -/

variable {X Y Z : Ont.{u}}

/-- The fibre product of two ontologies, as an object of `Ont`. -/
def pbOnt (F : X ⟶ Z) (G : Y ⟶ Z) : Ont := ⟨PullbackCarrier F G, pullback F G⟩

@[simp] theorem pbOnt_carrier (F : X ⟶ Z) (G : Y ⟶ Z) :
    (pbOnt F G).carrier = PullbackCarrier F G := rfl

/-- The first projection out of the fibre product. -/
def pbFst (F : X ⟶ Z) (G : Y ⟶ Z) : pbOnt F G ⟶ X := pullback.fst F G

/-- The second projection out of the fibre product. -/
def pbSnd (F : X ⟶ Z) (G : Y ⟶ Z) : pbOnt F G ⟶ Y := pullback.snd F G

@[simp] theorem pbFst_map (F : X ⟶ Z) (G : Y ⟶ Z) (p : (pbOnt F G).carrier) :
    (pbFst F G).map p = p.1.1 := rfl

@[simp] theorem pbSnd_map (F : X ⟶ Z) (G : Y ⟶ Z) (p : (pbOnt F G).carrier) :
    (pbSnd F G).map p = p.1.2 := rfl

theorem pbOnt_condition (F : X ⟶ Z) (G : Y ⟶ Z) (p : (pbOnt F G).carrier) :
    F.map p.1.1 = G.map p.1.2 := p.2

/-- **The pullback square commutes**, in the category `Ont`. -/
theorem pb_commSq (F : X ⟶ Z) (G : Y ⟶ Z) : pbFst F G ≫ F = pbSnd F G ≫ G :=
  Morphism.ext' (pullback.comm F G)

/-- **The fibre product of ontologies is a pullback.** The square built in
`RequestProject.Reflection` is a `CategoryTheory.IsPullback` square: a limit of
the cospan `X ⟶ Z ⟵ Y` in the category of ontologies. -/
theorem isPullback_pbOnt (F : X ⟶ Z) (G : Y ⟶ Z) :
    IsPullback (pbFst F G) (pbSnd F G) F G := by
  refine IsPullback.of_isLimit
    (c := PullbackCone.mk (pbFst F G) (pbSnd F G) (pb_commSq F G)) ?_
  refine PullbackCone.IsLimit.mk _ (fun s => pullback.lift F G s.fst s.snd
      (fun x => congrFun (congrArg Morphism.map s.condition) x)) ?_ ?_ ?_
  · intro s; exact Morphism.ext' rfl
  · intro s; exact Morphism.ext' rfl
  · intro s m h1 h2
    exact Morphism.ext' (pullback.lift_unique F G m _ (congrArg Morphism.map h1)
      (congrArg Morphism.map h2))

/-- Every cospan of ontologies has a pullback. -/
instance hasPullback_ont (F : X ⟶ Z) (G : Y ⟶ Z) : HasPullback F G :=
  (isPullback_pbOnt F G).hasPullback

/-- **`Ont` has all pullbacks.** -/
instance instHasPullbacksOnt : HasPullbacks Ont.{u} := hasPullbacks_of_hasLimit_cospan _

/-- **The forgetful functor takes the pullback of ontologies to the pullback of
sets**: the items of the fibre product are exactly the matched pairs of items. -/
theorem forgetOnt_isPullback (F : X ⟶ Z) (G : Y ⟶ Z) :
    IsPullback (forgetOnt.map (pbFst F G)) (forgetOnt.map (pbSnd F G))
      (forgetOnt.map F) (forgetOnt.map G) := by
  have hcomm : forgetOnt.map (pbFst F G) ≫ forgetOnt.map F
      = forgetOnt.map (pbSnd F G) ≫ forgetOnt.map G := by
    funext p; exact p.2
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ hcomm) ?_
  refine PullbackCone.IsLimit.mk _
    (fun s x => (⟨(s.fst x, s.snd x), congrFun s.condition x⟩ : PullbackCarrier F G))
    (fun s => rfl) (fun s => rfl) ?_
  intro s m h1 h2
  funext x
  exact Subtype.ext (Prod.ext (congrFun h1 x) (congrFun h2 x))

/-! ## Base change preserves injectivity and surjectivity -/

/-- **Base change preserves injectivity**: if `F` is injective on items then so
is the projection of the fibre product onto the other factor. -/
theorem pbSnd_injective_of_injective (F : X ⟶ Z) (G : Y ⟶ Z)
    (hF : Function.Injective F.map) : Function.Injective (pbSnd F G).map := by
  rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ h
  have hb : b = b' := h
  subst hb
  have : a = a' := hF (by rw [hab, hab'])
  subst this
  rfl

/-- **Base change preserves surjectivity**: if `F` is surjective on items then so
is the projection of the fibre product onto the other factor.  This is the
stability of covers under pullback, and it is what makes the surjective families
of `RequestProject.GrothendieckSite` a Grothendieck topology. -/
theorem pbSnd_surjective_of_surjective (F : X ⟶ Z) (G : Y ⟶ Z)
    (hF : Function.Surjective F.map) : Function.Surjective (pbSnd F G).map := by
  intro b
  obtain ⟨a, ha⟩ := hF (G.map b)
  exact ⟨⟨(a, b), ha⟩, rfl⟩

/-- Symmetrically for the first projection. -/
theorem pbFst_surjective_of_surjective (F : X ⟶ Z) (G : Y ⟶ Z)
    (hG : Function.Surjective G.map) : Function.Surjective (pbFst F G).map := by
  intro a
  obtain ⟨b, hb⟩ := hG (F.map a)
  exact ⟨⟨(a, b), hb.symm⟩, rfl⟩

end Ontology
end Wikidata
