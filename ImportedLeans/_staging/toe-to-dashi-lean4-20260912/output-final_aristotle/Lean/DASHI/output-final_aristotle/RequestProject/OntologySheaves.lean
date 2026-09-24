import RequestProject.GrothendieckSite

/-!
# Labellings are a sheaf on the site of ontologies

`RequestProject.GrothendieckSite` makes `Ont` into a site: the covering families
are the jointly surjective ones, the families of alignments that between them
name every item of their target.  A site is only useful once something is
*sheafified* over it, so this file supplies the first sheaf.

For a fixed type `S` of labels — think of the language codes of a label, or of
the values of an external identifier — an ontology `X` has the type
`X.carrier → S` of **labellings**, and an alignment `f : Y ⟶ X` pulls a
labelling of `X` back to a labelling of `Y`.  That is a presheaf on `Ont`,
`Ontology.funPresheaf S`, and it is a sheaf:

* `Ontology.isSheafFor_funPresheaf` — a family of labellings of the members of a
  covering family that agree wherever two members meet (that is: a *compatible*
  family, the agreement being tested on fibre products, which is what
  `RequestProject.Reflection` built) comes from exactly one labelling of the
  target;
* `Ontology.isSheaf_funPresheaf` — hence `funPresheaf S` is a sheaf for the
  Grothendieck topology `Ontology.ontologyTopology`, and
  `Ontology.funSheaf` packages it as an object of the category of sheaves of
  types on the site.

A map of label types is a morphism of the corresponding sheaves
(`Ontology.funPresheafMap`), naturally in the ontology, and this assignment is
functorial (`funPresheafMap_id`, `funPresheafMap_comp`).
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace Wikidata
namespace Ontology

universe u v

/-! ### The presheaf of labellings -/

/-- **The presheaf of `S`-valued labellings**: an ontology is sent to the
labellings of its items, an alignment to the pullback of labellings along it. -/
def funPresheaf (S : Type v) : Ont.{u}ᵒᵖ ⥤ Type (max u v) where
  obj X := X.unop.carrier → S
  map f g := g ∘ f.unop.map

@[simp] theorem funPresheaf_obj (S : Type v) (X : Ont.{u}ᵒᵖ) :
    (funPresheaf.{u, v} S).obj X = (X.unop.carrier → S) := rfl

@[simp] theorem funPresheaf_map (S : Type v) {X Y : Ont.{u}ᵒᵖ} (f : X ⟶ Y)
    (g : X.unop.carrier → S) : (funPresheaf.{u, v} S).map f g = g ∘ f.unop.map := rfl

/-! ### The sheaf condition -/

/-- **A compatible family of labellings over a covering family glues, uniquely.**
Existence uses that the family names every item; uniqueness uses it again.  That
a labelling is well defined where two members of the family overlap is exactly
the compatibility of the family, tested on the fibre product of the two
alignments. -/
theorem isSheafFor_funPresheaf {X : Ont.{u}} (S : Type v) (R : Presieve X)
    (hR : IsJointlySurjective R) : Presieve.IsSheafFor (funPresheaf.{u, v} S) R := by
  intro x hx
  choose Y f hf y hy using hR
  refine ⟨fun a => x (f a) (hf a) (y a), ?_, ?_⟩
  · -- it is an amalgamation
    intro W g hg
    funext w
    have hcomm : pbFst (f (g.map w)) g ≫ f (g.map w) = pbSnd (f (g.map w)) g ≫ g :=
      pb_commSq (f (g.map w)) g
    have hcompat := hx (pbFst (f (g.map w)) g) (pbSnd (f (g.map w)) g)
      (hf (g.map w)) hg hcomm
    have hp : (f (g.map w)).map (y (g.map w)) = g.map w := hy (g.map w)
    have := congrFun hcompat (⟨(y (g.map w), w), hp⟩ : (pbOnt (f (g.map w)) g).carrier)
    simpa [funPresheaf] using this
  · -- and it is the only one
    intro t ht
    funext a
    have h1 : t ((f a).map (y a)) = x (f a) (hf a) (y a) := congrFun (ht (f a) (hf a)) (y a)
    have h2 : (f a).map (y a) = a := hy a
    rw [h2] at h1
    exact h1

/-- **The labellings form a sheaf on the site of ontologies.** -/
theorem isSheaf_funPresheaf (S : Type v) :
    Presieve.IsSheaf ontologyTopology.{u} (funPresheaf.{u, v} S) :=
  (Presieve.isSheaf_pretopology surjectivePretopology.{u}).2
    fun R hR => isSheafFor_funPresheaf S R hR

/-- The sheaf of `S`-valued labellings, as an object of the category of sheaves
of types on the site of ontologies. -/
def funSheaf (S : Type v) : Sheaf ontologyTopology.{u} (Type (max u v)) :=
  ⟨funPresheaf.{u, v} S, (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_funPresheaf S)⟩

@[simp] theorem funSheaf_val (S : Type v) :
    (funSheaf.{u, v} S).val = funPresheaf.{u, v} S := rfl

/-! ### Functoriality in the labels -/

/-- Relabelling: a map of label types induces a morphism of the presheaves of
labellings, natural in the ontology. -/
def funPresheafMap {S T : Type v} (u : S → T) : funPresheaf.{u, v} S ⟶ funPresheaf.{u, v} T where
  app _ g := u ∘ g

@[simp] theorem funPresheafMap_app {S T : Type v} (u : S → T) (X : Ont.{u}ᵒᵖ)
    (g : X.unop.carrier → S) : (funPresheafMap.{u, v} u).app X g = u ∘ g := rfl

@[simp] theorem funPresheafMap_id (S : Type v) :
    funPresheafMap.{u, v} (id : S → S) = 𝟙 (funPresheaf.{u, v} S) := rfl

@[simp] theorem funPresheafMap_comp {S T U : Type v} (u : S → T) (w : T → U) :
    funPresheafMap.{u, v} (w ∘ u) = funPresheafMap.{u, v} u ≫ funPresheafMap.{u, v} w := rfl

/-- Relabelling is a morphism of sheaves. -/
def funSheafMap {S T : Type v} (u : S → T) : funSheaf.{u, v} S ⟶ funSheaf.{u, v} T :=
  ⟨funPresheafMap.{u, v} u⟩

end Ontology
end Wikidata
