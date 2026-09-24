import RequestProject.CategoryOfOntologies

/-!
# Field theory: class extensions as a vector space over `GF(2)`, and the pullback

*Wikidata: field theory (Q903820), field (Q190109), F₂ (Q5513324), vector space
(Q125977), linear map (Q207643), pullback (Q1397439).*

The extension of a class is a set of items, and the sets of items of a fixed
ontology form a Boolean algebra.  Read over the two-element **field** `GF(2)`
this is linear algebra: a set of items is its indicator function
`Ontology.chi`, symmetric difference is addition and intersection is
multiplication (`Ontology.chi_symmDiff`, `Ontology.chi_inter`), so the
extensions of an ontology form a `GF(2)`-**vector space** `Ontology.ExtSpace`.

Strict morphisms act on that space contravariantly: pulling a set of items back
along `F` is precomposition with `F`, a **linear map** `Ontology.comapLin`
(`Ontology.chi_pull`).  The pullback square of ontologies therefore casts a
linear shadow:

* `Ontology.comapLin_pb_comm` — the square of `GF(2)`-linear maps obtained from
  the fibre product commutes;
* `Ontology.extPullbackSubmodule` — the fibre product of two vector spaces over a
  third, with its universal property (`Ontology.extPullback_lift_apply`,
  `Ontology.extPullback_lift_unique`);
* `Ontology.toExtPullback` — the linear map from the extensions of the reference
  ontology into that fibre product, and `Ontology.injective_toExtPullback`: it is
  injective as soon as one of the two alignments is surjective on items, i.e.
  as soon as the reference ontology is covered.
-/

open CategoryTheory

namespace Wikidata
namespace Ontology

universe u

/-- The two-element field, the coefficients used for class extensions. -/
abbrev GF2 : Type := ZMod 2

example : Field GF2 := inferInstance

variable {I J : Type*}

/-! ## Extensions as vectors -/

/-- **The space of class extensions** of an ontology: `GF(2)`-valued functions on
its items, i.e. indicator functions of sets of items. -/
abbrev ExtSpace (_O : Ontology I) : Type _ := I → GF2

/-- **The extensions form a free `GF(2)`-vector space**: Wikidata's claim that a
vector space is a free module, for this one. -/
example (O : Ontology I) : Module.Free GF2 (ExtSpace O) := inferInstance

/-- The indicator vector of a set of items. -/
noncomputable def chi {O : Ontology I} (A : Set I) : ExtSpace O := A.indicator 1

theorem chi_of_mem {O : Ontology I} {A : Set I} {a : I} (ha : a ∈ A) :
    (chi (O := O) A) a = 1 := Set.indicator_of_mem ha _

theorem chi_of_not_mem {O : Ontology I} {A : Set I} {a : I} (ha : a ∉ A) :
    (chi (O := O) A) a = 0 := Set.indicator_of_notMem ha _

/-- **Symmetric difference is addition** in the `GF(2)`-space of extensions. -/
theorem chi_symmDiff {O : Ontology I} (A B : Set I) :
    chi (O := O) (symmDiff A B) = chi (O := O) A + chi (O := O) B := by
  funext a
  simp only [Pi.add_apply]
  by_cases hA : a ∈ A <;> by_cases hB : a ∈ B
  · rw [chi_of_not_mem (by simp [Set.mem_symmDiff, hA, hB]), chi_of_mem hA, chi_of_mem hB]
    decide
  · rw [chi_of_mem (by simp [Set.mem_symmDiff, hA, hB]), chi_of_mem hA, chi_of_not_mem hB,
      add_zero]
  · rw [chi_of_mem (by simp [Set.mem_symmDiff, hA, hB]), chi_of_not_mem hA, chi_of_mem hB,
      zero_add]
  · rw [chi_of_not_mem (by simp [Set.mem_symmDiff, hA, hB]), chi_of_not_mem hA,
      chi_of_not_mem hB, add_zero]

/-- **Intersection is multiplication** in the `GF(2)`-space of extensions. -/
theorem chi_inter {O : Ontology I} (A B : Set I) :
    chi (O := O) (A ∩ B) = chi (O := O) A * chi (O := O) B := by
  funext a
  simp only [Pi.mul_apply]
  by_cases hA : a ∈ A <;> by_cases hB : a ∈ B
  · rw [chi_of_mem (Set.mem_inter hA hB), chi_of_mem hA, chi_of_mem hB, mul_one]
  · rw [chi_of_not_mem (by simp [hB]), chi_of_mem hA, chi_of_not_mem hB, mul_zero]
  · rw [chi_of_not_mem (by simp [hA]), chi_of_not_mem hA, chi_of_mem hB, zero_mul]
  · rw [chi_of_not_mem (by simp [hA]), chi_of_not_mem hA, chi_of_not_mem hB, zero_mul]

@[simp] theorem chi_empty {O : Ontology I} : chi (O := O) (∅ : Set I) = 0 := by
  funext a; rw [chi_of_not_mem (Set.notMem_empty a)]; rfl

@[simp] theorem chi_univ {O : Ontology I} : chi (O := O) (Set.univ : Set I) = 1 := by
  funext a; rw [chi_of_mem (Set.mem_univ a)]; rfl

/-- The indicator vector determines the set. -/
theorem chi_injective {O : Ontology I} : Function.Injective (chi (O := O)) := by
  intro A B h
  ext a
  have h' := congrFun h a
  constructor
  · intro ha
    by_contra hb
    rw [chi_of_mem ha, chi_of_not_mem hb] at h'
    exact one_ne_zero h'
  · intro hb
    by_contra ha
    rw [chi_of_not_mem ha, chi_of_mem hb] at h'
    exact zero_ne_one h'

/-! ## Morphisms act linearly -/

variable {O₁ : Ontology I} {O₂ : Ontology J}

/-- **Pulling extensions back along a strict morphism is a linear map** of
`GF(2)`-vector spaces. -/
noncomputable def comapLin (F : Morphism O₁ O₂) : ExtSpace O₂ →ₗ[GF2] ExtSpace O₁ :=
  LinearMap.funLeft GF2 GF2 F.map

@[simp] theorem comapLin_apply (F : Morphism O₁ O₂) (u : ExtSpace O₂) (a : I) :
    comapLin F u a = u (F.map a) := rfl

/-- Pulling a set of items back along an alignment is exactly the linear map
`Ontology.comapLin` on indicator vectors. -/
theorem chi_pull (F : Morphism O₁ O₂) (B : Set J) :
    chi (O := O₁) (F.toAlignment.pull B) = comapLin F (chi (O := O₂) B) := by
  funext a
  by_cases hb : F.map a ∈ B
  · rw [comapLin_apply, chi_of_mem hb, chi_of_mem (show a ∈ F.toAlignment.pull B from hb)]
  · rw [comapLin_apply, chi_of_not_mem hb, chi_of_not_mem (show a ∉ F.toAlignment.pull B from hb)]

theorem comapLin_id (O : Ontology I) : comapLin (Morphism.id O) = LinearMap.id := rfl

theorem comapLin_comp {K : Type*} {O₃ : Ontology K} (F : Morphism O₁ O₂) (G : Morphism O₂ O₃) :
    comapLin (F.comp G) = (comapLin F).comp (comapLin G) := rfl

/-! ## The pullback square, linearly -/

variable {X Y Z : Ont.{u}}

/-- **The pullback square of ontologies induces a commuting square of
`GF(2)`-linear maps** on extensions. -/
theorem comapLin_pb_comm (F : X ⟶ Z) (G : Y ⟶ Z) :
    (comapLin (pbFst F G)).comp (comapLin F) = (comapLin (pbSnd F G)).comp (comapLin G) := by
  refine LinearMap.ext fun u => funext fun p => ?_
  exact congrArg u p.2

/-- **The fibre product of two vector spaces**: the pairs of extensions that
agree after restriction to the fibre product of the ontologies. -/
noncomputable def extPullbackSubmodule (F : X ⟶ Z) (G : Y ⟶ Z) :
    Submodule GF2 (ExtSpace X.str × ExtSpace Y.str) :=
  LinearMap.ker (((comapLin (pbFst F G)).comp (LinearMap.fst GF2 _ _))
    - ((comapLin (pbSnd F G)).comp (LinearMap.snd GF2 _ _)))

theorem mem_extPullbackSubmodule_iff (F : X ⟶ Z) (G : Y ⟶ Z)
    (uv : ExtSpace X.str × ExtSpace Y.str) :
    uv ∈ extPullbackSubmodule F G ↔
      comapLin (pbFst F G) uv.1 = comapLin (pbSnd F G) uv.2 := by
  simp [extPullbackSubmodule, LinearMap.sub_apply, sub_eq_zero]

/-- **The universal property of the fibre product of vector spaces**, existence:
a pair of linear maps into the two factors that agree over the fibre product
factors through it. -/
noncomputable def extPullbackLift {M : Type*} [AddCommGroup M] [Module GF2 M]
    (F : X ⟶ Z) (G : Y ⟶ Z) (a : M →ₗ[GF2] ExtSpace X.str) (b : M →ₗ[GF2] ExtSpace Y.str)
    (h : (comapLin (pbFst F G)).comp a = (comapLin (pbSnd F G)).comp b) :
    M →ₗ[GF2] extPullbackSubmodule F G :=
  LinearMap.codRestrict _ (a.prod b) (fun m => by
    simpa [mem_extPullbackSubmodule_iff] using congrArg (fun t => t m) h)

@[simp] theorem extPullback_lift_apply {M : Type*} [AddCommGroup M] [Module GF2 M]
    (F : X ⟶ Z) (G : Y ⟶ Z) (a : M →ₗ[GF2] ExtSpace X.str) (b : M →ₗ[GF2] ExtSpace Y.str)
    (h : (comapLin (pbFst F G)).comp a = (comapLin (pbSnd F G)).comp b) (m : M) :
    (extPullbackLift F G a b h m).1 = (a m, b m) := rfl

/-- **The universal property of the fibre product of vector spaces**, uniqueness. -/
theorem extPullback_lift_unique {M : Type*} [AddCommGroup M] [Module GF2 M]
    (F : X ⟶ Z) (G : Y ⟶ Z) (φ ψ : M →ₗ[GF2] extPullbackSubmodule F G)
    (h1 : ∀ m, (φ m).1.1 = (ψ m).1.1) (h2 : ∀ m, (φ m).1.2 = (ψ m).1.2) : φ = ψ := by
  refine LinearMap.ext fun m => Subtype.ext (Prod.ext (h1 m) (h2 m))

/-- **The extensions of the reference ontology map into the fibre product** of the
extension spaces of the two aligned ontologies. -/
noncomputable def toExtPullback (F : X ⟶ Z) (G : Y ⟶ Z) :
    ExtSpace Z.str →ₗ[GF2] extPullbackSubmodule F G :=
  extPullbackLift F G (comapLin F) (comapLin G) (comapLin_pb_comm F G)

@[simp] theorem toExtPullback_apply (F : X ⟶ Z) (G : Y ⟶ Z) (u : ExtSpace Z.str) :
    (toExtPullback F G u).1 = (comapLin F u, comapLin G u) := rfl

/-- **If the reference ontology is covered by one of the two alignments, an
extension is determined by its two restrictions**: the map into the fibre
product of the extension spaces is injective. -/
theorem injective_toExtPullback (F : X ⟶ Z) (G : Y ⟶ Z)
    (hF : Function.Surjective F.map) : Function.Injective (toExtPullback F G) := by
  intro u v huv
  have h : comapLin F u = comapLin F v := congrArg (fun t => t.1.1) huv
  funext c
  obtain ⟨a, rfl⟩ := hF c
  exact congrFun h a

end Ontology
end Wikidata
