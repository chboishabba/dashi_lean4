import Synthesis.MillenniumHodgeTetrahedralNativeFaces
import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
import Mathlib.Tactic

/-!
# Exhaust the native degree-two generators of ∂Δ[3]

A nondegenerate 2-simplex of the tetrahedral boundary is a nondegenerate
2-simplex of Δ[3].  Under `stdSimplex.objEquiv` this is a monomorphism
`[2] ⟶ [3]`.  Mathlib's `SimplexCategory.eq_δ_of_mono` says every such
codimension-one mono is one of the four cofaces.

Hence the four explicit tetrahedral faces are not merely four generators:
they exhaust the complete native nondegenerate degree-two generator family.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory Opposite Limits
open scoped Simplicial

theorem tetrahedralFaceSimplex_val_objEquiv (i : Fin 4) :
    SSet.stdSimplex.objEquiv (tetrahedralFaceSimplex i).val =
      SimplexCategory.δ i := by
  apply SSet.stdSimplex.objEquiv.injective
  change (tetrahedralFaceSimplex i).val =
    SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i)
  calc
    (tetrahedralFaceSimplex i).val =
        ((SSet.boundary 3).ι).app (op ⦋2⦌) (tetrahedralFaceSimplex i) := rfl
    _ = SSet.yonedaEquiv
        (tetrahedralFaceMap i ≫ (SSet.boundary 3).ι) := by
          rw [SSet.yonedaEquiv_comp]
    _ = SSet.yonedaEquiv (SSet.stdSimplex.δ i) := by
          rw [tetrahedralFaceMap_then_boundary_inclusion]
    _ = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i) := by
          exact SSet.yonedaEquiv_map _

/-- Every native nondegenerate 2-simplex of ∂Δ[3] is exactly one of the four faces. -/
theorem tetrahedralNondegenerateTwoSimplex_eq_face
    (x : TetrahedralSphereSSet _⦋2⦌)
    (hx : x ∈ TetrahedralSphereSSet.nonDegenerate 2) :
    ∃ i : Fin 4, x = tetrahedralFaceSimplex i := by
  have hxAmbient : x.val ∈ (Δ[3] : SSet).nonDegenerate 2 := by
    simpa [Subcomplex.mem_nonDegenerate_iff] using hx
  have hmono : Mono (SSet.stdSimplex.objEquiv x.val) :=
    (SSet.stdSimplex.mem_nonDegenerate_iff_mono x.val).mp hxAmbient
  letI : Mono (SSet.stdSimplex.objEquiv x.val) := hmono
  obtain ⟨i, hi⟩ :=
    SimplexCategory.eq_δ_of_mono (SSet.stdSimplex.objEquiv x.val)
  refine ⟨i, ?_⟩
  apply Subtype.ext
  apply SSet.stdSimplex.objEquiv.injective
  rw [hi, tetrahedralFaceSimplex_val_objEquiv]

/-- The four face simplices exhaust the subtype of nondegenerate degree-two simplices. -/
theorem tetrahedralNondegenerateTwoSimplex_surjective :
    Function.Surjective
      (fun i : Fin 4 =>
        (⟨tetrahedralFaceSimplex i, tetrahedralFaceSimplex_nondegenerate i⟩ :
          TetrahedralSphereSSet.nonDegenerate 2)) := by
  intro x
  rcases x with ⟨x,hx⟩
  obtain ⟨i,rfl⟩ := tetrahedralNondegenerateTwoSimplex_eq_face x hx
  exact ⟨i, rfl⟩

/--
To prove equality of maps out of native N₂(∂Δ³;Q), it now suffices to check
the four literal tetrahedral face generators.
-/
theorem tetrahedralNormalized_degreeTwo_hom_ext_fourFaces
    {T : ModuleCat ℚ}
    {f g : tetrahedralNormalizedChains.X 2 ⟶ T}
    (h : ∀ i : Fin 4,
      tetrahedralNativeFaceGenerator i ≫ f =
        tetrahedralNativeFaceGenerator i ≫ g) :
    f = g := by
  apply tetrahedralNormalized_degreeTwo_hom_ext
  intro x hx
  obtain ⟨i,rfl⟩ := tetrahedralNondegenerateTwoSimplex_eq_face x hx
  exact h i

end Synthesis.Millennium.Hodge
