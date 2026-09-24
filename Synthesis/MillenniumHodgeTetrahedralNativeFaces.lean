import Synthesis.MillenniumHodgeTetrahedralNativeFundamentalChain
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.Tactic

/-!
# Native nondegenerate tetrahedral faces

The four codimension-one face inclusions `Δ[2] ⟶ ∂Δ[3]` are monomorphisms.
The top simplex of `Δ[2]` is nondegenerate, hence its image is nondegenerate.
This ties the four generators used in the explicit tetrahedral calculation to
the actual coproduct generators of mathlib's normalized degree-two chains.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory Opposite Limits
open scoped Simplicial

theorem tetrahedralFaceSimplex_nondegenerate (i : Fin 4) :
    tetrahedralFaceSimplex i ∈ TetrahedralSphereSSet.nonDegenerate 2 := by
  rw [Subcomplex.mem_nonDegenerate_iff]
  change ((SSet.boundary.ι i).app (op ⦋2⦌)
    (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋2⦌))) ∈
      (Δ[3] : SSet).nonDegenerate 2
  rw [SSet.stdSimplex.mem_nonDegenerate_iff_mono]
  infer_instance

noncomputable def tetrahedralNativeFaceGenerator (i : Fin 4) :
    rationalCoefficientObject ⟶ tetrahedralNormalizedChains.X 2 :=
  TetrahedralSphereSSet.ιNormalizedChainComplex
    (tetrahedralFaceSimplex i)

theorem tetrahedralNativeFaceGenerator_eq (i : Fin 4) :
    tetrahedralNativeFaceGenerator i = tetrahedralNativeFaceChain i := rfl

/-- The four face generators are genuine coproduct injections in degree two. -/
theorem tetrahedralNativeFaceGenerator_is_coproduct_leg (i : Fin 4) :
    tetrahedralNativeFaceGenerator i =
      Sigma.ι
        (fun (_ : TetrahedralSphereSSet.nonDegenerate 2) =>
          rationalCoefficientObject)
        ⟨tetrahedralFaceSimplex i, tetrahedralFaceSimplex_nondegenerate i⟩ := by
  exact TetrahedralSphereSSet.ιNormalizedChainComplex_eq_ι
    rationalCoefficientObject 2
    (tetrahedralFaceSimplex i)
    (tetrahedralFaceSimplex_nondegenerate i)

/--
Any two maps out of native degree-two normalized chains agree once they agree
on all nondegenerate 2-simplices.  The four explicit faces are now certified
members of that native generator family.
-/
theorem tetrahedralNormalized_degreeTwo_hom_ext
    {T : ModuleCat ℚ}
    {f g : tetrahedralNormalizedChains.X 2 ⟶ T}
    (h : ∀ (x : TetrahedralSphereSSet _⦋2⦌)
      (_ : x ∈ TetrahedralSphereSSet.nonDegenerate 2),
      TetrahedralSphereSSet.ιNormalizedChainComplex x ≫ f =
        TetrahedralSphereSSet.ιNormalizedChainComplex x ≫ g) :
    f = g := by
  exact TetrahedralSphereSSet.normalizedChainComplex_hom_ext h

end Synthesis.Millennium.Hodge
