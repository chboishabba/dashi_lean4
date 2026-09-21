import Synthesis.MillenniumHodgeTetrahedralNativeCoordinates
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.Tactic

/-!
# Native fundamental class maps to the ambient top-simplex boundary

The alternating four-face chain in `N₂(∂Δ[3])` is sent by the monic
native-to-ambient comparison to the ordinary simplicial boundary of the unique
nondegenerate top simplex of `Δ[3]`.  Hence its native boundary vanishes by
`d²=0` and monomorphism cancellation.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory Opposite Limits
open scoped Simplicial

noncomputable def tetrahedralAmbientTopSimplex : (Δ[3] : SSet) _⦋3⦌ :=
  SSet.stdSimplex.objEquiv.symm (𝟙 ⦋3⦌)

noncomputable def tetrahedralAmbientTopChain :
    rationalCoefficientObject ⟶
      ((Δ[3] : SSet).chainComplex rationalCoefficientObject).X 3 :=
  (Δ[3] : SSet).ιChainComplex tetrahedralAmbientTopSimplex

theorem tetrahedralAmbientTop_boundary :
    tetrahedralAmbientTopChain ≫
        ((Δ[3] : SSet).chainComplex rationalCoefficientObject).d 3 2 =
      ∑ i : Fin 4, ((-1 : ℚ) ^ i.val) •
        (Δ[3] : SSet).ιChainComplex
          ((Δ[3] : SSet).δ i tetrahedralAmbientTopSimplex) := by
  simpa [tetrahedralAmbientTopChain] using
    ((Δ[3] : SSet).ιChainComplex_d
      (R := rationalCoefficientObject)
      (n := 2) tetrahedralAmbientTopSimplex)

theorem tetrahedralFace_toAmbient_is_topFace (i : Fin 4) :
    tetrahedralNativeFaceChain i ≫ tetrahedralNativeToAmbientOrdinary 2 =
      (Δ[3] : SSet).ιChainComplex
        ((Δ[3] : SSet).δ i tetrahedralAmbientTopSimplex) := by
  simp [tetrahedralNativeFaceChain, tetrahedralNativeToAmbientOrdinary,
    tetrahedralFaceSimplex, tetrahedralFaceMap, tetrahedralAmbientTopSimplex,
    SSet.ιNormalizedChainComplex_fromNormalizedChainComplex_f,
    SSet.ι_chainComplexMap_f]

theorem tetrahedralNativeFundamental_to_ambient_boundary :
    tetrahedralNativeFundamentalChain ≫
        tetrahedralNativeToAmbientOrdinary 2 =
      tetrahedralAmbientTopChain ≫
        ((Δ[3] : SSet).chainComplex rationalCoefficientObject).d 3 2 := by
  rw [tetrahedralAmbientTop_boundary]
  simp only [tetrahedralNativeFundamentalChain, Preadditive.sum_comp,
    Preadditive.smul_comp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [tetrahedralFace_toAmbient_is_topFace i]

theorem tetrahedralNativeFundamental_isCycle :
    tetrahedralNativeFundamentalChain ≫
      tetrahedralNormalizedChains.d 2 1 = 0 := by
  apply tetrahedralNativeToAmbientOrdinary_cancel
    (n := 1)
    (tetrahedralNativeFundamentalChain ≫ tetrahedralNormalizedChains.d 2 1)
    0
  rw [Category.assoc]
  change tetrahedralNativeFundamentalChain ≫
      tetrahedralNativeToAmbientOrdinary 2 ≫
      ((Δ[3] : SSet).chainComplex rationalCoefficientObject).d 2 1 = 0
  rw [tetrahedralNativeFundamental_to_ambient_boundary]
  simp only [Category.assoc]
  rw [HomologicalComplex.d_comp_d]
  simp

end Synthesis.Millennium.Hodge
