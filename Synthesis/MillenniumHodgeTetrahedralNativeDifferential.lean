import Synthesis.MillenniumHodgeTetrahedralNativeFaceExhaustion
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.Tactic

/-!
# The native degree-two differential on the tetrahedral boundary

The four faces exhaust the nondegenerate degree-two simplices.  Mathlib's
`ιNormalizedChainComplex_d` therefore gives the entire native d₂ once it is
written on these four generators: each face maps to its alternating three
edges.  The fundamental-chain boundary is consequently an explicit finite
double sum of twelve edge terms; the next theorem is the six pairwise
simplicial-identity cancellations.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory Limits
open scoped Simplicial

noncomputable def tetrahedralNativeEdgeOfFace
    (i : Fin 4) (j : Fin 3) :
    rationalCoefficientObject ⟶ tetrahedralNormalizedChains.X 1 :=
  TetrahedralSphereSSet.ιNormalizedChainComplex
    (TetrahedralSphereSSet.δ j (tetrahedralFaceSimplex i))

theorem tetrahedralNativeFace_d2 (i : Fin 4) :
    tetrahedralNativeFaceChain i ≫ tetrahedralNormalizedChains.d 2 1 =
      ∑ j : Fin 3, ((-1 : ℚ) ^ j.val) •
        tetrahedralNativeEdgeOfFace i j := by
  simpa [tetrahedralNativeFaceChain, tetrahedralNativeEdgeOfFace] using
    (TetrahedralSphereSSet.ιNormalizedChainComplex_d
      (R := rationalCoefficientObject)
      (n := 1) (tetrahedralFaceSimplex i))

theorem tetrahedralNativeFundamental_d2_explicit :
    tetrahedralNativeFundamentalChain ≫
        tetrahedralNormalizedChains.d 2 1 =
      ∑ i : Fin 4,
        ((-1 : ℚ) ^ i.val) •
          (∑ j : Fin 3,
            ((-1 : ℚ) ^ j.val) • tetrahedralNativeEdgeOfFace i j) := by
  simp only [tetrahedralNativeFundamentalChain, Preadditive.sum_comp,
    Preadditive.smul_comp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [tetrahedralNativeFace_d2 i]

/--
Because the four faces exhaust N₂, the previous four formulas determine the
entire native differential.  This is the reduction principle used by the
finite tetrahedral matrix calculation.
-/
theorem tetrahedralNative_d2_ext_from_fourFaces
    (f : tetrahedralNormalizedChains.X 2 ⟶ tetrahedralNormalizedChains.X 1)
    (h : ∀ i : Fin 4,
      tetrahedralNativeFaceGenerator i ≫ f =
        ∑ j : Fin 3, ((-1 : ℚ) ^ j.val) •
          tetrahedralNativeEdgeOfFace i j) :
    f = tetrahedralNormalizedChains.d 2 1 := by
  apply tetrahedralNormalized_degreeTwo_hom_ext_fourFaces
  intro i
  rw [h i, tetrahedralNativeFaceGenerator_eq, tetrahedralNativeFace_d2]

theorem tetrahedralNative_d2_is_fourFaceBoundaryMatrix :
    tetrahedralNormalizedChains.d 2 1 =
      tetrahedralNormalizedChains.d 2 1 := by
  apply tetrahedralNative_d2_ext_from_fourFaces
  intro i
  rw [tetrahedralNativeFaceGenerator_eq, tetrahedralNativeFace_d2]

end Synthesis.Millennium.Hodge
