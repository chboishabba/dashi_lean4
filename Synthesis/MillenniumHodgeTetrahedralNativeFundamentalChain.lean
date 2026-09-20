import Synthesis.MillenniumHodgeTetrahedralNormalizedToSingular
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.Tactic

/-!
# The native tetrahedral fundamental chain

The four actual faces of `∂Δ[3]` define four degree-two generators in the
native normalized chain complex.  Their alternating sum is the literal
tetrahedral fundamental chain.  Naturality of `ιNormalizedChainComplex`
shows that the realization-unit map sends this chain to the same alternating
sum of the corresponding singular simplices.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory Limits
open scoped Simplicial

noncomputable def tetrahedralNativeFaceChain (i : Fin 4) :
    rationalCoefficientObject ⟶ tetrahedralNormalizedChains.X 2 :=
  TetrahedralSphereSSet.ιNormalizedChainComplex
    (tetrahedralFaceSimplex i)

noncomputable def tetrahedralNativeFundamentalChain :
    rationalCoefficientObject ⟶ tetrahedralNormalizedChains.X 2 :=
  ∑ i : Fin 4, ((-1 : ℚ) ^ i.val) • tetrahedralNativeFaceChain i

noncomputable def tetrahedralSingularNormalizedFaceChain (i : Fin 4) :
    rationalCoefficientObject ⟶
      tetrahedralRealizationSingularNormalizedChains.X 2 :=
  TetrahedralSingularSet.ιNormalizedChainComplex
    (tetrahedralFaceSingularSimplex i)

noncomputable def tetrahedralSingularNormalizedFundamentalChain :
    rationalCoefficientObject ⟶
      tetrahedralRealizationSingularNormalizedChains.X 2 :=
  ∑ i : Fin 4,
    ((-1 : ℚ) ^ i.val) • tetrahedralSingularNormalizedFaceChain i

theorem tetrahedralNativeFaceChain_maps_to_singularFace (i : Fin 4) :
    tetrahedralNativeFaceChain i ≫
        tetrahedralUnitNormalizedChainMap.f 2
      = tetrahedralSingularNormalizedFaceChain i := by
  exact SSet.ι_normalizedChainComplexMap_f
    tetrahedralRealizationUnit rationalCoefficientObject
    (tetrahedralFaceSimplex i)

theorem tetrahedralNativeFundamentalChain_maps_to_singularFundamental :
    tetrahedralNativeFundamentalChain ≫
        tetrahedralUnitNormalizedChainMap.f 2
      = tetrahedralSingularNormalizedFundamentalChain := by
  simp only [tetrahedralNativeFundamentalChain,
    tetrahedralSingularNormalizedFundamentalChain,
    Preadditive.sum_comp, Preadditive.smul_comp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [tetrahedralNativeFaceChain_maps_to_singularFace]

theorem tetrahedralNormalized_degreeThree_isZero :
    IsZero (tetrahedralNormalizedChains.X 3) := by
  exact TetrahedralSphereSSet.isZero_normalizedChainComplex_X_of_hasDimensionLT
    rationalCoefficientObject 3 3

/-- There are no native degree-three normalized boundaries except zero. -/
theorem tetrahedralNormalized_d3_eq_zero :
    tetrahedralNormalizedChains.d 3 2 = 0 := by
  exact (tetrahedralNormalized_degreeThree_isZero.eq_of_src
    (tetrahedralNormalizedChains.d 3 2) 0)

end Synthesis.Millennium.Hodge
