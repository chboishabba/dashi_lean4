import Synthesis.MillenniumHodgeDeltaThreeAcyclicH2
import Synthesis.MillenniumHodgeTetrahedralNativeCycle
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.Tactic

/-!
# Exactness of the single ambient 3-simplex in degree two

This is the only ambient exactness fact required for the tetrahedral kernel.
By the specialized extra-degeneracy argument, normalized H₂(Δ[3];Q)=0, hence
the normalized complex is exact at degree 2.  In degree 3 there is exactly
one nondegenerate simplex: the identity top simplex.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory Limits
open AlgebraicTopology HomologicalComplex
open scoped Simplicial

noncomputable abbrev deltaThreeNormalizedChains :
    ChainComplex (ModuleCat ℚ) ℕ :=
  (Δ[3] : SSet).normalizedChainComplex rationalCoefficientObject

theorem deltaThreeNormalized_exactAt_two :
    deltaThreeNormalizedChains.ExactAt 2 := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact deltaThreeNormalizedH2_isZero

noncomputable def deltaThreeTopSimplex : (Δ[3] : SSet) _⦋3⦌ :=
  SSet.stdSimplex.objEquiv.symm (𝟙 ⦋3⦌)

theorem deltaThreeTopSimplex_nondegenerate :
    deltaThreeTopSimplex ∈ (Δ[3] : SSet).nonDegenerate 3 := by
  rw [SSet.stdSimplex.mem_nonDegenerate_iff_mono]
  change Mono (𝟙 ⦋3⦌)
  infer_instance

theorem deltaThree_nondegenerate_three_eq_top
    (x : (Δ[3] : SSet) _⦋3⦌)
    (hx : x ∈ (Δ[3] : SSet).nonDegenerate 3) :
    x = deltaThreeTopSimplex := by
  haveI : Mono (SSet.stdSimplex.objEquiv x) :=
    (SSet.stdSimplex.mem_nonDegenerate_iff_mono x).mp hx
  have h := SimplexCategory.eq_id_of_mono (SSet.stdSimplex.objEquiv x)
  apply SSet.stdSimplex.objEquiv.injective
  simpa [deltaThreeTopSimplex] using h

noncomputable def deltaThreeTopGenerator :
    rationalCoefficientObject ⟶ deltaThreeNormalizedChains.X 3 :=
  (Δ[3] : SSet).ιNormalizedChainComplex deltaThreeTopSimplex

/-- Every map out of ambient normalized degree three is determined by the top simplex. -/
theorem deltaThreeNormalized_degreeThree_hom_ext_top
    {T : ModuleCat ℚ}
    {f g : deltaThreeNormalizedChains.X 3 ⟶ T}
    (h : deltaThreeTopGenerator ≫ f = deltaThreeTopGenerator ≫ g) :
    f = g := by
  apply (Δ[3] : SSet).normalizedChainComplex_hom_ext
  intro x hx
  rw [deltaThree_nondegenerate_three_eq_top x hx]
  exact h

end Synthesis.Millennium.Hodge
