import Synthesis.MillenniumHodgeTetrahedralNativeKernel
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Tactic

/-!
# Native H₂ of the tetrahedral sphere is Q

Prize-facing closure of the finite simplicial calculation.

H5 already proves every native degree-two cycle is a scalar multiple of the
alternating fundamental chain.  We prove that chain is nonzero by projecting
onto one coproduct summand.  Since degree three of the boundary is zero, there
are no nonzero degree-two boundaries.  The explicit ModuleCat homology quotient
therefore collapses to the one-dimensional cycle line.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory Limits
open scoped Simplicial DirectSum

noncomputable abbrev tetrahedralDegreeTwoShortComplex :
    ShortComplex (ModuleCat ℚ) :=
  tetrahedralNormalizedChains.sc 2

noncomputable def tetrahedralFundamentalVector :
    tetrahedralNormalizedChains.X 2 :=
  tetrahedralNativeFundamentalChain (1 : ℚ)

theorem tetrahedralFundamentalVector_cycle :
    tetrahedralNormalizedChains.d 2 1 tetrahedralFundamentalVector = 0 := by
  have h := congrArg
    (fun f : rationalCoefficientObject ⟶ tetrahedralNormalizedChains.X 1 => f (1 : ℚ))
    tetrahedralNativeFundamental_isCycle
  simpa [tetrahedralFundamentalVector, Category.assoc] using h

/-- Coordinate projection onto a chosen native face summand. -/
noncomputable def tetrahedralFaceCoordinate
    (x : TetrahedralSphereSSet.nonDegenerate 2) :
    tetrahedralNormalizedChains.X 2 →ₗ[ℚ] ℚ :=
  (DirectSum.component ℚ
      (TetrahedralSphereSSet.nonDegenerate 2)
      (fun _ => ℚ) x).comp
    (tetrahedralNativeIsoDirectSum 2).hom.hom

theorem tetrahedralFaceCoordinate_generator
    (x y : TetrahedralSphereSSet.nonDegenerate 2) :
    tetrahedralFaceCoordinate x
      (TetrahedralSphereSSet.ιNormalizedChainComplex y.1 (1 : ℚ)) =
      if y = x then 1 else 0 := by
  classical
  by_cases h : y = x
  · subst y
    simp [tetrahedralFaceCoordinate, tetrahedralNativeIsoDirectSum]
  · simp [tetrahedralFaceCoordinate, tetrahedralNativeIsoDirectSum, h]

noncomputable def tetrahedralFaceZeroND :
    TetrahedralSphereSSet.nonDegenerate 2 :=
  ⟨tetrahedralFaceSimplex 0, tetrahedralFaceSimplex_nondegenerate 0⟩

theorem tetrahedralFaceSimplex_injective :
    Function.Injective (fun i : Fin 4 => tetrahedralFaceSimplex i) := by
  intro i j h
  have hij := congrArg
    (fun x => SSet.stdSimplex.objEquiv x.val) h
  simpa [tetrahedralFaceSimplex_val_objEquiv] using
    (SimplexCategory.δ_injective hij)

theorem tetrahedralFundamentalVector_faceZero :
    tetrahedralFaceCoordinate tetrahedralFaceZeroND
      tetrahedralFundamentalVector = 1 := by
  classical
  simp only [tetrahedralFundamentalVector, tetrahedralNativeFundamentalChain,
    map_sum, map_smul]
  rw [Fin.sum_univ_four]
  simp [tetrahedralNativeFaceChain, tetrahedralFaceCoordinate_generator,
    tetrahedralFaceZeroND, tetrahedralFaceSimplex_injective.eq_iff]

theorem tetrahedralFundamentalVector_ne_zero :
    tetrahedralFundamentalVector ≠ 0 := by
  intro h
  have := congrArg
    (tetrahedralFaceCoordinate tetrahedralFaceZeroND) h
  simpa [tetrahedralFundamentalVector_faceZero] using this

noncomputable def tetrahedralFundamentalToCycles :
    ℚ →ₗ[ℚ] LinearMap.ker (tetrahedralNormalizedChains.d 2 1).hom where
  toFun q := ⟨q • tetrahedralFundamentalVector, by
    simp [tetrahedralFundamentalVector_cycle]⟩
  map_add' q r := by ext; simp [add_smul]
  map_smul' q r := by ext; simp [mul_smul]

theorem tetrahedralFundamentalToCycles_injective :
    Function.Injective tetrahedralFundamentalToCycles := by
  intro q r h
  have hv : (q - r) • tetrahedralFundamentalVector = 0 := by
    have := congrArg Subtype.val h
    simpa [tetrahedralFundamentalToCycles, sub_smul] using
      sub_eq_zero.mpr this
  have : q - r = 0 := by
    exact (smul_eq_zero.mp hv).resolve_right tetrahedralFundamentalVector_ne_zero
  exact sub_eq_zero.mp this

theorem tetrahedralFundamentalToCycles_surjective :
    Function.Surjective tetrahedralFundamentalToCycles := by
  intro z
  let cycleMap : rationalCoefficientObject ⟶ tetrahedralNormalizedChains.X 2 :=
    ModuleCat.ofHom (LinearMap.smulRight (LinearMap.id) z.1)
  have hcycle :
      cycleMap ≫ tetrahedralNormalizedChains.d 2 1 = 0 := by
    ext q
    simp [cycleMap, z.2]
  obtain ⟨a, ha⟩ := tetrahedralNative_cycle_eq_scalar_fundamental cycleMap hcycle
  refine ⟨a, ?_⟩
  apply Subtype.ext
  have h1 := congrArg
    (fun f : rationalCoefficientObject ⟶ tetrahedralNormalizedChains.X 2 => f (1 : ℚ)) ha
  simpa [cycleMap, tetrahedralFundamentalToCycles, tetrahedralFundamentalVector] using h1

noncomputable def tetrahedralCyclesEquivQ :
    LinearMap.ker (tetrahedralNormalizedChains.d 2 1).hom ≃ₗ[ℚ] ℚ :=
  (LinearEquiv.ofBijective tetrahedralFundamentalToCycles
    ⟨tetrahedralFundamentalToCycles_injective,
      tetrahedralFundamentalToCycles_surjective⟩).symm

theorem tetrahedralDegreeTwoIncoming_range_eq_bot :
    tetrahedralDegreeTwoShortComplex.moduleCatToCycles.range = ⊥ := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    have hz : tetrahedralNormalizedChains.d 3 2 = 0 :=
      tetrahedralNormalized_d3_eq_zero
    simp [tetrahedralDegreeTwoShortComplex,
      ShortComplex.moduleCatToCycles, hz]
  · exact bot_le

noncomputable def tetrahedralNativeH2LinearEquivQ :
    tetrahedralNormalizedChains.homology 2 ≃ₗ[ℚ] ℚ := by
  let S := tetrahedralDegreeTwoShortComplex
  let eHom : S.homology ≃ₗ[ℚ] S.moduleCatLeftHomologyData.H :=
    S.moduleCatHomologyIso.toLinearEquiv
  let eBot :
      (LinearMap.ker S.g.hom ⧸ S.moduleCatToCycles.range) ≃ₗ[ℚ]
        LinearMap.ker S.g.hom :=
    (Submodule.quotEquivOfEq _ _ tetrahedralDegreeTwoIncoming_range_eq_bot).trans
      (Submodule.quotEquivOfEqBot ⊥ rfl)
  exact eHom.trans (eBot.trans tetrahedralCyclesEquivQ)

theorem tetrahedralNativeH2_finrank :
    Module.finrank ℚ (tetrahedralNormalizedChains.homology 2) = 1 := by
  rw [tetrahedralNativeH2LinearEquivQ.finrank_eq, Module.finrank_self]

end Synthesis.Millennium.Hodge
