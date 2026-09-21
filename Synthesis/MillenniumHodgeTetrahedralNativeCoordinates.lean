import Synthesis.MillenniumHodgeTetrahedralNativeEdges
import Synthesis.MillenniumHodgeTetrahedralNativeFaceExhaustion
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Tactic

/-!
# Native tetrahedral normalized chains have literal Q^4 / Q^6 coordinates

The normalized chain object is the coproduct of one copy of `Q` for each
nondegenerate simplex.  We use its actual colimit certificate, the concrete
`ModuleCat` coproduct/direct-sum comparison, and the finite direct-sum/function
equivalence.  Degree two has four face coordinates and degree one six edge
coordinates.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory Opposite Limits
open scoped Simplicial DirectSum

noncomputable def tetrahedralNativeIsoDirectSum (n : ℕ) :
    tetrahedralNormalizedChains.X n ≅
      ModuleCat.of ℚ (⨁ _ : TetrahedralSphereSSet.nonDegenerate n, ℚ) := by
  classical
  let Z : TetrahedralSphereSSet.nonDegenerate n → ModuleCat ℚ :=
    fun _ => rationalCoefficientObject
  exact
    (TetrahedralSphereSSet.isColimitCofanNormalizedChainComplex
      rationalCoefficientObject n).coconePointUniqueUpToIso
      (ModuleCat.coproductCoconeIsColimit Z)

noncomputable def tetrahedralNativeNondegenerateCoords (n : ℕ) :
    tetrahedralNormalizedChains.X n ≃ₗ[ℚ]
      (TetrahedralSphereSSet.nonDegenerate n → ℚ) := by
  classical
  exact (tetrahedralNativeIsoDirectSum n).toLinearEquiv.trans
    (DirectSum.linearEquivFunOnFintype ℚ
      (TetrahedralSphereSSet.nonDegenerate n) (fun _ => ℚ))

noncomputable def reindexFunLinearEquiv
    {α β : Type} (e : α ≃ β) :
    (α → ℚ) ≃ₗ[ℚ] (β → ℚ) where
  toFun f b := f (e.symm b)
  invFun g a := g (e a)
  left_inv f := by funext a; simp
  right_inv g := by funext b; simp
  map_add' f g := rfl
  map_smul' q f := rfl

abbrev TetrahedralFaceIndex : Type :=
  { S : Finset (Fin 4) // S.card = 3 }

noncomputable def tetrahedralBoundaryNDFaceToAmbient :
    TetrahedralSphereSSet.nonDegenerate 2 ≃
      (Δ[3] : SSet).nonDegenerate 2 where
  toFun x := ⟨x.1.val, by
    rw [Subcomplex.mem_nonDegenerate_iff] at x
    exact x.2⟩
  invFun x :=
    ⟨⟨x.1, by
        rw [SSet.boundary_obj_eq_univ 2 3 (by omega)]
        simp⟩, by
      rw [Subcomplex.mem_nonDegenerate_iff]
      exact x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

noncomputable def tetrahedralNondegenerateFaceEquiv :
    TetrahedralSphereSSet.nonDegenerate 2 ≃ TetrahedralFaceIndex :=
  tetrahedralBoundaryNDFaceToAmbient.trans
    SSet.stdSimplex.nonDegenerateEquiv'

noncomputable instance tetrahedralFaceIndexFintype : Fintype TetrahedralFaceIndex :=
  Fintype.ofFinite _

theorem tetrahedralFaceIndex_card : Fintype.card TetrahedralFaceIndex = 4 := by
  native_decide

noncomputable def tetrahedralFaceIndexEquivFinFour :
    TetrahedralFaceIndex ≃ Fin 4 :=
  Fintype.equivFinOfCardEq tetrahedralFaceIndex_card

noncomputable def tetrahedralN2EquivQ4 :
    tetrahedralNormalizedChains.X 2 ≃ₗ[ℚ] (Fin 4 → ℚ) :=
  (tetrahedralNativeNondegenerateCoords 2).trans
    ((reindexFunLinearEquiv tetrahedralNondegenerateFaceEquiv).trans
      (reindexFunLinearEquiv tetrahedralFaceIndexEquivFinFour))

noncomputable def tetrahedralN1EquivQ6 :
    tetrahedralNormalizedChains.X 1 ≃ₗ[ℚ] (Fin 6 → ℚ) :=
  (tetrahedralNativeNondegenerateCoords 1).trans
    ((reindexFunLinearEquiv tetrahedralNondegenerateEdgeEquiv).trans
      (reindexFunLinearEquiv tetrahedralEdgeIndexEquivFinSix))

theorem tetrahedralN2_finrank :
    Module.finrank ℚ (tetrahedralNormalizedChains.X 2) = 4 := by
  rw [tetrahedralN2EquivQ4.finrank_eq, Module.finrank_pi_fintype]
  simp

theorem tetrahedralN1_finrank :
    Module.finrank ℚ (tetrahedralNormalizedChains.X 1) = 6 := by
  rw [tetrahedralN1EquivQ6.finrank_eq, Module.finrank_pi_fintype]
  simp

/-- Transport the actual native d2 into a literal 6x4 linear map. -/
noncomputable def tetrahedralNativeD2Coordinates :
    (Fin 4 → ℚ) →ₗ[ℚ] (Fin 6 → ℚ) :=
  tetrahedralN1EquivQ6.toLinearMap.comp
    ((tetrahedralNormalizedChains.d 2 1).hom.comp
      tetrahedralN2EquivQ4.symm.toLinearMap)

end Synthesis.Millennium.Hodge
