import Synthesis.MillenniumHodgeTetrahedralNativeAmbientMono
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.Tactic

/-!
# Native degree-one tetrahedral generators are exactly the six edges

Mathlib identifies nondegenerate one-simplices of `Δ[3]` with two-element
subsets of `Fin 4`.  Since the degree-one object of `∂Δ[3]` is all of the
degree-one object of `Δ[3]`, the same classification applies to the boundary.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory Opposite Limits
open scoped Simplicial

abbrev TetrahedralEdgeIndex : Type :=
  { S : Finset (Fin 4) // S.card = 2 }

noncomputable def tetrahedralBoundaryNDEdgeToAmbient :
    TetrahedralSphereSSet.nonDegenerate 1 ≃
      (Δ[3] : SSet).nonDegenerate 1 where
  toFun x := ⟨x.1.val, by
    rw [Subcomplex.mem_nonDegenerate_iff] at x
    exact x.2⟩
  invFun x :=
    ⟨⟨x.1, by
        rw [SSet.boundary_obj_eq_univ 1 3 (by omega)]
        simp⟩, by
      rw [Subcomplex.mem_nonDegenerate_iff]
      exact x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

noncomputable def tetrahedralNondegenerateEdgeEquiv :
    TetrahedralSphereSSet.nonDegenerate 1 ≃ TetrahedralEdgeIndex :=
  tetrahedralBoundaryNDEdgeToAmbient.trans
    SSet.stdSimplex.nonDegenerateEquiv'

noncomputable def tetrahedralEdgeSimplex
    (e : TetrahedralEdgeIndex) :
    TetrahedralSphereSSet _⦋1⦌ :=
  (tetrahedralNondegenerateEdgeEquiv.symm e).1

theorem tetrahedralEdgeSimplex_nondegenerate
    (e : TetrahedralEdgeIndex) :
    tetrahedralEdgeSimplex e ∈ TetrahedralSphereSSet.nonDegenerate 1 :=
  (tetrahedralNondegenerateEdgeEquiv.symm e).2

noncomputable def tetrahedralNativeEdgeGenerator
    (e : TetrahedralEdgeIndex) :
    rationalCoefficientObject ⟶ tetrahedralNormalizedChains.X 1 :=
  TetrahedralSphereSSet.ιNormalizedChainComplex
    (tetrahedralEdgeSimplex e)

theorem tetrahedralNativeEdgeGenerator_is_coproduct_leg
    (e : TetrahedralEdgeIndex) :
    tetrahedralNativeEdgeGenerator e =
      Sigma.ι
        (fun (_ : TetrahedralSphereSSet.nonDegenerate 1) =>
          rationalCoefficientObject)
        (tetrahedralNondegenerateEdgeEquiv.symm e) := by
  exact TetrahedralSphereSSet.ιNormalizedChainComplex_eq_ι
    rationalCoefficientObject 1
    (tetrahedralEdgeSimplex e)
    (tetrahedralEdgeSimplex_nondegenerate e)

theorem tetrahedral_degreeOne_generators_exhaust
    (x : TetrahedralSphereSSet _⦋1⦌)
    (hx : x ∈ TetrahedralSphereSSet.nonDegenerate 1) :
    ∃ e : TetrahedralEdgeIndex, x = tetrahedralEdgeSimplex e := by
  let nx : TetrahedralSphereSSet.nonDegenerate 1 := ⟨x,hx⟩
  refine ⟨tetrahedralNondegenerateEdgeEquiv nx, ?_⟩
  exact congrArg Subtype.val
    (tetrahedralNondegenerateEdgeEquiv.symm_apply_apply nx).symm

theorem tetrahedralNormalized_degreeOne_hom_ext_sixEdges
    {T : ModuleCat ℚ}
    {f g : tetrahedralNormalizedChains.X 1 ⟶ T}
    (h : ∀ e : TetrahedralEdgeIndex,
      tetrahedralNativeEdgeGenerator e ≫ f =
        tetrahedralNativeEdgeGenerator e ≫ g) :
    f = g := by
  apply TetrahedralSphereSSet.normalizedChainComplex_hom_ext
  intro x hx
  obtain ⟨e,rfl⟩ := tetrahedral_degreeOne_generators_exhaust x hx
  exact h e

noncomputable instance tetrahedralEdgeIndexFintype : Fintype TetrahedralEdgeIndex :=
  Fintype.ofFinite _

theorem tetrahedralEdgeIndex_card : Fintype.card TetrahedralEdgeIndex = 6 := by
  native_decide

noncomputable def tetrahedralEdgeIndexEquivFinSix :
    TetrahedralEdgeIndex ≃ Fin 6 :=
  Fintype.equivFinOfCardEq tetrahedralEdgeIndex_card

end Synthesis.Millennium.Hodge
