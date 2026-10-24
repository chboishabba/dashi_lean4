import Synthesis.MillenniumHodgeCP1CellularH2
import Synthesis.MillenniumHodgeSphereSimplicialBoundaryH2
import Mathlib.Tactic

/-!
# CP¹/S² finite cellular H² paired with the tetrahedral H₂ model

MAXIMUM REUSE: No new sphere, projective quotient, simplex or homology
quotient. Sources, all already present in dashi_lean4:
* MillenniumHodgeCP1TopologicalSphere: genuine CP¹ ≃ₜ S²;
* MillenniumHodgeCP1SingularTransport: actual singular H₂ transport;
* MillenniumHodgeCP1CellularH2: rational cellular degree-two class;
* MillenniumHodgeSphereSimplicialBoundaryH2: exact tetrahedral H₂ ≃ ℚ.

What is now proved here is a PERFECT PAIRING on these two existing
finite abstract models. It does not identify the pairing with actual
singular cup/cap evaluation, nor supply the uninhabited tetrahedral
simplicial-to-singular comparison. H² and H₂ are deliberately distinct.
Classical background: cellular/simplicial homology and the universal
coefficient pairing over a field (Eilenberg--Steenrod, Hatcher).
-/

namespace Synthesis.ExoticTopology

open Synthesis.Millennium.Hodge

/-- Evaluation on the finite H² and H₂ models, via their source-owned
    exact rational coefficient maps. -/
def finiteSphereEvaluation (cohom : CP1CellularH2)
    (hom : TetraH2Class) : ℚ :=
  cohom * tetraH2ToQ hom

theorem evaluation_on_fundamental_cycle (cohom : CP1CellularH2) :
    finiteSphereEvaluation cohom (qToTetraH2 1) = cohom := by
  simp [finiteSphereEvaluation, qToTetraH2_toQ]

theorem evaluation_on_cohomological_unit (hom : TetraH2Class) :
    finiteSphereEvaluation pointDivisorCellularClass hom =
      tetraH2ToQ hom := by
  simp [finiteSphereEvaluation, pointDivisorCellularClass]

theorem detects_nonzero_cohomology (cohom : CP1CellularH2)
    (hcohom : cohom ≠ 0) :
    ∃ hom : TetraH2Class, finiteSphereEvaluation cohom hom ≠ 0 := by
  refine ⟨qToTetraH2 1, ?_⟩
  simpa [evaluation_on_fundamental_cycle] using hcohom

theorem detects_nonzero_homology (hom : TetraH2Class)
    (hhom : hom ≠ qToTetraH2 0) :
    ∃ cohom : CP1CellularH2, finiteSphereEvaluation cohom hom ≠ 0 := by
  have hcoord : tetraH2ToQ hom ≠ 0 := by
    intro heq
    apply hhom
    calc
      hom = qToTetraH2 (tetraH2ToQ hom) :=
        (tetraH2_toQ_roundTrip hom).symm
      _ = qToTetraH2 0 := by rw [heq]
  refine ⟨pointDivisorCellularClass, ?_⟩
  simpa [evaluation_on_cohomological_unit] using hcoord

theorem zero_evaluation_iff_zero_cohomology (cohom : CP1CellularH2) :
    (∀ hom : TetraH2Class, finiteSphereEvaluation cohom hom = 0) ↔
      cohom = 0 := by
  constructor
  · intro h
    have hfund := h (qToTetraH2 1)
    simpa [evaluation_on_fundamental_cycle] using hfund
  · rintro rfl hom
    simp [finiteSphereEvaluation]

theorem zero_evaluation_iff_zero_homology (hom : TetraH2Class) :
    (∀ cohom : CP1CellularH2, finiteSphereEvaluation cohom hom = 0) ↔
      hom = qToTetraH2 0 := by
  constructor
  · intro h
    have hcoord : tetraH2ToQ hom = 0 := by
      simpa [evaluation_on_cohomological_unit] using
        h pointDivisorCellularClass
    calc
      hom = qToTetraH2 (tetraH2ToQ hom) :=
        (tetraH2_toQ_roundTrip hom).symm
      _ = qToTetraH2 0 := by rw [hcoord]
  · intro heq cohom
    subst hom
    simp [finiteSphereEvaluation, qToTetraH2_toQ]

end Synthesis.ExoticTopology
