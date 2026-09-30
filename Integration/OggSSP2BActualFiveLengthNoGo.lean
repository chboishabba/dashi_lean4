import Integration.OggSSP2BActualRestrictedTate
import Integration.OggSSP2BActualWeightTwoSourceBudget

/-!
# Actual 2B Tate lengths versus the proposed five geometric defect lengths

The published 4A(2B) integral decomposition and its restriction to H=<g^2>
already determine ordinary C2 Tate lengths in low Moonshine weights:
  weight 2 : Hhat0 length 276, Hhat1 length 0
  weight 3 : Hhat0 length 0,   Hhat1 length 2048.

The independent binary-tetrahedral defect vector (3,3,2,1,1) sums to 10.
Therefore five modules of exactly those lengths CANNOT be an exhaustive
direct-sum decomposition of either nonzero actual low-weight Tate module.

This is not a no-go for some additional five *localized subquotients* whose
lengths are 3,3,2,1,1. It proves that such objects would need extra residual
pieces and independently sourced localization maps; they are not the complete
actual Tate module supplied by Carnahan--Urano.
-/

namespace Integration.OggSSP2BActualFiveLengthNoGo

namespace T := Integration.OggSSP2BActualRestrictedTate
namespace M := Integration.OggSSP2B4AActualIntegralMultiplicities

def proposedFiveTotal : ℕ := 3 + 3 + 2 + 1 + 1

theorem proposedFiveTotal_eq_ten : proposedFiveTotal = 10 := by
  decide

theorem weightTwo_actual_nonzero_tate_length :
    T.gradeH0Length M.weightTwo = 276 := by
  exact (T.weight_two_ordinary_tate_lengths).1

theorem weightThree_actual_nonzero_tate_length :
    T.gradeH1Length M.weightThree = 2048 := by
  exact (T.weight_three_ordinary_tate_lengths).2

theorem proposed_five_not_exhaust_weightTwo_H0 :
    proposedFiveTotal ≠ T.gradeH0Length M.weightTwo := by
  rw [proposedFiveTotal_eq_ten, weightTwo_actual_nonzero_tate_length]
  decide

theorem proposed_five_not_exhaust_weightThree_H1 :
    proposedFiveTotal ≠ T.gradeH1Length M.weightThree := by
  rw [proposedFiveTotal_eq_ten, weightThree_actual_nonzero_tate_length]
  decide

theorem weightTwo_residual_after_proposed_five :
    T.gradeH0Length M.weightTwo - proposedFiveTotal = 266 := by
  rw [weightTwo_actual_nonzero_tate_length, proposedFiveTotal_eq_ten]
  decide

theorem weightThree_residual_after_proposed_five :
    T.gradeH1Length M.weightThree - proposedFiveTotal = 2038 := by
  rw [weightThree_actual_nonzero_tate_length, proposedFiveTotal_eq_ten]
  decide

/-- Any source claim that the five lengths exhaust an actual low-weight Tate
module contradicts the published restricted-module calculation. -/
theorem no_exhaustive_five_length_identification :
    ¬ (
      proposedFiveTotal = T.gradeH0Length M.weightTwo ∨
      proposedFiveTotal = T.gradeH1Length M.weightThree
    ) := by
  intro h
  rcases h with h | h
  · exact proposed_five_not_exhaust_weightTwo_H0 h
  · exact proposed_five_not_exhaust_weightThree_H1 h

end Integration.OggSSP2BActualFiveLengthNoGo
