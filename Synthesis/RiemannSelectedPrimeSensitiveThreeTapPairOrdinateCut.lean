import Synthesis.RiemannSelectedPrimeSensitiveThreeTapKernelAlphaEnvelope
import Zeta23Bridge.OffOrdinateCutoffCarrier

/-!
# Finite-ordinate core plus residual adverse tail

After the signed pair cut, only the nonnegative adverse pair mass must be paid.
This file introduces an arbitrary physical ordinate cutoff `R` using the existing
literal `nearOffFinset`.  The near adverse mass is therefore a finite, exact
same-object sum.  The residual adverse tail is defined by subtraction from the
absolutely convergent total adverse mass.

No absolute value is applied to the original signed pair series and no bound on
the residual tail is asserted.  This is the finite/infinite seam required by a
subsequent RvM/Abel or oscillatory-decay estimate.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators
open Zeta23Bridge.OffOrdinateCutoffCarrier

/-- Finite adverse mass inside a literal physical ordinate window. -/
def QuarticFourSignedPolePair.threeTapPairAdverseNearAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps R : ℝ) : ℝ :=
  ∑ sigma ∈ nearOffFinset t R,
    W.threeTapPairAdversePart eps (sigma : Zeros)

/-- Residual adverse tail after removing the finite literal core. -/
def QuarticFourSignedPolePair.threeTapPairAdverseFarAfter
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps R : ℝ) : ℝ :=
  (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      W.threeTapPairAdversePart eps (sigma : Zeros))
    - W.threeTapPairAdverseNearAt eps R

theorem QuarticFourSignedPolePair.threeTap_pair_adverse_tsum_eq_near_add_far
    {t eps R : ℝ}
    (W : QuarticFourSignedPolePair t) :
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      W.threeTapPairAdversePart eps (sigma : Zeros))
      =
    W.threeTapPairAdverseNearAt eps R
      + W.threeTapPairAdverseFarAfter eps R := by
  unfold QuarticFourSignedPolePair.threeTapPairAdverseFarAfter
  ring

theorem QuarticFourSignedPolePair.threeTapPairAdverseNearAt_nonneg
    {t eps R : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.threeTapPairAdverseNearAt eps R := by
  classical
  unfold QuarticFourSignedPolePair.threeTapPairAdverseNearAt
  exact Finset.sum_nonneg fun sigma hsigma =>
    W.threeTapPairAdversePart_nonneg (eps:=eps) (sigma : Zeros)

/-- Exact PASS surface after the finite/infinite adverse split. -/
theorem QuarticFourSignedPolePair.threeTapResonancePaidCost_neg_of_near_add_far_lt
    {t eps R : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hcut :
      (1/2 : ℝ) *
        (W.threeTapPairAdverseNearAt eps R
          + W.threeTapPairAdverseFarAfter eps R)
        < W.threeTapAdaptiveLocalExact eps
            - W.threeTapResonanceCompensation eps) :
    W.threeTapResonancePaidCost eps < 0 := by
  apply W.threeTapResonancePaidCost_neg_of_adverse_tsum_lt ht
  rw [W.threeTap_pair_adverse_tsum_eq_near_add_far]
  exact hcut

/-- Producer-facing sufficient condition: a finite-core upper bound and a
residual-tail upper bound add directly, with no charge for favorable pairs. -/
theorem QuarticFourSignedPolePair.threeTapResonancePaidCost_neg_of_near_far_bounds
    {t eps R Bnear Bfar : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hnear : W.threeTapPairAdverseNearAt eps R <= Bnear)
    (hfar : W.threeTapPairAdverseFarAfter eps R <= Bfar)
    (hbudget :
      (1/2 : ℝ) * (Bnear + Bfar)
        < W.threeTapAdaptiveLocalExact eps
            - W.threeTapResonanceCompensation eps) :
    W.threeTapResonancePaidCost eps < 0 := by
  apply W.threeTapResonancePaidCost_neg_of_near_add_far_lt
    (R:=R) ht
  have hsum :
      W.threeTapPairAdverseNearAt eps R
        + W.threeTapPairAdverseFarAfter eps R
      <= Bnear + Bfar := add_le_add hnear hfar
  have hscaled :=
    mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ) <= 1/2)
  exact lt_of_le_of_lt hscaled hbudget

/-- Direct near-line PASS from separately paid finite-core and adverse-tail
bounds. -/
theorem QuarticFourSignedPolePair.exists_threeTapResonantTerminalProfile_pos_right_of_near_far_bounds
    {t eps mult R Bnear Bfar : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (hnear : W.threeTapPairAdverseNearAt eps R <= Bnear)
    (hfar : W.threeTapPairAdverseFarAfter eps R <= Bfar)
    (hbudget :
      (1/2 : ℝ) * (Bnear + Bfar)
        < W.threeTapAdaptiveLocalExact eps
            - W.threeTapResonanceCompensation eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a -> a < delta ->
        0 < W.threeTapAdaptiveTerminalProfile eps mult a := by
  apply W.exists_threeTapResonantTerminalProfile_pos_right_of_paidCost_neg
    ht hphase
  exact W.threeTapResonancePaidCost_neg_of_near_far_bounds
    (R:=R) ht hnear hfar hbudget

end Synthesis
