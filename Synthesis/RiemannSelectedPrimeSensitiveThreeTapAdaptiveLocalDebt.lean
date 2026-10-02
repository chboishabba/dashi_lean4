import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdaptiveJet
import Synthesis.RiemannProjectiveQuarticFourWindowSignedPolePostSixthAbsorb

/-!
# Finite adaptive-local carrier for the transformed three-tap profile

This module turns the exact normalized transformed pair kernel into the same
finite-window architecture used by the original signed-pole proof.

For each zero rho we use
  mult(rho) / r^2 * K_eps(alpha_rho,q_rho),
where K_eps is the actual transformed normalized pair kernel.

On the adaptive-local lane this splits exactly into
  degree-six jet + eighth-order remainder.

The remainder debt is bounded by the transformed M8 coordinate times the
existing expanded local zero count.  The final identification of this carrier
with the transformed Zeta23 off-ordinate projective channel is deliberately
kept as a separate same-object weld.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators

def QuarticFourSignedPolePair.threeTapAdaptivePairTerm
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (rho : Zeros) : ℝ :=
  ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2
    *
  W.threeTapNormalizedPairKernel eps
    (heightOf rho / (t/16))
    (quarticSignedPoleNormalizedOrdinateOffset t rho)

def QuarticFourSignedPolePair.threeTapAdaptiveJetTerm
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (rho : Zeros) : ℝ :=
  ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2
    *
  W.threeTapNormalizedDegreeSixJet eps
    (heightOf rho / (t/16))
    (quarticSignedPoleNormalizedOrdinateOffset t rho)

def QuarticFourSignedPolePair.threeTapAdaptiveRemainderTerm
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (rho : Zeros) : ℝ :=
  ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2
    *
  W.threeTapNormalizedMixedSixthRemainder eps
    (heightOf rho / (t/16))
    (quarticSignedPoleNormalizedOrdinateOffset t rho)

theorem QuarticFourSignedPolePair.threeTapAdaptivePairTerm_eq_jet_add_remainder
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.threeTapAdaptivePairTerm eps rho
      =
    W.threeTapAdaptiveJetTerm eps rho
      + W.threeTapAdaptiveRemainderTerm eps rho := by
  unfold QuarticFourSignedPolePair.threeTapAdaptivePairTerm
    QuarticFourSignedPolePair.threeTapAdaptiveJetTerm
    QuarticFourSignedPolePair.threeTapAdaptiveRemainderTerm
  rw [W.threeTapNormalizedPairKernel_eq_jet_add_remainder]
  ring

def QuarticFourSignedPolePair.threeTapAdaptiveLocalPairAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (n : ℕ) : ℝ := by
  classical
  exact ∑ rho ∈ centeredZeroFinset t n,
    if quarticSignedPoleThreeTapAdaptiveLocal W rho then
      W.threeTapAdaptivePairTerm eps rho
    else 0

def QuarticFourSignedPolePair.threeTapAdaptiveLocalJetAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (n : ℕ) : ℝ := by
  classical
  exact ∑ rho ∈ centeredZeroFinset t n,
    if quarticSignedPoleThreeTapAdaptiveLocal W rho then
      W.threeTapAdaptiveJetTerm eps rho
    else 0

def QuarticFourSignedPolePair.threeTapAdaptiveLocalRemainderAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (n : ℕ) : ℝ := by
  classical
  exact ∑ rho ∈ centeredZeroFinset t n,
    if quarticSignedPoleThreeTapAdaptiveLocal W rho then
      W.threeTapAdaptiveRemainderTerm eps rho
    else 0

def QuarticFourSignedPolePair.threeTapAdaptiveLocalRemainderDebtAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (n : ℕ) : ℝ := by
  classical
  exact ∑ rho ∈ centeredZeroFinset t n,
    if quarticSignedPoleThreeTapAdaptiveLocal W rho then
      |W.threeTapAdaptiveRemainderTerm eps rho|
    else 0

theorem QuarticFourSignedPolePair.threeTapAdaptiveLocalPairAt_eq_jet_add_remainder
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.threeTapAdaptiveLocalPairAt eps n
      =
    W.threeTapAdaptiveLocalJetAt eps n
      + W.threeTapAdaptiveLocalRemainderAt eps n := by
  classical
  unfold QuarticFourSignedPolePair.threeTapAdaptiveLocalPairAt
    QuarticFourSignedPolePair.threeTapAdaptiveLocalJetAt
    QuarticFourSignedPolePair.threeTapAdaptiveLocalRemainderAt
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hl : quarticSignedPoleThreeTapAdaptiveLocal W rho
  · simp [hl, W.threeTapAdaptivePairTerm_eq_jet_add_remainder]
  · simp [hl]

theorem QuarticFourSignedPolePair.threeTapAdaptiveLocalRemainderAt_le_debt
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.threeTapAdaptiveLocalRemainderAt eps n
      <= W.threeTapAdaptiveLocalRemainderDebtAt eps n := by
  classical
  unfold QuarticFourSignedPolePair.threeTapAdaptiveLocalRemainderAt
    QuarticFourSignedPolePair.threeTapAdaptiveLocalRemainderDebtAt
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hl : quarticSignedPoleThreeTapAdaptiveLocal W rho
  · simp [hl, le_abs_self]
  · simp [hl]

def QuarticFourSignedPolePair.threeTapAdaptiveMixedEnvelope
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  quarticSignedPoleMixedEighthEnvelope
    W.threeTapAdaptiveLocalRadius
    W.threeTapAdaptiveLocalRadius

theorem QuarticFourSignedPolePair.threeTapAdaptiveMixedEnvelope_nonneg
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    0 <= W.threeTapAdaptiveMixedEnvelope := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveMixedEnvelope
    quarticSignedPoleMixedEighthEnvelope
  positivity

theorem quarticSignedPoleMixedEighthEnvelope_le_of_abs_le
    {alpha q eta : ℝ}
    (heta : 0 <= eta)
    (ha : |alpha| <= eta)
    (hq : |q| <= eta) :
    quarticSignedPoleMixedEighthEnvelope alpha q
      <= quarticSignedPoleMixedEighthEnvelope eta eta := by
  have ha2 : alpha^2 <= eta^2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg alpha) ha 2
  have hq2 : q^2 <= eta^2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg q) hq 2
  have ha4 : alpha^4 <= eta^4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 <= alpha^4)]
    exact pow_le_pow_left₀ (abs_nonneg alpha) ha 4
  have hq4 : q^4 <= eta^4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 <= q^4)]
    exact pow_le_pow_left₀ (abs_nonneg q) hq 4
  have ha6 : alpha^6 <= eta^6 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 <= alpha^6)]
    exact pow_le_pow_left₀ (abs_nonneg alpha) ha 6
  have hq6 : q^6 <= eta^6 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 <= q^6)]
    exact pow_le_pow_left₀ (abs_nonneg q) hq 6
  have ha8 : alpha^8 <= eta^8 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 <= alpha^8)]
    exact pow_le_pow_left₀ (abs_nonneg alpha) ha 8
  have hq8 : q^8 <= eta^8 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 <= q^8)]
    exact pow_le_pow_left₀ (abs_nonneg q) hq 8
  unfold quarticSignedPoleMixedEighthEnvelope
  nlinarith [
    mul_le_mul ha2 hq6 (by positivity) (by positivity),
    mul_le_mul ha4 hq4 (by positivity) (by positivity),
    mul_le_mul ha6 hq2 (by positivity) (by positivity)]

theorem QuarticFourSignedPolePair.threeTapAdaptiveRemainderTerm_abs_le
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hl : quarticSignedPoleThreeTapAdaptiveLocal W rho) :
    |W.threeTapAdaptiveRemainderTerm eps rho|
      <=
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2
      *
    (W.threeTapAdaptiveMixedEnvelope
      * W.threeTapNormalizedProjectiveAbsMomentEight eps) := by
  have hr : 0 < t/16 := by linarith
  have hm : 0 <= ((zetaZeroConfig).mult (rho : ℂ) : ℝ) := by positivity
  have hcoef :
      0 <= ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2 := by
    positivity
  have hdom := W.threeTap_zero_mixed_domain ht hl
  have hrem :=
    W.threeTapNormalizedMixedSixthRemainder_abs_le hdom.1 hdom.2
  have henv :=
    quarticSignedPoleMixedEighthEnvelope_le_of_abs_le
      W.threeTapAdaptiveLocalRadius_pos.le hdom.1 hdom.2
  unfold QuarticFourSignedPolePair.threeTapAdaptiveRemainderTerm
  rw [abs_mul, abs_of_nonneg hcoef]
  calc
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2
      *
      |W.threeTapNormalizedMixedSixthRemainder eps
        (heightOf rho / (t/16))
        (quarticSignedPoleNormalizedOrdinateOffset t rho)|
      <=
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2
      *
      (quarticSignedPoleMixedEighthEnvelope
        (heightOf rho / (t/16))
        (quarticSignedPoleNormalizedOrdinateOffset t rho)
        * W.threeTapNormalizedProjectiveAbsMomentEight eps) :=
      mul_le_mul_of_nonneg_left hrem hcoef
    _ <=
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2
      *
      (W.threeTapAdaptiveMixedEnvelope
        * W.threeTapNormalizedProjectiveAbsMomentEight eps) := by
      unfold QuarticFourSignedPolePair.threeTapAdaptiveMixedEnvelope
      have hM :=
        W.threeTapNormalizedProjectiveAbsMoment_nonneg (eps:=eps) 8
      gcongr
    _ = _ := by rfl

theorem QuarticFourSignedPolePair.threeTapAdaptiveLocalRemainderDebtAt_le_multiplicity
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.threeTapAdaptiveLocalRemainderDebtAt eps n
      <=
    ((W.threeTapAdaptiveMixedEnvelope
        * W.threeTapNormalizedProjectiveAbsMomentEight eps)
      / (t/16)^2)
      *
    (W.literalLocalMultiplicityAt
      W.threeTapAdaptiveLocalRadius n : ℝ) := by
  classical
  have hcoef :
      0 <=
      (W.threeTapAdaptiveMixedEnvelope
        * W.threeTapNormalizedProjectiveAbsMomentEight eps)
        / (t/16)^2 := by
    have hE := W.threeTapAdaptiveMixedEnvelope_nonneg
    have hM := W.threeTapNormalizedProjectiveAbsMoment_nonneg (eps:=eps) 8
    positivity
  unfold QuarticFourSignedPolePair.threeTapAdaptiveLocalRemainderDebtAt
    QuarticFourSignedPolePair.literalLocalMultiplicityAt
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hl : quarticSignedPoleThreeTapAdaptiveLocal W rho
  · have hpoint := W.threeTapAdaptiveRemainderTerm_abs_le ht hl
    have hlocal :
        quarticSignedPoleLocal
          t W.threeTapAdaptiveLocalRadius rho := hl
    simp [hl, hlocal]
    have hm : 0 <= (zetaZeroConfig.mult (rho : ℂ) : ℝ) := by positivity
    calc
      |W.threeTapAdaptiveRemainderTerm eps rho|
        <=
      (zetaZeroConfig.mult (rho : ℂ) : ℝ) / (t/16)^2
        *
      (W.threeTapAdaptiveMixedEnvelope
        * W.threeTapNormalizedProjectiveAbsMomentEight eps) := hpoint
      _ =
      ((W.threeTapAdaptiveMixedEnvelope
          * W.threeTapNormalizedProjectiveAbsMomentEight eps)
        / (t/16)^2)
        * (zetaZeroConfig.mult (rho : ℂ) : ℝ) := by ring
  · have hnot :
        ¬ quarticSignedPoleLocal
          t W.threeTapAdaptiveLocalRadius rho := by
      exact hl
    simp [hl, hnot]
    exact mul_nonneg hcoef (by positivity)

theorem QuarticFourSignedPolePair.threeTapAdaptiveLocalRemainderDebtAt_le_expandedWindowN
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.threeTapAdaptiveLocalRemainderDebtAt eps n
      <=
    ((W.threeTapAdaptiveMixedEnvelope
        * W.threeTapNormalizedProjectiveAbsMomentEight eps)
      / (t/16)^2)
      *
    (zetaZeroConfig.N
      (t - quarticSignedPoleLocalHalfWidth
        t W.threeTapAdaptiveLocalRadius - 1)
      (t + quarticSignedPoleLocalHalfWidth
        t W.threeTapAdaptiveLocalRadius) : ℝ) := by
  have hdebt :=
    W.threeTapAdaptiveLocalRemainderDebtAt_le_multiplicity ht n
  have hmultNat :=
    W.literalLocalMultiplicityAt_le_expandedWindowN
      (by linarith : 0 < t)
      W.threeTapAdaptiveLocalRadius_pos.le
      (eta:=W.threeTapAdaptiveLocalRadius) n
  have hmult :
      (W.literalLocalMultiplicityAt
        W.threeTapAdaptiveLocalRadius n : ℝ)
      <=
      (zetaZeroConfig.N
        (t - quarticSignedPoleLocalHalfWidth
          t W.threeTapAdaptiveLocalRadius - 1)
        (t + quarticSignedPoleLocalHalfWidth
          t W.threeTapAdaptiveLocalRadius) : ℝ) := by
    exact_mod_cast hmultNat
  have hcoef :
      0 <=
      (W.threeTapAdaptiveMixedEnvelope
        * W.threeTapNormalizedProjectiveAbsMomentEight eps)
        / (t/16)^2 := by
    have hE := W.threeTapAdaptiveMixedEnvelope_nonneg
    have hM := W.threeTapNormalizedProjectiveAbsMoment_nonneg (eps:=eps) 8
    positivity
  exact hdebt.trans
    (mul_le_mul_of_nonneg_left hmult hcoef)

/-- Explicit same-object seam still required for the transformed completed
off-ordinate channel.  It is intentionally a proposition, not an assumption
hidden inside the adaptive budget. -/
def QuarticFourSignedPolePair.ThreeTapAdaptiveOffOrdCarrierWeld
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : Prop :=
  W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
    =
  (1/2 : ℝ) * ∑' rho : Zeros,
    W.threeTapAdaptivePairTerm eps rho

end Synthesis
