import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleEighthRemainder
import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleV4EndpointAbsorb

/-!
# Post-sixth strict-ABSORB surface

The preferred local source is now recut as

  complete quartic
    + signed sixth harmonic
    + absolute eighth-and-higher debt.

The signed sixth carrier is never replaced by its absolute moment in this
module.  Only the beyond-sixth residual is majorized.

The eighth debt is paid against the same literal expanded zero count already
used by V4/H4.  Its profile norm is cross-welded to the same selected-witness
G1 fourth-Lipschitz constant.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Interval Real

namespace Synthesis

def quarticSignedPoleLocalEighthPhysicalEnvelope
    (t eta : ℝ) : ℝ :=
  let r := quarticSignedPoleLocalHalfWidth t eta
  (1/30000 : ℝ) * (1/2 : ℝ)^8
    + (1/17000 : ℝ) * r^8
    + (1/300 : ℝ)
        * ((1/2 : ℝ)^2 * r^6
          + (1/2 : ℝ)^4 * r^4
          + (1/2 : ℝ)^6 * r^2)

theorem quarticSignedPoleLocalEighthPhysicalEnvelope_nonneg
    {t eta : ℝ}
    (ht : 0 <= t)
    (heta : 0 <= eta) :
    0 <= quarticSignedPoleLocalEighthPhysicalEnvelope t eta := by
  unfold quarticSignedPoleLocalEighthPhysicalEnvelope
    quarticSignedPoleLocalHalfWidth
  positivity

theorem QuarticFourSignedPolePair.literalCompleteEighthPhysicalPolynomial_le_localEnvelope
    {t eta : ℝ}
    (ht : 0 < t)
    (heta : 0 <= eta)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hl : quarticSignedPoleLocal t eta rho) :
    W.literalCompleteEighthPhysicalPolynomial rho
      <= quarticSignedPoleLocalEighthPhysicalEnvelope t eta := by
  have hclosed :=
    (quarticSignedPoleLocal_iff_closed_ordinate_window
      ht heta rho).mp hl
  let r := quarticSignedPoleLocalHalfWidth t eta
  have hr0 : 0 <= r := by
    dsimp [r, quarticSignedPoleLocalHalfWidth]
    positivity
  have hdelta :
      |(rho : ℂ).im-t| <= r := by
    rw [abs_le]
    constructor <;> dsimp [r] at hclosed ⊢ <;> linarith
  have ha := zetaZero_height_abs_le_half rho

  have hd2 : |(rho : ℂ).im-t|^2 <= r^2 := by gcongr
  have hd4 : |(rho : ℂ).im-t|^4 <= r^4 := by gcongr
  have hd6 : |(rho : ℂ).im-t|^6 <= r^6 := by gcongr
  have hd8 : |(rho : ℂ).im-t|^8 <= r^8 := by gcongr

  have ha2 : |heightOf rho|^2 <= (1/2 : ℝ)^2 := by gcongr
  have ha4 : |heightOf rho|^4 <= (1/2 : ℝ)^4 := by gcongr
  have ha6 : |heightOf rho|^6 <= (1/2 : ℝ)^6 := by gcongr
  have ha8 : |heightOf rho|^8 <= (1/2 : ℝ)^8 := by gcongr

  have ha2' : heightOf rho^2 <= (1/2 : ℝ)^2 := by
    rw [← sq_abs]
    exact ha2
  have ha4' : heightOf rho^4 <= (1/2 : ℝ)^4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 <= heightOf rho^4)]
    exact ha4
  have ha6' : heightOf rho^6 <= (1/2 : ℝ)^6 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 <= heightOf rho^6)]
    exact ha6
  have ha8' : heightOf rho^8 <= (1/2 : ℝ)^8 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 <= heightOf rho^8)]
    exact ha8

  have hd2' : ((rho : ℂ).im-t)^2 <= r^2 := by
    rw [← sq_abs]
    exact hd2
  have hd4' : ((rho : ℂ).im-t)^4 <= r^4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 <= ((rho : ℂ).im-t)^4)]
    exact hd4
  have hd6' : ((rho : ℂ).im-t)^6 <= r^6 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 <= ((rho : ℂ).im-t)^6)]
    exact hd6
  have hd8' : ((rho : ℂ).im-t)^8 <= r^8 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 <= ((rho : ℂ).im-t)^8)]
    exact hd8

  unfold QuarticFourSignedPolePair.literalCompleteEighthPhysicalPolynomial
    quarticSignedPoleLocalEighthPhysicalEnvelope
  dsimp [r]
  gcongr

def QuarticFourSignedPolePair.literalLocalEighthDebtAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ := by
  classical
  exact ∑ rho ∈ centeredZeroFinset t n,
    if quarticSignedPoleLocal t eta rho then
      if _h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
        W.literalCompleteEighthRemainderBound rho
      else
        0
    else
      0

theorem QuarticFourSignedPolePair.literalLocalBeyondSixthRemainderAt_le_eighthDebt
    {t : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalBeyondSixthRemainderAt
        quarticSignedPoleCanonicalLocalRadius n
      <=
    W.literalLocalEighthDebtAt
        quarticSignedPoleCanonicalLocalRadius n := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalBeyondSixthRemainderAt
    QuarticFourSignedPolePair.literalLocalEighthDebtAt
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hl :
      quarticSignedPoleLocal
        t quarticSignedPoleCanonicalLocalRadius rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · have ha :=
        quarticSignedPole_normalizedHeight_abs_le_canonicalRadius
          ht rho
      have hq :
          |((rho : ℂ).im-t)/(t/16)|
            <= quarticSignedPoleCanonicalLocalRadius := by
        exact hl
      have hrem :=
        W.literalCompleteJointBeyondSixthRemainder_abs_le
          (by linarith : 0 < t) rho ha hq
      simp [hl,hoff]
      exact (le_abs_self _).trans hrem
    · simp [hl,hoff]
      exact W.literalCompleteEighthPhysicalPolynomial_nonneg rho
        |> fun hp => by
          unfold QuarticFourSignedPolePair.literalCompleteEighthRemainderBound
          positivity
  · simp [hl]
    unfold QuarticFourSignedPolePair.literalCompleteEighthRemainderBound
    positivity

theorem QuarticFourSignedPolePair.literalLocalEighthDebtAt_le_envelope_mul_multiplicity
    {t eta : ℝ}
    (ht : 0 < t)
    (heta : 0 <= eta)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalEighthDebtAt eta n
      <=
    (W.signedProfileAbsMomentEight
        * quarticSignedPoleLocalEighthPhysicalEnvelope t eta
        / (t/16)^10)
      * (W.literalLocalMultiplicityAt eta n : ℝ) := by
  classical
  have hcoef :
      0 <=
        W.signedProfileAbsMomentEight
          * quarticSignedPoleLocalEighthPhysicalEnvelope t eta
          / (t/16)^10 := by
    have henv :=
      quarticSignedPoleLocalEighthPhysicalEnvelope_nonneg
        ht.le heta
    positivity
  unfold QuarticFourSignedPolePair.literalLocalEighthDebtAt
    QuarticFourSignedPolePair.literalLocalMultiplicityAt
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hl : quarticSignedPoleLocal t eta rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · have hp :=
        W.literalCompleteEighthPhysicalPolynomial_le_localEnvelope
          ht heta hl
      have hm :
          0 <= ((zetaZeroConfig).mult (rho : ℂ) : ℝ) := by
        positivity
      have hM8 : 0 <= W.signedProfileAbsMomentEight :=
        W.signedProfileAbsMomentEight_nonneg
      have hden : 0 < (t/16)^10 := by positivity
      simp [hl,hoff,
        QuarticFourSignedPolePair.literalCompleteEighthRemainderBound]
      apply div_le_div_of_nonneg_right _ hden.le
      have hscale :
          ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
            * W.signedProfileAbsMomentEight
            * W.literalCompleteEighthPhysicalPolynomial rho
          <=
          ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
            * W.signedProfileAbsMomentEight
            * quarticSignedPoleLocalEighthPhysicalEnvelope t eta := by
        gcongr
      simpa [mul_assoc, mul_left_comm, mul_comm] using hscale
    · simp [hl,hoff]
      exact mul_nonneg hcoef (by positivity)
  · simp [hl]
    exact mul_nonneg hcoef (by positivity)

theorem QuarticFourSignedPolePair.literalLocalEighthDebtAt_le_expandedWindowN
    {t eta : ℝ}
    (ht : 0 < t)
    (heta : 0 <= eta)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalEighthDebtAt eta n
      <=
    (W.signedProfileAbsMomentEight
        * quarticSignedPoleLocalEighthPhysicalEnvelope t eta
        / (t/16)^10)
      *
    (zetaZeroConfig.N
      (t - quarticSignedPoleLocalHalfWidth t eta - 1)
      (t + quarticSignedPoleLocalHalfWidth t eta) : ℝ) := by
  have hdebt :=
    W.literalLocalEighthDebtAt_le_envelope_mul_multiplicity
      ht heta n
  have hmultNat :=
    W.literalLocalMultiplicityAt_le_expandedWindowN
      ht heta (eta:=eta) n
  have hmult :
      (W.literalLocalMultiplicityAt eta n : ℝ)
        <=
      (zetaZeroConfig.N
        (t - quarticSignedPoleLocalHalfWidth t eta - 1)
        (t + quarticSignedPoleLocalHalfWidth t eta) : ℝ) := by
    exact_mod_cast hmultNat
  have hcoef :
      0 <=
        W.signedProfileAbsMomentEight
          * quarticSignedPoleLocalEighthPhysicalEnvelope t eta
          / (t/16)^10 := by
    have henv :=
      quarticSignedPoleLocalEighthPhysicalEnvelope_nonneg
        ht.le heta
    positivity
  exact hdebt.trans
    (mul_le_mul_of_nonneg_left hmult hcoef)

theorem QuarticFourSignedPolePair.literalLocalEighthDebtAt_le_G1_expandedWindowN
    {t eta : ℝ}
    (ht : 0 < t)
    (heta : 0 <= eta)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalEighthDebtAt eta n
      <=
    (((Real.pi+1)^2 * W.fourthLipschitz)
        * quarticSignedPoleLocalEighthPhysicalEnvelope t eta
        / (t/16)^10)
      *
    (zetaZeroConfig.N
      (t - quarticSignedPoleLocalHalfWidth t eta - 1)
      (t + quarticSignedPoleLocalHalfWidth t eta) : ℝ) := by
  have hbase :=
    W.literalLocalEighthDebtAt_le_expandedWindowN
      ht heta n
  have hM8 :=
    W.signedProfileAbsMomentEight_le_supportSq_mul_fourthLipschitz
  have henv :
      0 <= quarticSignedPoleLocalEighthPhysicalEnvelope t eta :=
    quarticSignedPoleLocalEighthPhysicalEnvelope_nonneg ht.le heta
  have hden : 0 < (t/16)^10 := by positivity
  have hcoef :
      W.signedProfileAbsMomentEight
          * quarticSignedPoleLocalEighthPhysicalEnvelope t eta
          / (t/16)^10
        <=
      ((Real.pi+1)^2 * W.fourthLipschitz)
          * quarticSignedPoleLocalEighthPhysicalEnvelope t eta
          / (t/16)^10 := by
    apply div_le_div_of_nonneg_right _ hden.le
    exact mul_le_mul_of_nonneg_right hM8 henv
  have hN :
      0 <=
      (zetaZeroConfig.N
        (t - quarticSignedPoleLocalHalfWidth t eta - 1)
        (t + quarticSignedPoleLocalHalfWidth t eta) : ℝ) := by
    positivity
  exact hbase.trans
    (mul_le_mul_of_nonneg_right hcoef hN)


theorem QuarticFourSignedPolePair.literalOffOrdExactAt_le_phase_add_signedSixth_add_eighth_add_far
    {t : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalOffOrdExactAt n
      <=
    - W.targetStrength / (6 * (t/16)^6)
      *
      W.literalLocalFourthPhaseMomentAt
        quarticSignedPoleCanonicalLocalRadius n
      +
    W.literalLocalSignedSixthHarmonicAt
        quarticSignedPoleCanonicalLocalRadius n
      +
    W.literalLocalEighthDebtAt
        quarticSignedPoleCanonicalLocalRadius n
      +
    W.literalFarExactAt
        quarticSignedPoleCanonicalLocalRadius n := by
  have htpos : 0 < t := by linarith
  rw [W.literalOffOrdExactAt_eq_local_add_farExact]
  rw [W.literalLocalExactAt_eq_fourthHarmonic_add_remainder htpos]
  rw [W.literalLocalCompleteRemainderAt_eq_signedSixth_add_beyond]
  rw [W.literalLocalFourthHarmonicAt_eq_phaseMoment
      htpos
      (eta:=quarticSignedPoleCanonicalLocalRadius)
      n]
  have hbeyond :=
    W.literalLocalBeyondSixthRemainderAt_le_eighthDebt ht n
  linarith

theorem QuarticFourSignedPolePair.literalLocalFourthPhaseMomentAt_ge_corrected_scalar
    {t EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hn :
      quarticSignedPoleLocalHalfWidth
          t quarticSignedPoleCanonicalLocalRadius
        < (n : ℝ))
    (hV :
      |quarticSignedPoleRvMVerticalFourthDiscrepancy
        t
        (quarticSignedPoleLocalHalfWidth
          t quarticSignedPoleCanonicalLocalRadius)|
        <= EV) :
    -EV
      -
    (3/2 : ℝ)
      * quarticSignedPoleLocalHalfWidth
          t quarticSignedPoleCanonicalLocalRadius ^ 2
      *
    (zetaZeroConfig.N
      (t
        - quarticSignedPoleLocalHalfWidth
            t quarticSignedPoleCanonicalLocalRadius
        - 1)
      (t
        + quarticSignedPoleLocalHalfWidth
            t quarticSignedPoleCanonicalLocalRadius) : ℝ)
      +
    (2/5 : ℝ)
      * quarticSignedPoleLocalHalfWidth
          t quarticSignedPoleCanonicalLocalRadius ^ 5
      * quarticSignedPoleMuLowerEnvelope
          (t
            - quarticSignedPoleLocalHalfWidth
                t quarticSignedPoleCanonicalLocalRadius)
      <=
    W.literalLocalFourthPhaseMomentAt
        quarticSignedPoleCanonicalLocalRadius n := by
  have htpos : 0 < t := by linarith
  have heta :
      0 <= quarticSignedPoleCanonicalLocalRadius :=
    quarticSignedPoleCanonicalLocalRadius_pos.le
  have hleft :
      1 <=
        t
          - quarticSignedPoleLocalHalfWidth
              t quarticSignedPoleCanonicalLocalRadius := by
    unfold quarticSignedPoleLocalHalfWidth
      quarticSignedPoleCanonicalLocalRadius
    have hden : 0 < Real.pi + 1 := by positivity
    have hetaHi :
        1 / (Real.pi + 1) <= 1/4 := by
      rw [div_le_iff₀ hden]
      nlinarith [Real.pi_gt_three]
    nlinarith
  have hang :=
    W.literalLocalCenteredFourthAngularAt_lower
      htpos heta n hn hV
  have hcenter :
      W.literalLocalFourthPhaseMomentAt
          quarticSignedPoleCanonicalLocalRadius n
        =
      W.literalLocalCenteredFourthAngularAt
          quarticSignedPoleCanonicalLocalRadius n
        +
      quarticSignedPoleLocalMuVerticalFourthMoment
        t quarticSignedPoleCanonicalLocalRadius := by
    unfold QuarticFourSignedPolePair.literalLocalCenteredFourthAngularAt
    ring
  have hmultNat :=
    W.literalLocalMultiplicityAt_le_expandedWindowN
      htpos heta
      (eta:=quarticSignedPoleCanonicalLocalRadius)
      n
  have hmult :
      (W.literalLocalMultiplicityAt
          quarticSignedPoleCanonicalLocalRadius n : ℝ)
        <=
      (zetaZeroConfig.N
        (t
          - quarticSignedPoleLocalHalfWidth
              t quarticSignedPoleCanonicalLocalRadius
          - 1)
        (t
          + quarticSignedPoleLocalHalfWidth
              t quarticSignedPoleCanonicalLocalRadius) : ℝ) := by
    exact_mod_cast hmultNat
  have hmu :=
    quarticSignedPoleLocalMuVerticalFourthMoment_ge_leftEnvelope_local
      htpos heta hleft
  have hr2 :
      0 <=
        (3/2 : ℝ)
          * quarticSignedPoleLocalHalfWidth
              t quarticSignedPoleCanonicalLocalRadius ^ 2 := by
    positivity
  have hmultScaled :=
    mul_le_mul_of_nonneg_left hmult hr2
  rw [hcenter]
  linarith

def QuarticFourSignedPolePair.postSixthV4H4AbsorbBudgetAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (EV : ℝ) (n : ℕ) : ℝ :=
  let eta := quarticSignedPoleCanonicalLocalRadius
  let r := quarticSignedPoleLocalHalfWidth t eta
  let NZ : ℝ :=
    (zetaZeroConfig.N (t-r-1) (t+r) : ℝ)
  (W.targetStrength / (6 * (t/16)^6))
    *
  (
    EV
      + (3/2 : ℝ) * r^2 * NZ
      - (2/5 : ℝ) * r^5
          * quarticSignedPoleMuLowerEnvelope (t-r)
  )
    +
  W.literalLocalSignedSixthHarmonicAt eta n
    +
  (W.signedProfileAbsMomentEight
      * quarticSignedPoleLocalEighthPhysicalEnvelope t eta
      / (t/16)^10)
    * NZ
    +
  W.literalFarExactAt eta n

def QuarticFourSignedPolePair.postSixthV4H4G1BudgetAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (EV : ℝ) (n : ℕ) : ℝ :=
  let eta := quarticSignedPoleCanonicalLocalRadius
  let r := quarticSignedPoleLocalHalfWidth t eta
  let NZ : ℝ :=
    (zetaZeroConfig.N (t-r-1) (t+r) : ℝ)
  (W.targetStrength / (6 * (t/16)^6))
    *
  (
    EV
      + (3/2 : ℝ) * r^2 * NZ
      - (2/5 : ℝ) * r^5
          * quarticSignedPoleMuLowerEnvelope (t-r)
  )
    +
  W.literalLocalSignedSixthHarmonicAt eta n
    +
  (((Real.pi+1)^2 * W.fourthLipschitz)
      * quarticSignedPoleLocalEighthPhysicalEnvelope t eta
      / (t/16)^10)
    * NZ
    +
  W.literalFarExactAt eta n

theorem QuarticFourSignedPolePair.literalOffOrdExactAt_le_postSixthV4H4AbsorbBudgetAt
    {t EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hn :
      quarticSignedPoleLocalHalfWidth
          t quarticSignedPoleCanonicalLocalRadius
        < (n : ℝ))
    (hV :
      |quarticSignedPoleRvMVerticalFourthDiscrepancy
        t
        (quarticSignedPoleLocalHalfWidth
          t quarticSignedPoleCanonicalLocalRadius)|
        <= EV) :
    W.literalOffOrdExactAt n
      <= W.postSixthV4H4AbsorbBudgetAt EV n := by
  have hsource :=
    W.literalOffOrdExactAt_le_phase_add_signedSixth_add_eighth_add_far
      ht n
  have hphase :=
    W.literalLocalFourthPhaseMomentAt_ge_corrected_scalar
      ht n hn hV
  have hcoef :
      0 <= W.targetStrength / (6 * (t/16)^6) := by
    positivity
  have hlead :=
    mul_le_mul_of_nonneg_left hphase hcoef
  have heighth :=
    W.literalLocalEighthDebtAt_le_expandedWindowN
      (by linarith : 0 < t)
      quarticSignedPoleCanonicalLocalRadius_pos.le
      n
  unfold QuarticFourSignedPolePair.postSixthV4H4AbsorbBudgetAt
  dsimp
  nlinarith

theorem QuarticFourSignedPolePair.postSixthV4H4AbsorbBudgetAt_le_G1
    {t EV : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.postSixthV4H4AbsorbBudgetAt EV n
      <= W.postSixthV4H4G1BudgetAt EV n := by
  let eta := quarticSignedPoleCanonicalLocalRadius
  let r := quarticSignedPoleLocalHalfWidth t eta
  let NZ : ℝ :=
    (zetaZeroConfig.N (t-r-1) (t+r) : ℝ)
  have hM8 :=
    W.signedProfileAbsMomentEight_le_supportSq_mul_fourthLipschitz
  have henv :
      0 <= quarticSignedPoleLocalEighthPhysicalEnvelope t eta :=
    quarticSignedPoleLocalEighthPhysicalEnvelope_nonneg
      ht.le quarticSignedPoleCanonicalLocalRadius_pos.le
  have hden : 0 < (t/16)^10 := by positivity
  have hcoef :
      W.signedProfileAbsMomentEight
          * quarticSignedPoleLocalEighthPhysicalEnvelope t eta
          / (t/16)^10
        <=
      ((Real.pi+1)^2 * W.fourthLipschitz)
          * quarticSignedPoleLocalEighthPhysicalEnvelope t eta
          / (t/16)^10 := by
    apply div_le_div_of_nonneg_right _ hden.le
    exact mul_le_mul_of_nonneg_right hM8 henv
  have hNZ : 0 <= NZ := by
    dsimp [NZ]
    positivity
  have he := mul_le_mul_of_nonneg_right hcoef hNZ
  unfold QuarticFourSignedPolePair.postSixthV4H4AbsorbBudgetAt
    QuarticFourSignedPolePair.postSixthV4H4G1BudgetAt
  dsimp [eta,r,NZ]
  linarith

end Synthesis
