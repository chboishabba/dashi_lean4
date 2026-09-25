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
  · simp [hl]

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
  rw [W.literalOffOrdExactAt_eq_local_add_far]
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


/-!
## Signed-sixth cone split

The degree-six physical angular polynomial factors exactly as

  (a^2-d^2) * (a^4 - 14*a^2*d^2 + d^4).

Hence the outer cone 16*a^2 <= d^2 is favorable whenever the selected signed
sixth profile moment is nonnegative.  We keep those terms signed and drop
them only after proving their sum is nonpositive.

The complementary potentially adverse carrier is much smaller than the
canonical local window: since every zeta zero has |height| <= 1/2, failure of
the outer-cone condition forces d^2 < 4.  Thus the remaining sixth payment is
confined to the fixed physical strip |Im rho - t| < 2.
-/

def QuarticFourSignedPolePair.literalPhysicalSixthPhase
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) : ℝ :=
  let a := heightOf sigma
  let d := (sigma : ℂ).im - t
  a^6 - 15*a^4*d^2 + 15*a^2*d^4 - d^6

theorem QuarticFourSignedPolePair.literalPhysicalSixthPhase_factor
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) :
    W.literalPhysicalSixthPhase sigma
      =
    (heightOf sigma^2 - ((sigma : ℂ).im-t)^2)
      *
    (heightOf sigma^4
      - 14*heightOf sigma^2*((sigma : ℂ).im-t)^2
      + ((sigma : ℂ).im-t)^4) := by
  unfold QuarticFourSignedPolePair.literalPhysicalSixthPhase
  ring

theorem QuarticFourSignedPolePair.literalPhysicalSixthPhase_nonpos_of_outerCone
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (sigma : Zeros)
    (houter :
      16 * heightOf sigma^2
        <= ((sigma : ℂ).im-t)^2) :
    W.literalPhysicalSixthPhase sigma <= 0 := by
  rw [W.literalPhysicalSixthPhase_factor sigma]
  let a2 := heightOf sigma^2
  let d2 := ((sigma : ℂ).im-t)^2
  have ha2 : 0 <= a2 := by
    dsimp [a2]
    positivity
  have hd2 : 0 <= d2 := by
    dsimp [d2]
    positivity
  have hfirst : a2 - d2 <= 0 := by
    dsimp [a2,d2] at houter ⊢
    nlinarith
  have hmul : 16*a2*d2 <= d2*d2 := by
    exact mul_le_mul_of_nonneg_right
      (by simpa [a2,d2] using houter) hd2
  have hsecond :
      0 <=
        heightOf sigma^4
          - 14*heightOf sigma^2*((sigma : ℂ).im-t)^2
          + ((sigma : ℂ).im-t)^4 := by
    dsimp [a2,d2] at hmul
    nlinarith [sq_nonneg (heightOf sigma^2)]
  exact mul_nonpos_of_nonpos_of_nonneg hfirst hsecond

theorem QuarticFourSignedPolePair.literalCompleteJointSixthHarmonic_eq_physical
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (sigma : Zeros) :
    W.literalCompleteJointSixthHarmonic sigma
      =
    ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
      * W.signedProfileMomentSix
      * W.literalPhysicalSixthPhase sigma
      / (720 * (t/16)^8) := by
  unfold QuarticFourSignedPolePair.literalCompleteJointSixthHarmonic
    QuarticFourSignedPolePair.completeJointSixthHarmonic
    QuarticFourSignedPolePair.literalPhysicalSixthPhase
    quarticSignedPoleSixthPhaseReal
  dsimp
  have hr : t/16 ≠ 0 := by positivity
  field_simp [hr]
  ring

def QuarticFourSignedPolePair.literalLocalSignedSixthOuterAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ := by
  classical
  exact ∑ rho ∈ centeredZeroFinset t n,
    if quarticSignedPoleLocal t eta rho then
      if _h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
        if 16 * heightOf rho^2 <= ((rho : ℂ).im-t)^2 then
          W.literalCompleteJointSixthHarmonic rho
        else
          0
      else
        0
    else
      0

def QuarticFourSignedPolePair.literalLocalSignedSixthCentralAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ := by
  classical
  exact ∑ rho ∈ centeredZeroFinset t n,
    if quarticSignedPoleLocal t eta rho then
      if _h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
        if 16 * heightOf rho^2 <= ((rho : ℂ).im-t)^2 then
          0
        else
          W.literalCompleteJointSixthHarmonic rho
      else
        0
    else
      0

theorem QuarticFourSignedPolePair.literalLocalSignedSixthHarmonicAt_eq_outer_add_central
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalSignedSixthHarmonicAt eta n
      =
    W.literalLocalSignedSixthOuterAt eta n
      + W.literalLocalSignedSixthCentralAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalSignedSixthHarmonicAt
    QuarticFourSignedPolePair.literalLocalSignedSixthOuterAt
    QuarticFourSignedPolePair.literalLocalSignedSixthCentralAt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hl : quarticSignedPoleLocal t eta rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · by_cases houter :
        16 * heightOf rho^2 <= ((rho : ℂ).im-t)^2
      · simp [hl,hoff,houter]
      · simp [hl,hoff,houter]
    · simp [hl,hoff]
  · simp [hl]

theorem QuarticFourSignedPolePair.literalLocalSignedSixthOuterAt_nonpos
    {t eta : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hM6 : 0 <= W.signedProfileMomentSix)
    (n : ℕ) :
    W.literalLocalSignedSixthOuterAt eta n <= 0 := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalSignedSixthOuterAt
  apply Finset.sum_nonpos
  intro rho hrho
  by_cases hl : quarticSignedPoleLocal t eta rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · by_cases houter :
        16 * heightOf rho^2 <= ((rho : ℂ).im-t)^2
      · simp [hl,hoff,houter]
        rw [W.literalCompleteJointSixthHarmonic_eq_physical ht rho]
        have hm :
            0 <= ((zetaZeroConfig).mult (rho : ℂ) : ℝ) := by
          positivity
        have hp :=
          W.literalPhysicalSixthPhase_nonpos_of_outerCone rho houter
        have hnum :
            ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
                * W.signedProfileMomentSix
                * W.literalPhysicalSixthPhase rho
              <= 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos
            (mul_nonneg hm hM6) hp
        have hden : 0 <= 720 * (t/16)^8 := by positivity
        exact div_nonpos_of_nonpos_of_nonneg hnum hden
      · simp [hl,hoff,houter]
    · simp [hl,hoff]
  · simp [hl]

theorem QuarticFourSignedPolePair.literalLocalSignedSixthHarmonicAt_le_central
    {t eta : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hM6 : 0 <= W.signedProfileMomentSix)
    (n : ℕ) :
    W.literalLocalSignedSixthHarmonicAt eta n
      <= W.literalLocalSignedSixthCentralAt eta n := by
  rw [W.literalLocalSignedSixthHarmonicAt_eq_outer_add_central]
  have houter :=
    W.literalLocalSignedSixthOuterAt_nonpos ht hM6 n
  linarith

theorem QuarticFourSignedPolePair.sixthCentral_vertical_sq_lt_four
    {t : ℝ}
    (rho : Zeros)
    (hcentral :
      ¬ 16 * heightOf rho^2 <= ((rho : ℂ).im-t)^2) :
    ((rho : ℂ).im-t)^2 < 4 := by
  have ha := zetaZero_height_abs_le_half rho
  have ha2abs :
      |heightOf rho|^2 <= (1/2 : ℝ)^2 := by
    gcongr
  have ha2 :
      heightOf rho^2 <= (1/2 : ℝ)^2 := by
    rw [← sq_abs]
    exact ha2abs
  have hc :
      ((rho : ℂ).im-t)^2 < 16 * heightOf rho^2 := by
    exact lt_of_not_ge hcentral
  nlinarith



/-!
## Fixed-width central sixth debt

The previous cone split reduces the potentially adverse signed-sixth carrier,
under M6_signed(W) >= 0, to the complement of 16*a^2 <= d^2.  That complement
satisfies |d| < 2.  We now enlarge it harmlessly to the closed fixed strip
|d| <= 2 and pay only that strip.

The normalized radius 32/t has physical half-width exactly 2.  Therefore the
existing endpoint-safe local multiplicity theorem counts it by

  N(t-3,t+2).

No full canonical-local sixth count reappears.
-/

def quarticSignedPoleSixthFixedRadius (t : ℝ) : ℝ :=
  32 / t

theorem quarticSignedPoleSixthFixedRadius_nonneg
    {t : ℝ} (ht : 0 < t) :
    0 <= quarticSignedPoleSixthFixedRadius t := by
  unfold quarticSignedPoleSixthFixedRadius
  positivity

theorem quarticSignedPoleSixthFixedHalfWidth
    {t : ℝ} (ht : 0 < t) :
    quarticSignedPoleLocalHalfWidth
        t (quarticSignedPoleSixthFixedRadius t)
      = 2 := by
  unfold quarticSignedPoleLocalHalfWidth
    quarticSignedPoleSixthFixedRadius
  field_simp [ht.ne']
  ring

theorem quarticSignedPoleSixthCentral_mem_fixedLocal
    {t : ℝ} (ht : 0 < t)
    (rho : Zeros)
    (hcentral :
      ¬ 16 * heightOf rho^2 <= ((rho : ℂ).im-t)^2) :
    quarticSignedPoleLocal
      t (quarticSignedPoleSixthFixedRadius t) rho := by
  have hsquare :=
    QuarticFourSignedPolePair.sixthCentral_vertical_sq_lt_four
      (t:=t) rho hcentral
  have habs : |(rho : ℂ).im-t| < 2 := by
    have h0 : 0 <= |(rho : ℂ).im-t| := abs_nonneg _
    have heq :
        |(rho : ℂ).im-t|^2 = ((rho : ℂ).im-t)^2 := by
      rw [sq_abs]
    rw [← heq] at hsquare
    nlinarith
  have heta :=
    quarticSignedPoleSixthFixedRadius_nonneg ht
  rw [quarticSignedPoleLocal_iff_closed_ordinate_window
      ht heta rho]
  rw [quarticSignedPoleSixthFixedHalfWidth ht]
  rw [abs_lt] at habs
  constructor <;> linarith

theorem QuarticFourSignedPolePair.literalPhysicalSixthPhase_abs_le_128_of_fixedLocal
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hl :
      quarticSignedPoleLocal
        t (quarticSignedPoleSixthFixedRadius t) rho) :
    |W.literalPhysicalSixthPhase rho| <= 128 := by
  have heta :=
    quarticSignedPoleSixthFixedRadius_nonneg ht
  have hclosed :=
    (quarticSignedPoleLocal_iff_closed_ordinate_window
      ht heta rho).mp hl
  rw [quarticSignedPoleSixthFixedHalfWidth ht] at hclosed
  have hdabs : |(rho : ℂ).im-t| <= 2 := by
    rw [abs_le]
    constructor <;> linarith
  have haabs := zetaZero_height_abs_le_half rho

  have ha2 : heightOf rho^2 <= (1/2 : ℝ)^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (heightOf rho)) haabs 2
    rw [← abs_pow, abs_of_nonneg (sq_nonneg (heightOf rho))] at h
    simpa using h
  have ha4 : heightOf rho^4 <= (1/2 : ℝ)^4 := by
    have h := pow_le_pow_left₀ (abs_nonneg (heightOf rho)) haabs 4
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 <= heightOf rho^4)] at h
    simpa using h
  have ha6 : heightOf rho^6 <= (1/2 : ℝ)^6 := by
    have h := pow_le_pow_left₀ (abs_nonneg (heightOf rho)) haabs 6
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 <= heightOf rho^6)] at h
    simpa using h

  have hd2 : ((rho : ℂ).im-t)^2 <= (2 : ℝ)^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg ((rho : ℂ).im-t)) hdabs 2
    rw [← abs_pow, abs_of_nonneg (sq_nonneg ((rho : ℂ).im-t))] at h
    simpa using h
  have hd4 : ((rho : ℂ).im-t)^4 <= (2 : ℝ)^4 := by
    have h := pow_le_pow_left₀ (abs_nonneg ((rho : ℂ).im-t)) hdabs 4
    rw [← abs_pow, abs_of_nonneg (by positivity :
      0 <= ((rho : ℂ).im-t)^4)] at h
    simpa using h
  have hd6 : ((rho : ℂ).im-t)^6 <= (2 : ℝ)^6 := by
    have h := pow_le_pow_left₀ (abs_nonneg ((rho : ℂ).im-t)) hdabs 6
    rw [← abs_pow, abs_of_nonneg (by positivity :
      0 <= ((rho : ℂ).im-t)^6)] at h
    simpa using h

  have ha4d2 :
      heightOf rho^4 * ((rho : ℂ).im-t)^2 <= (1 : ℝ) := by
    have h :=
      mul_le_mul ha4 hd2
        (by positivity : 0 <= ((rho : ℂ).im-t)^2)
        (by positivity : 0 <= (1/2 : ℝ)^4)
    norm_num at h ⊢
    linarith
  have ha2d4 :
      heightOf rho^2 * ((rho : ℂ).im-t)^4 <= (4 : ℝ) := by
    have h :=
      mul_le_mul ha2 hd4
        (by positivity : 0 <= ((rho : ℂ).im-t)^4)
        (by positivity : 0 <= (1/2 : ℝ)^2)
    norm_num at h ⊢
    linarith

  unfold QuarticFourSignedPolePair.literalPhysicalSixthPhase
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (heightOf rho),
      sq_nonneg ((rho : ℂ).im-t),
      ha4d2, ha2d4]
  · nlinarith [sq_nonneg (heightOf rho),
      sq_nonneg ((rho : ℂ).im-t),
      ha4d2, ha2d4]

def QuarticFourSignedPolePair.literalFixedStripSixthDebtAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (n : ℕ) : ℝ := by
  classical
  exact ∑ rho ∈ centeredZeroFinset t n,
    if quarticSignedPoleLocal
        t (quarticSignedPoleSixthFixedRadius t) rho then
      if _h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
        |W.literalCompleteJointSixthHarmonic rho|
      else
        0
    else
      0

theorem QuarticFourSignedPolePair.literalLocalSignedSixthCentralAt_le_fixedStripDebt
    {t eta : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalSignedSixthCentralAt eta n
      <= W.literalFixedStripSixthDebtAt n := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalSignedSixthCentralAt
    QuarticFourSignedPolePair.literalFixedStripSixthDebtAt
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hl : quarticSignedPoleLocal t eta rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · by_cases houter :
        16 * heightOf rho^2 <= ((rho : ℂ).im-t)^2
      · simp [hl,hoff,houter]
        positivity
      · have hfixed :=
          quarticSignedPoleSixthCentral_mem_fixedLocal
            ht rho houter
        simp [hl,hoff,houter,hfixed]
        exact le_abs_self _
    · simp [hl,hoff]
  · simp [hl]

theorem QuarticFourSignedPolePair.literalCompleteJointSixthHarmonic_abs_le_fixed
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hl :
      quarticSignedPoleLocal
        t (quarticSignedPoleSixthFixedRadius t) rho) :
    |W.literalCompleteJointSixthHarmonic rho|
      <=
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * W.signedProfileAbsMomentSix
      * 128
      / (720 * (t/16)^8) := by
  rw [W.literalCompleteJointSixthHarmonic_eq_physical ht rho]
  rw [abs_div, abs_mul, abs_mul]
  have hm :
      |((zetaZeroConfig).mult (rho : ℂ) : ℝ)|
        = ((zetaZeroConfig).mult (rho : ℂ) : ℝ) := by
    rw [abs_of_nonneg]
    positivity
  rw [hm]
  have hM6 := W.signedProfileMomentSix_abs_le
  have hphase :=
    W.literalPhysicalSixthPhase_abs_le_128_of_fixedLocal
      ht rho hl
  have hden :
      0 < |720 * (t/16)^8| := by
    rw [abs_of_pos]
    · positivity
    · positivity
  apply div_le_div_of_nonneg_right _ hden.le
  have hm0 :
      0 <= ((zetaZeroConfig).mult (rho : ℂ) : ℝ) := by
    positivity
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul hM6 hphase
      (abs_nonneg _)
      W.signedProfileAbsMomentSix_nonneg)
    hm0

theorem QuarticFourSignedPolePair.literalFixedStripSixthDebtAt_le_multiplicity
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalFixedStripSixthDebtAt n
      <=
    (W.signedProfileAbsMomentSix * 128
        / (720 * (t/16)^8))
      *
    (W.literalLocalMultiplicityAt
      (quarticSignedPoleSixthFixedRadius t) n : ℝ) := by
  classical
  have hcoef :
      0 <= W.signedProfileAbsMomentSix * 128
        / (720 * (t/16)^8) := by
    positivity
  unfold QuarticFourSignedPolePair.literalFixedStripSixthDebtAt
    QuarticFourSignedPolePair.literalLocalMultiplicityAt
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hl :
      quarticSignedPoleLocal
        t (quarticSignedPoleSixthFixedRadius t) rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · simp [hl,hoff]
      have hterm :=
        W.literalCompleteJointSixthHarmonic_abs_le_fixed
          ht rho hl
      simpa [mul_assoc, mul_left_comm, mul_comm] using hterm
    · simp [hl,hoff]
      exact mul_nonneg hcoef (by positivity)
  · simp [hl]
    exact mul_nonneg hcoef (by positivity)

theorem QuarticFourSignedPolePair.literalFixedStripSixthDebtAt_le_fixedWindowN
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalFixedStripSixthDebtAt n
      <=
    (W.signedProfileAbsMomentSix * 128
        / (720 * (t/16)^8))
      *
    (zetaZeroConfig.N (t-3) (t+2) : ℝ) := by
  have hbase :=
    W.literalFixedStripSixthDebtAt_le_multiplicity ht n
  have heta :=
    quarticSignedPoleSixthFixedRadius_nonneg ht
  have hcountNat :=
    W.literalLocalMultiplicityAt_le_expandedWindowN
      ht heta
      (eta:=quarticSignedPoleSixthFixedRadius t) n
  rw [quarticSignedPoleSixthFixedHalfWidth ht] at hcountNat
  have hcount :
      (W.literalLocalMultiplicityAt
        (quarticSignedPoleSixthFixedRadius t) n : ℝ)
        <=
      (zetaZeroConfig.N (t-3) (t+2) : ℝ) := by
    exact_mod_cast hcountNat
  have hcoef :
      0 <= W.signedProfileAbsMomentSix * 128
        / (720 * (t/16)^8) := by
    positivity
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hcount hcoef)

theorem QuarticFourSignedPolePair.literalFixedStripSixthDebtAt_le_G1_fixedWindowN
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalFixedStripSixthDebtAt n
      <=
    (W.fourthLipschitz * 128
        / (720 * (t/16)^8))
      *
    (zetaZeroConfig.N (t-3) (t+2) : ℝ) := by
  have hbase :=
    W.literalFixedStripSixthDebtAt_le_fixedWindowN ht n
  have hM6 :=
    W.signedProfileAbsMomentSix_le_fourthLipschitz
  have hden : 0 < 720 * (t/16)^8 := by positivity
  have hcoef :
      W.signedProfileAbsMomentSix * 128
          / (720 * (t/16)^8)
        <=
      W.fourthLipschitz * 128
          / (720 * (t/16)^8) := by
    apply div_le_div_of_nonneg_right _ hden.le
    exact mul_le_mul_of_nonneg_right hM6 (by norm_num)
  have hN :
      0 <= (zetaZeroConfig.N (t-3) (t+2) : ℝ) := by
    positivity
  exact hbase.trans
    (mul_le_mul_of_nonneg_right hcoef hN)

theorem QuarticFourSignedPolePair.literalLocalSignedSixthHarmonicAt_le_G1_fixedWindowN
    {t eta : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hM6 : 0 <= W.signedProfileMomentSix)
    (n : ℕ) :
    W.literalLocalSignedSixthHarmonicAt eta n
      <=
    (W.fourthLipschitz * 128
        / (720 * (t/16)^8))
      *
    (zetaZeroConfig.N (t-3) (t+2) : ℝ) := by
  calc
    W.literalLocalSignedSixthHarmonicAt eta n
      <= W.literalLocalSignedSixthCentralAt eta n :=
        W.literalLocalSignedSixthHarmonicAt_le_central
          ht hM6 n
    _ <= W.literalFixedStripSixthDebtAt n :=
        W.literalLocalSignedSixthCentralAt_le_fixedStripDebt
          ht n
    _ <=
      (W.fourthLipschitz * 128
          / (720 * (t/16)^8))
        *
      (zetaZeroConfig.N (t-3) (t+2) : ℝ) :=
        W.literalFixedStripSixthDebtAt_le_G1_fixedWindowN
          ht n

def QuarticFourSignedPolePair.postSixthFixedStripG1BudgetAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (EV : ℝ) (n : ℕ) : ℝ :=
  let eta := quarticSignedPoleCanonicalLocalRadius
  let r := quarticSignedPoleLocalHalfWidth t eta
  let NZ : ℝ :=
    (zetaZeroConfig.N (t-r-1) (t+r) : ℝ)
  let N6 : ℝ :=
    (zetaZeroConfig.N (t-3) (t+2) : ℝ)
  (W.targetStrength / (6 * (t/16)^6))
    *
  (
    EV
      + (3/2 : ℝ) * r^2 * NZ
      - (2/5 : ℝ) * r^5
          * quarticSignedPoleMuLowerEnvelope (t-r)
  )
    +
  (W.fourthLipschitz * 128
      / (720 * (t/16)^8)) * N6
    +
  (((Real.pi+1)^2 * W.fourthLipschitz)
      * quarticSignedPoleLocalEighthPhysicalEnvelope t eta
      / (t/16)^10) * NZ
    +
  W.literalFarExactAt eta n

theorem QuarticFourSignedPolePair.postSixthV4H4G1BudgetAt_le_fixedStripG1_of_M6_nonneg
    {t EV : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hM6 : 0 <= W.signedProfileMomentSix)
    (n : ℕ) :
    W.postSixthV4H4G1BudgetAt EV n
      <= W.postSixthFixedStripG1BudgetAt EV n := by
  have hsix :=
    W.literalLocalSignedSixthHarmonicAt_le_G1_fixedWindowN
      ht hM6
      (eta:=quarticSignedPoleCanonicalLocalRadius) n
  unfold QuarticFourSignedPolePair.postSixthV4H4G1BudgetAt
    QuarticFourSignedPolePair.postSixthFixedStripG1BudgetAt
  dsimp
  linarith

theorem QuarticFourSignedPolePair.literalOffOrdExactAt_le_postSixthFixedStripG1BudgetAt
    {t EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hM6 : 0 <= W.signedProfileMomentSix)
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
      <= W.postSixthFixedStripG1BudgetAt EV n := by
  have h0 :=
    W.literalOffOrdExactAt_le_postSixthV4H4AbsorbBudgetAt
      ht n hn hV
  have h1 :=
    W.postSixthV4H4AbsorbBudgetAt_le_G1
      (by linarith : 0 < t) n
  have h2 :=
    W.postSixthV4H4G1BudgetAt_le_fixedStripG1_of_M6_nonneg
      (by linarith : 0 < t) hM6 n
  exact h0.trans (h1.trans h2)



/-!
## Selected-witness sixth-moment determinant

The remaining sign hypothesis is not left as an opaque integral.  Because the
signed combined profile is the exact pole-residual-weighted linear combination
of the two endpoint projective profiles, its sixth moment is the corresponding
two-endpoint determinant.

This is the preferred witness-analysis surface:

  M6_signed(W)
    = poleTwo(W) * M6_half(W)
      - poleHalf(W) * M6_two(W).

The pole residuals already have positive high-t certificates elsewhere.  Thus
the unresolved sign has been reduced to a quantitative comparison of the two
literal endpoint sixth moments; no new representation layer is introduced.
-/

def quarticFourNormalizedProjectiveProfileSixthMoment
    (R lam mu : ℝ) : ℝ :=
  ∫ u : ℝ,
    quarticFourNormalizedProjectiveProfile R lam mu u * u^6

def QuarticFourSignedPolePair.endpointHalfSixthMoment
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  quarticFourNormalizedProjectiveProfileSixthMoment
    W.R (1/2) W.muHalf

def QuarticFourSignedPolePair.endpointTwoSixthMoment
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  quarticFourNormalizedProjectiveProfileSixthMoment
    W.R (2/3) W.muTwo

theorem QuarticFourSignedPolePair.signedProfileMomentSix_eq_endpoint_determinant
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.signedProfileMomentSix
      =
    W.poleTwo * W.endpointHalfSixthMoment
      - W.poleHalf * W.endpointTwoSixthMoment := by
  have hHalfC :=
    quarticFourNormalizedProjectiveProfile_continuous
      (R:=W.R) (lam:=(1/2 : ℝ)) (mu:=W.muHalf) W.Rpos
  have hHalfK :=
    quarticFourNormalizedProjectiveProfile_compact
      (R:=W.R) (lam:=(1/2 : ℝ)) (mu:=W.muHalf) W.Rpos
  have hTwoC :=
    quarticFourNormalizedProjectiveProfile_continuous
      (R:=W.R) (lam:=(2/3 : ℝ)) (mu:=W.muTwo) W.Rpos
  have hTwoK :=
    quarticFourNormalizedProjectiveProfile_compact
      (R:=W.R) (lam:=(2/3 : ℝ)) (mu:=W.muTwo) W.Rpos
  unfold QuarticFourSignedPolePair.signedProfileMomentSix
    QuarticFourSignedPolePair.endpointHalfSixthMoment
    QuarticFourSignedPolePair.endpointTwoSixthMoment
    quarticFourNormalizedProjectiveProfileSixthMoment
    quarticFourSignedPoleCombinedProfile
  rw [profileMoment_linearCombination
      hHalfC hHalfK hTwoC hTwoK
      W.poleTwo (-W.poleHalf) 6]
  ring

def QuarticFourSignedPolePair.endpointSixthDeterminant
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  W.poleTwo * W.endpointHalfSixthMoment
    - W.poleHalf * W.endpointTwoSixthMoment

theorem QuarticFourSignedPolePair.signedProfileMomentSix_eq_endpointSixthDeterminant
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.signedProfileMomentSix = W.endpointSixthDeterminant := by
  rw [W.signedProfileMomentSix_eq_endpoint_determinant]
  rfl

theorem QuarticFourSignedPolePair.signedProfileMomentSix_nonneg_iff_endpoint
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.signedProfileMomentSix
      ↔
    W.poleHalf * W.endpointTwoSixthMoment
      <= W.poleTwo * W.endpointHalfSixthMoment := by
  rw [W.signedProfileMomentSix_eq_endpoint_determinant]
  linarith



/-!
## Generic projective moment bridge and J6 reduction

The physical projective profile is 4*g*B_r, so every polynomial moment is four
times the corresponding bracket moment.  For the four-window family at r=1,
that bracket moment is exactly quarticFourWindowJ at the same order.

This general k bridge makes the selected signed sixth determinant completely
explicit in the existing four-window coordinates.
-/

def projectiveMomentEvenResp
    (g : ℝ -> ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  ∫ u : ℝ, g u * u^k * Real.cos (s*u)

def projectiveBracketMoment
    (g : ℝ -> ℝ) (r : ℝ) (k : ℕ) : ℝ :=
  ∫ u : ℝ, g u * u^k * twoRadiusBracket g r u

theorem projectiveBracketMoment_eq_response_det
    {g : ℝ -> ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (r : ℝ) (k : ℕ) :
    projectiveBracketMoment g r k
      =
    evenResp g 0 r * projectiveMomentEvenResp g k (2*r)
      - evenResp g 0 (2*r) * projectiveMomentEvenResp g k r := by
  let f2 : ℝ -> ℝ := fun u =>
    g u * u^k * Real.cos ((2*r)*u)
  let f1 : ℝ -> ℝ := fun u =>
    g u * u^k * Real.cos (r*u)
  have hf2 : Integrable f2 := by
    dsimp [f2]
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      ((hgc.mul_right).mul_right)
  have hf1 : Integrable f1 := by
    dsimp [f1]
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      ((hgc.mul_right).mul_right)
  unfold projectiveBracketMoment twoRadiusBracket
  have hpoint :
      (fun u : ℝ =>
        g u * u^k *
          (evenResp g 0 r * Real.cos (2*r*u)
            - evenResp g 0 (2*r) * Real.cos (r*u)))
        =
      (fun u : ℝ =>
        evenResp g 0 r * f2 u
          - evenResp g 0 (2*r) * f1 u) := by
    funext u
    dsimp [f1,f2]
    ring
  rw [hpoint,
      integral_sub (hf2.const_mul _) (hf1.const_mul _),
      integral_const_mul, integral_const_mul]
  unfold projectiveMomentEvenResp
  rfl

theorem genericProjectivePhysicalProfile_moment
    {g : ℝ -> ℝ}
    (r : ℝ) (k : ℕ) :
    (∫ u : ℝ,
      genericProjectivePhysicalProfile g r u * u^k)
      =
    4 * projectiveBracketMoment g r k := by
  unfold genericProjectivePhysicalProfile projectiveBracketMoment
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by ring

theorem projectiveBracketMoment_fourWindow_one
    {R lam mu : ℝ}
    (hR : 0 < R)
    (k : ℕ) :
    projectiveBracketMoment
      (quarticFourWindowProfile R lam mu) 1 k
      =
    quarticFourWindowJ R lam mu k := by
  rw [projectiveBracketMoment_eq_response_det
      (quarticFourWindowProfile_continuous hR)
      (quarticFourWindowProfile_compact hR) 1 k,
    evenResp_zero_fourWindow hR,
    evenResp_zero_fourWindow hR]
  unfold projectiveMomentEvenResp
    quarticFourWindowJ quarticFourWindowMomentResp
  rw [quarticFourWindowProfile_pairing_eq hR (by fun_prop),
      quarticFourWindowProfile_pairing_eq hR (by fun_prop)]
  norm_num

theorem quarticFourNormalizedProjectiveProfile_moment
    {R lam mu : ℝ}
    (hR : 0 < R)
    (k : ℕ) :
    (∫ u : ℝ,
      quarticFourNormalizedProjectiveProfile R lam mu u * u^k)
      =
    4 * quarticFourWindowJ R lam mu k := by
  unfold quarticFourNormalizedProjectiveProfile
  rw [genericProjectivePhysicalProfile_moment,
      projectiveBracketMoment_fourWindow_one hR]

theorem quarticFourNormalizedProjectiveProfileSixthMoment_eq_J6
    {R lam mu : ℝ}
    (hR : 0 < R) :
    quarticFourNormalizedProjectiveProfileSixthMoment R lam mu
      =
    4 * quarticFourWindowJ R lam mu 6 := by
  unfold quarticFourNormalizedProjectiveProfileSixthMoment
  exact quarticFourNormalizedProjectiveProfile_moment hR 6

theorem QuarticFourSignedPolePair.endpointHalfSixthMoment_eq_J6
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.endpointHalfSixthMoment
      =
    4 * quarticFourWindowJ W.R (1/2) W.muHalf 6 := by
  unfold QuarticFourSignedPolePair.endpointHalfSixthMoment
  exact quarticFourNormalizedProjectiveProfileSixthMoment_eq_J6
    W.Rpos

theorem QuarticFourSignedPolePair.endpointTwoSixthMoment_eq_J6
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.endpointTwoSixthMoment
      =
    4 * quarticFourWindowJ W.R (2/3) W.muTwo 6 := by
  unfold QuarticFourSignedPolePair.endpointTwoSixthMoment
  exact quarticFourNormalizedProjectiveProfileSixthMoment_eq_J6
    W.Rpos

theorem QuarticFourSignedPolePair.signedProfileMomentSix_eq_J6_determinant
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.signedProfileMomentSix
      =
    4 *
      (W.poleTwo * quarticFourWindowJ W.R (1/2) W.muHalf 6
        - W.poleHalf * quarticFourWindowJ W.R (2/3) W.muTwo 6) := by
  rw [W.signedProfileMomentSix_eq_endpoint_determinant,
      W.endpointHalfSixthMoment_eq_J6,
      W.endpointTwoSixthMoment_eq_J6]
  ring

theorem QuarticFourSignedPolePair.signedProfileMomentSix_nonneg_iff_J6
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.signedProfileMomentSix
      ↔
    W.poleHalf * quarticFourWindowJ W.R (2/3) W.muTwo 6
      <=
    W.poleTwo * quarticFourWindowJ W.R (1/2) W.muHalf 6 := by
  rw [W.signedProfileMomentSix_eq_J6_determinant]
  constructor <;> intro h <;> nlinarith



/-!
## Atomic J6 sign diagnostic

The exact atomic sixth moment is already determined by the same four support
points used for J2/J4.  Along the atomic J2-null curve its endpoint signs are
opposite:

  J6(1/2) < 0,
  J6(2/3) > 0.

Since the smooth endpoint pole residuals are positive in the high-t corridor,
this diagnostic shows that the preferred witness should not be expected to
satisfy M6_signed >= 0.  The positive-sign fixed-strip compiler above remains a
valid conditional theorem, but it is not promoted as the selected-witness
route.
-/

theorem quarticFourAtomicJAt_six_formula
    (lam mu : ℝ) :
    quarticFourAtomicJAt lam mu 6
      =
    -(Real.pi^6 *
      (91854*lam*mu + 793*lam - 186624*mu - 128) / 93312) := by
  unfold quarticFourAtomicJAt quarticFourAtomicRespAt
    quarticFourAtomicMomentRespAt
  have hc1 : Real.cos (Real.pi/3) = 1/2 := by
    simpa using Real.cos_pi_div_three
  have hc2 : Real.cos (Real.pi/2) = 0 := by
    simpa using Real.cos_pi_div_two
  have hcp : Real.cos Real.pi = -1 := Real.cos_pi
  have h2c1 : Real.cos (2*(Real.pi/3)) = -1/2 := by
    have harg : 2*(Real.pi/3) = Real.pi - Real.pi/3 := by ring
    rw [harg, Real.cos_sub, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_three]
    norm_num
  have h2c2 : Real.cos (2*(Real.pi/2)) = -1 := by
    have harg : 2*(Real.pi/2) = Real.pi := by ring
    rw [harg, Real.cos_pi]
  have h2cp : Real.cos (2*Real.pi) = 1 := by
    have harg : 2*Real.pi = Real.pi + Real.pi := by ring
    rw [harg, Real.cos_add, Real.cos_pi, Real.sin_pi]
    norm_num
  simp only [one_mul, mul_zero, Real.cos_zero,
    zero_pow (by norm_num : 6 ≠ 0)]
  rw [hc1,hc2,hcp,h2c1,h2c2,h2cp]
  ring

theorem quarticFourAtomicJ6_on_null_formula
    {lam : ℝ} (hlam : lam <= 2/3) :
    quarticFourAtomicJAt lam (quarticFourAtomicMu lam) 6
      =
    5 * Real.pi^6 * (lam-2) * (1599*lam-1024)
      / (11664*(3*lam-8)) := by
  rw [quarticFourAtomicJAt_six_formula]
  unfold quarticFourAtomicMu
  have hden : 144 - 54*lam ≠ 0 :=
    ne_of_gt (quarticFourAtomicMu_den_pos hlam)
  field_simp [hden]
  ring

theorem quarticFourAtomicMu_half :
    quarticFourAtomicMu (1/2) = -(1/78 : ℝ) := by
  unfold quarticFourAtomicMu
  norm_num

theorem quarticFourAtomicMu_twoThirds :
    quarticFourAtomicMu (2/3) = (1/162 : ℝ) := by
  unfold quarticFourAtomicMu
  norm_num

theorem quarticFourAtomicJ6_half_exact :
    quarticFourAtomicJAt
      (1/2) (quarticFourAtomicMu (1/2)) 6
      =
    -(2245/101088 : ℝ) * Real.pi^6 := by
  rw [quarticFourAtomicJ6_on_null_formula (by norm_num : (1/2 : ℝ) <= 2/3)]
  ring

theorem quarticFourAtomicJ6_twoThirds_exact :
    quarticFourAtomicJAt
      (2/3) (quarticFourAtomicMu (2/3)) 6
      =
    (35/8748 : ℝ) * Real.pi^6 := by
  rw [quarticFourAtomicJ6_on_null_formula (by norm_num : (2/3 : ℝ) <= 2/3)]
  ring

theorem quarticFourAtomicJ6_half_neg :
    quarticFourAtomicJAt
      (1/2) (quarticFourAtomicMu (1/2)) 6 < 0 := by
  rw [quarticFourAtomicJ6_half_exact]
  positivity

theorem quarticFourAtomicJ6_twoThirds_pos :
    0 <
    quarticFourAtomicJAt
      (2/3) (quarticFourAtomicMu (2/3)) 6 := by
  rw [quarticFourAtomicJ6_twoThirds_exact]
  positivity

theorem quarticMomentWeight_even_six (s u : ℝ) :
    quarticMomentWeight 6 s (-u)
      = quarticMomentWeight 6 s u := by
  unfold quarticMomentWeight
  rw [show (-u)^6 = u^6 by ring]
  rw [show s*(-u) = -(s*u) by ring, Real.cos_neg]

theorem exists_radius_quarticFourWindowJ6_close_atomic
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R lam mu : ℝ,
        0 < R -> R < delta ->
        lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) ->
        |mu| <= 1/10 ->
        |quarticFourWindowJ R lam mu 6
          - quarticFourAtomicJAt lam mu 6| <= eps :=
  exists_radius_quarticFourWindowJ_close_atomic
    (quarticMomentWeight_even_six 1)
    (quarticMomentWeight_even_six 2) heps



/-!
## Uniform J6 endpoint signs on the selected mu corridors

The atomic endpoint signs above have comfortable corridor margins.  These
margins are stated in pi^6 units so the smooth approximation radius can be
chosen without decimal estimates.
-/

theorem quarticFourAtomicJ6_half_le_neg_pi6_div_100
    {mu : ℝ}
    (hmu :
      |mu-quarticFourAtomicMu (1/2)|
        <= quarticFourAtomicMuRadius) :
    quarticFourAtomicJAt (1/2) mu 6
      <= -(Real.pi^6 / 100) := by
  rw [quarticFourAtomicJAt_six_formula]
  rw [quarticFourAtomicMu_half] at hmu
  unfold quarticFourAtomicMuRadius at hmu
  have hlo := (abs_le.mp hmu).1
  have hhi := (abs_le.mp hmu).2
  have hp6 : 0 < Real.pi^6 := by positivity
  norm_num at hlo hhi ⊢
  nlinarith

theorem quarticFourAtomicJ6_twoThirds_ge_pi6_div_500
    {mu : ℝ}
    (hmu :
      |mu-quarticFourAtomicMu (2/3)|
        <= quarticFourAtomicMuRadius) :
    Real.pi^6 / 500
      <= quarticFourAtomicJAt (2/3) mu 6 := by
  rw [quarticFourAtomicJAt_six_formula]
  rw [quarticFourAtomicMu_twoThirds] at hmu
  unfold quarticFourAtomicMuRadius at hmu
  have hlo := (abs_le.mp hmu).1
  have hhi := (abs_le.mp hmu).2
  have hp6 : 0 < Real.pi^6 := by positivity
  norm_num at hlo hhi ⊢
  nlinarith

theorem exists_radius_quarticFourWindow_endpointJ6_signs :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R muHalf muTwo : ℝ,
        0 < R -> R < delta ->
        |muHalf-quarticFourAtomicMu (1/2)|
          <= quarticFourAtomicMuRadius ->
        |muTwo-quarticFourAtomicMu (2/3)|
          <= quarticFourAtomicMuRadius ->
        quarticFourWindowJ R (1/2) muHalf 6 < 0
          ∧ 0 < quarticFourWindowJ R (2/3) muTwo 6 := by
  let eps : ℝ := Real.pi^6 / 1000
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  obtain ⟨d,hd,hclose⟩ :=
    exists_radius_quarticFourWindowJ6_close_atomic heps
  refine ⟨d,hd,?_⟩
  intro R muHalf muTwo hR hRd hmuHalf hmuTwo
  have hmuHalfAbs :
      |muHalf| < 1/10 :=
    quarticFourAtomicMu_corridor_abs_lt_tenth
      (by norm_num) (by norm_num) hmuHalf
  have hmuTwoAbs :
      |muTwo| < 1/10 :=
    quarticFourAtomicMu_corridor_abs_lt_tenth
      (by norm_num) (by norm_num) hmuTwo
  have hlamHalf : (1/2 : ℝ) ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) :=
    ⟨le_rfl, by norm_num⟩
  have hlamTwo : (2/3 : ℝ) ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) :=
    ⟨by norm_num, le_rfl⟩
  have eHalf :=
    hclose R (1/2) muHalf hR hRd hlamHalf hmuHalfAbs.le
  have eTwo :=
    hclose R (2/3) muTwo hR hRd hlamTwo hmuTwoAbs.le
  have hHalfAtom :=
    quarticFourAtomicJ6_half_le_neg_pi6_div_100 hmuHalf
  have hTwoAtom :=
    quarticFourAtomicJ6_twoThirds_ge_pi6_div_500 hmuTwo
  have eHalfHi := (abs_le.mp eHalf).2
  have eTwoLo := (abs_le.mp eTwo).1
  dsimp [eps] at eHalfHi eTwoLo
  have hp6 : 0 < Real.pi^6 := by positivity
  constructor <;> nlinarith

/--
For t >= 200 and sufficiently small R, both smooth endpoint pole residuals are
strictly positive throughout the selected mu corridors.
-/
theorem exists_radius_quarticFourSmooth_endpointPole_pos
    {t : ℝ} (ht : 200 <= t) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R muHalf muTwo : ℝ,
        0 < R -> R < delta ->
        |muHalf-quarticFourAtomicMu (1/2)|
          <= quarticFourAtomicMuRadius ->
        |muTwo-quarticFourAtomicMu (2/3)|
          <= quarticFourAtomicMuRadius ->
        0 < quarticFourSmoothFinitePoleResidual R (1/2) muHalf t
          ∧
        0 < quarticFourSmoothFinitePoleResidual R (2/3) muTwo t := by
  obtain ⟨d,hd,hclose⟩ :=
    exists_radius_quarticFourSmoothPole_close_atomic ht (1/4)
  refine ⟨d,hd,?_⟩
  intro R muHalf muTwo hR hRd hmuHalf hmuTwo
  have hmuHalfAbs :
      |muHalf| < 1/10 :=
    quarticFourAtomicMu_corridor_abs_lt_tenth
      (by norm_num) (by norm_num) hmuHalf
  have hmuTwoAbs :
      |muTwo| < 1/10 :=
    quarticFourAtomicMu_corridor_abs_lt_tenth
      (by norm_num) (by norm_num) hmuTwo
  have hlamHalf : (1/2 : ℝ) ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) :=
    ⟨le_rfl, by norm_num⟩
  have hlamTwo : (2/3 : ℝ) ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) :=
    ⟨by norm_num, le_rfl⟩
  have eHalf :=
    hclose R (1/2) muHalf hR hRd hlamHalf hmuHalfAbs.le
  have eTwo :=
    hclose R (2/3) muTwo hR hRd hlamTwo hmuTwoAbs.le
  have aHalf :=
    quarticFourAtomicFinitePoleResidual_ge_seventeen_twentieths_of_twoHundred
      ht hlamHalf hmuHalfAbs.le
  have aTwo :=
    quarticFourAtomicFinitePoleResidual_ge_seventeen_twentieths_of_twoHundred
      ht hlamTwo hmuTwoAbs.le
  have eHalfLo := (abs_le.mp eHalf).1
  have eTwoLo := (abs_le.mp eTwo).1
  constructor <;> norm_num at eHalfLo eTwoLo ⊢ <;> linarith

/--
Refined selected-witness existence: the same floor-certified witness can be
chosen with strictly negative signed sixth profile moment.

This is the source-native correction to the earlier exploratory
M6_signed >= 0 branch.
-/
theorem exists_quarticFourSignedPolePair_with_strength_floor_and_M6_neg
    {t : ℝ} (ht : 200 <= t) :
    ∃ W : QuarticFourSignedPolePair t,
      7 * Real.pi^4 / 1600 <= W.targetStrength
        ∧ W.signedProfileMomentSix < 0 := by
  obtain ⟨R0,hR0,hfamily⟩ :=
    exists_uniform_smooth_quarticFourWindow_family
  obtain ⟨dTarget,hdTarget,hTarget⟩ :=
    exists_radius_quarticFourSmooth_signedPoleTarget_ge_margin ht
  obtain ⟨dJ6,hdJ6,hJ6⟩ :=
    exists_radius_quarticFourWindow_endpointJ6_signs
  obtain ⟨dPole,hdPole,hPole⟩ :=
    exists_radius_quarticFourSmooth_endpointPole_pos ht

  let d := min dTarget (min dJ6 dPole)
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min hdTarget (lt_min hdJ6 hdPole)
  let R : ℝ := min 1 (min R0 d) / 2
  have hinner : 0 < min R0 d := lt_min hR0 hd
  have hmin : 0 < min 1 (min R0 d) :=
    lt_min (by norm_num) hinner
  have hR : 0 < R := by
    dsimp [R]
    linarith
  have hRone : R < 1 := by
    dsimp [R]
    have hle := min_le_left 1 (min R0 d)
    linarith
  have hRinner : R < min R0 d := by
    dsimp [R]
    have hle := min_le_right 1 (min R0 d)
    linarith
  have hRR0 : R < R0 :=
    hRinner.trans_le (min_le_left R0 d)
  have hRd : R < d :=
    hRinner.trans_le (min_le_right R0 d)
  have hRTarget : R < dTarget :=
    hRd.trans_le (min_le_left dTarget (min dJ6 dPole))
  have hRrest : R < min dJ6 dPole :=
    hRd.trans_le (min_le_right dTarget (min dJ6 dPole))
  have hRJ6 : R < dJ6 :=
    hRrest.trans_le (min_le_left dJ6 dPole)
  have hRPole : R < dPole :=
    hRrest.trans_le (min_le_right dJ6 dPole)

  have hlamHalf : (1/2 : ℝ) ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) :=
    ⟨le_rfl, by norm_num⟩
  have hlamTwo : (2/3 : ℝ) ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) :=
    ⟨by norm_num, le_rfl⟩

  obtain ⟨S1⟩ := hfamily R (1/2) hR hRR0 hlamHalf
  obtain ⟨S2⟩ := hfamily R (2/3) hR hRR0 hlamTwo

  have hfloor :
      7 * Real.pi^4 / 1600 <=
        quarticFourSmoothPoleCancelledTarget
          R S1.mu S2.mu t :=
    hTarget R S1.mu S2.mu hR hRTarget S1.muNear S2.muNear
  have htransPos :
      0 < quarticFourSmoothPoleCancelledTarget
        R S1.mu S2.mu t := by
    have hp4 : 0 < Real.pi^4 := by positivity
    nlinarith
  obtain ⟨eps,heps,hband⟩ :=
    exists_quarticFourSignedPoleCombinedHeightDefect_pos_punctured
      hR S1.J2zero S2.J2zero htransPos

  let W : QuarticFourSignedPolePair t := {
    R := R
    muHalf := S1.mu
    muTwo := S2.mu
    eps := eps
    Rpos := hR
    RltOne := hRone
    muHalfNear := S1.muNear
    muTwoNear := S2.muNear
    J2Half := S1.J2zero
    J2Two := S2.J2zero
    signedTargetStrength := htransPos
    epsPos := heps
    combinedTargetBand := hband
  }

  have hJ6sign :=
    hJ6 R S1.mu S2.mu hR hRJ6 S1.muNear S2.muNear
  have hPsign :=
    hPole R S1.mu S2.mu hR hRPole S1.muNear S2.muNear
  have hM6 : W.signedProfileMomentSix < 0 := by
    rw [W.signedProfileMomentSix_eq_J6_determinant]
    dsimp [W]
    have hpHalf :
        0 <
        quarticFourSmoothFinitePoleResidual R (1/2) S1.mu t :=
      hPsign.1
    have hpTwo :
        0 <
        quarticFourSmoothFinitePoleResidual R (2/3) S2.mu t :=
      hPsign.2
    have hJHalf :
        quarticFourWindowJ R (1/2) S1.mu 6 < 0 :=
      hJ6sign.1
    have hJTwo :
        0 < quarticFourWindowJ R (2/3) S2.mu 6 :=
      hJ6sign.2
    have hterm1 :
        quarticFourSmoothFinitePoleResidual R (2/3) S2.mu t
          * quarticFourWindowJ R (1/2) S1.mu 6 < 0 :=
      mul_neg_of_pos_of_neg hpTwo hJHalf
    have hterm2 :
        0 <
        quarticFourSmoothFinitePoleResidual R (1/2) S1.mu t
          * quarticFourWindowJ R (2/3) S2.mu 6 :=
      mul_pos hpHalf hJTwo
    nlinarith

  refine ⟨W, ?_, hM6⟩
  simpa [W, QuarticFourSignedPolePair.targetStrength] using hfloor


/-!
## Clay-facing selected M6 certificate

The manuscript min-cut does not need another generic moment theory.  What the
terminal scalar inequality needs is one quantitative sixth-moment certificate
for the same floor-certified selected witness.

The existing atomic pole estimates were intentionally very coarse.  On the
actual high range t>=200 the three hyperbolic arguments in the endpoint pole
formula are all <= 4/25 in absolute value.  The already-certified degree-six
cosh Taylor theorem therefore gives a much tighter endpoint-pole bound.

Together with the existing atomic/smooth J6 bridge this yields

  -(3/20) pi^6 <= M6_signed(W) < 0

for one strength-floor witness at every t>=200.

This is deliberately terminal-specific; no new generic J_k API is introduced.
-/

theorem quarticSignedPole_cosh_le_51_50_of_abs_le_four_twentyfive
    {x : ℝ}
    (hx : |x| <= (4/25 : ℝ)) :
    Real.cosh x <= 51/50 := by
  have hx1 : |x| <= 1 := by linarith
  have hr :=
    real_cosh_sub_sixth_abs_le_eighth (x:=x) hx1
  have hu := (abs_le.mp hr).2

  have h2a : |x|^2 <= (4/25 : ℝ)^2 := by gcongr
  have h4a : |x|^4 <= (4/25 : ℝ)^4 := by gcongr
  have h6a : |x|^6 <= (4/25 : ℝ)^6 := by gcongr
  have h8a : |x|^8 <= (4/25 : ℝ)^8 := by gcongr

  have h2 : x^2 <= (4/25 : ℝ)^2 := by
    simpa [sq_abs] using h2a
  have h4 : x^4 <= (4/25 : ℝ)^4 := by
    calc
      x^4 = |x^4| := (abs_of_nonneg (by positivity)).symm
      _ = |x|^4 := abs_pow x 4
      _ <= (4/25 : ℝ)^4 := h4a
  have h6 : x^6 <= (4/25 : ℝ)^6 := by
    calc
      x^6 = |x^6| := (abs_of_nonneg (by positivity)).symm
      _ = |x|^6 := abs_pow x 6
      _ <= (4/25 : ℝ)^6 := h6a
  have h8 : x^8 <= (4/25 : ℝ)^8 := by
    calc
      x^8 = |x^8| := (abs_of_nonneg (by positivity)).symm
      _ = |x|^8 := abs_pow x 8
      _ <= (4/25 : ℝ)^8 := h8a
  have habs8 : |x|^8 = x^8 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 <= x^8)]
  rw [habs8] at hu
  norm_num at h2 h4 h6 h8 ⊢
  nlinarith

theorem quarticSignedPole_atomic_arguments_abs_le_four_twentyfive
    {t : ℝ} (ht : 200 <= t) :
    |8*Real.pi/(3*t)| <= (4/25 : ℝ)
      ∧ |4*Real.pi/t| <= (4/25 : ℝ)
      ∧ |8*Real.pi/t| <= (4/25 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hp0 : 0 < Real.pi := Real.pi_pos
  have hp4 : Real.pi < 4 := Real.pi_lt_four
  have h1non : 0 <= 8*Real.pi/(3*t) := by positivity
  have h2non : 0 <= 4*Real.pi/t := by positivity
  have h3non : 0 <= 8*Real.pi/t := by positivity
  rw [abs_of_nonneg h1non, abs_of_nonneg h2non, abs_of_nonneg h3non]
  constructor
  · rw [div_le_iff₀ (by positivity : 0 < 3*t)]
    nlinarith
  constructor <;> rw [div_le_iff₀ ht0] <;> nlinarith

theorem quarticFourAtomicNullPole_half_le_57_50
    {t : ℝ} (ht : 200 <= t) :
    quarticFourAtomicFinitePoleResidual
      t (1/2) (quarticFourAtomicMu (1/2))
      <= 57/50 := by
  have ht0 : 0 < t := by linarith
  obtain ⟨hx1,hx2,hx3⟩ :=
    quarticSignedPole_atomic_arguments_abs_le_four_twentyfive ht
  have hc1 :=
    quarticSignedPole_cosh_le_51_50_of_abs_le_four_twentyfive hx1
  have hc2 :=
    quarticSignedPole_cosh_le_51_50_of_abs_le_four_twentyfive hx2
  have hc3 :=
    quarticSignedPole_cosh_le_51_50_of_abs_le_four_twentyfive hx3
  rw [quarticFourAtomicFinitePoleResidual_formula_general ht0.ne',
      quarticFourAtomicMu_half]
  norm_num at ⊢
  nlinarith

theorem quarticFourAtomicNullPole_two_le_51_50
    {t : ℝ} (ht : 200 <= t) :
    quarticFourAtomicFinitePoleResidual
      t (2/3) (quarticFourAtomicMu (2/3))
      <= 51/50 := by
  have ht0 : 0 < t := by linarith
  obtain ⟨hx1,hx2,hx3⟩ :=
    quarticSignedPole_atomic_arguments_abs_le_four_twentyfive ht
  have hc1 :=
    quarticSignedPole_cosh_le_51_50_of_abs_le_four_twentyfive hx1
  have hc2 :=
    quarticSignedPole_cosh_le_51_50_of_abs_le_four_twentyfive hx2
  have hc3lo : 1 <= Real.cosh (8*Real.pi/t) :=
    Real.one_le_cosh _
  rw [quarticFourAtomicFinitePoleResidual_formula_general ht0.ne',
      quarticFourAtomicMu_twoThirds]
  norm_num at ⊢
  nlinarith

theorem quarticFourAtomicEndpointPole_corridor_le_23_20
    {t lam mu : ℝ}
    (ht : 200 <= t)
    (hlam : lam = (1/2 : ℝ) ∨ lam = (2/3 : ℝ))
    (hmu :
      |mu-quarticFourAtomicMu lam|
        <= quarticFourAtomicMuRadius) :
    quarticFourAtomicFinitePoleResidual t lam mu <= 23/20 := by
  rcases hlam with rfl | rfl
  · have hc :=
      quarticFourAtomicFinitePoleResidual_corridor_close_null
        ht ⟨by norm_num, by norm_num⟩ hmu
    have hu := (abs_le.mp hc).2
    have h0 := quarticFourAtomicNullPole_half_le_57_50 ht
    linarith
  · have hc :=
      quarticFourAtomicFinitePoleResidual_corridor_close_null
        ht ⟨by norm_num, by norm_num⟩ hmu
    have hu := (abs_le.mp hc).2
    have h0 := quarticFourAtomicNullPole_two_le_51_50 ht
    linarith

theorem exists_radius_quarticFourSmooth_endpointPole_le_six_fifths
    {t : ℝ} (ht : 200 <= t) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R muHalf muTwo : ℝ,
        0 < R -> R < delta ->
        |muHalf-quarticFourAtomicMu (1/2)|
          <= quarticFourAtomicMuRadius ->
        |muTwo-quarticFourAtomicMu (2/3)|
          <= quarticFourAtomicMuRadius ->
        quarticFourSmoothFinitePoleResidual R (1/2) muHalf t <= 6/5
          ∧
        quarticFourSmoothFinitePoleResidual R (2/3) muTwo t <= 6/5 := by
  obtain ⟨d,hd,hclose⟩ :=
    exists_radius_quarticFourSmoothPole_close_atomic
      ht (by norm_num : (0:ℝ) < 1/100)
  refine ⟨d,hd,?_⟩
  intro R muHalf muTwo hR hRd hmuHalf hmuTwo
  have hmuHalfAbs :
      |muHalf| < 1/10 :=
    quarticFourAtomicMu_corridor_abs_lt_tenth
      (by norm_num) (by norm_num) hmuHalf
  have hmuTwoAbs :
      |muTwo| < 1/10 :=
    quarticFourAtomicMu_corridor_abs_lt_tenth
      (by norm_num) (by norm_num) hmuTwo
  have hlamHalf : (1/2 : ℝ) ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) :=
    ⟨le_rfl, by norm_num⟩
  have hlamTwo : (2/3 : ℝ) ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) :=
    ⟨by norm_num, le_rfl⟩
  have eHalf :=
    hclose R (1/2) muHalf hR hRd hlamHalf hmuHalfAbs.le
  have eTwo :=
    hclose R (2/3) muTwo hR hRd hlamTwo hmuTwoAbs.le
  have aHalf :=
    quarticFourAtomicEndpointPole_corridor_le_23_20
      ht (Or.inl rfl) hmuHalf
  have aTwo :=
    quarticFourAtomicEndpointPole_corridor_le_23_20
      ht (Or.inr rfl) hmuTwo
  have eHalfHi := (abs_le.mp eHalf).2
  have eTwoHi := (abs_le.mp eTwo).2
  constructor <;> nlinarith

theorem quarticFourAtomicJ6_half_abs_le_three_125
    {mu : ℝ}
    (hmu :
      |mu-quarticFourAtomicMu (1/2)|
        <= quarticFourAtomicMuRadius) :
    |quarticFourAtomicJAt (1/2) mu 6|
      <= (3/125 : ℝ) * Real.pi^6 := by
  rw [quarticFourAtomicJAt_six_formula]
  rw [quarticFourAtomicMu_half] at hmu
  unfold quarticFourAtomicMuRadius at hmu
  have hlo := (abs_le.mp hmu).1
  have hhi := (abs_le.mp hmu).2
  have hp6 : 0 < Real.pi^6 := by positivity
  rw [abs_le]
  norm_num at hlo hhi ⊢
  constructor <;> nlinarith

theorem quarticFourAtomicJ6_twoThirds_abs_le_one_200
    {mu : ℝ}
    (hmu :
      |mu-quarticFourAtomicMu (2/3)|
        <= quarticFourAtomicMuRadius) :
    |quarticFourAtomicJAt (2/3) mu 6|
      <= (1/200 : ℝ) * Real.pi^6 := by
  rw [quarticFourAtomicJAt_six_formula]
  rw [quarticFourAtomicMu_twoThirds] at hmu
  unfold quarticFourAtomicMuRadius at hmu
  have hlo := (abs_le.mp hmu).1
  have hhi := (abs_le.mp hmu).2
  have hp6 : 0 < Real.pi^6 := by positivity
  rw [abs_le]
  norm_num at hlo hhi ⊢
  constructor <;> nlinarith

theorem exists_radius_quarticFourWindow_endpointJ6_terminal_abs_bounds :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R muHalf muTwo : ℝ,
        0 < R -> R < delta ->
        |muHalf-quarticFourAtomicMu (1/2)|
          <= quarticFourAtomicMuRadius ->
        |muTwo-quarticFourAtomicMu (2/3)|
          <= quarticFourAtomicMuRadius ->
        |quarticFourWindowJ R (1/2) muHalf 6|
            <= Real.pi^6 / 40
          ∧
        |quarticFourWindowJ R (2/3) muTwo 6|
            <= 3 * Real.pi^6 / 500 := by
  let eps : ℝ := Real.pi^6 / 1000
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  obtain ⟨d,hd,hclose⟩ :=
    exists_radius_quarticFourWindowJ6_close_atomic heps
  refine ⟨d,hd,?_⟩
  intro R muHalf muTwo hR hRd hmuHalf hmuTwo
  have hmuHalfAbs :
      |muHalf| < 1/10 :=
    quarticFourAtomicMu_corridor_abs_lt_tenth
      (by norm_num) (by norm_num) hmuHalf
  have hmuTwoAbs :
      |muTwo| < 1/10 :=
    quarticFourAtomicMu_corridor_abs_lt_tenth
      (by norm_num) (by norm_num) hmuTwo
  have hlamHalf : (1/2 : ℝ) ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) :=
    ⟨le_rfl, by norm_num⟩
  have hlamTwo : (2/3 : ℝ) ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) :=
    ⟨by norm_num, le_rfl⟩
  have eHalf :=
    hclose R (1/2) muHalf hR hRd hlamHalf hmuHalfAbs.le
  have eTwo :=
    hclose R (2/3) muTwo hR hRd hlamTwo hmuTwoAbs.le
  have aHalf :=
    quarticFourAtomicJ6_half_abs_le_three_125 hmuHalf
  have aTwo :=
    quarticFourAtomicJ6_twoThirds_abs_le_one_200 hmuTwo
  have triHalf :
      |quarticFourWindowJ R (1/2) muHalf 6|
        <=
      |quarticFourAtomicJAt (1/2) muHalf 6|
        + |quarticFourWindowJ R (1/2) muHalf 6
            - quarticFourAtomicJAt (1/2) muHalf 6| := by
    have h :=
      abs_add
        (quarticFourAtomicJAt (1/2) muHalf 6)
        (quarticFourWindowJ R (1/2) muHalf 6
          - quarticFourAtomicJAt (1/2) muHalf 6)
    simpa [add_sub_cancel_left] using h
  have triTwo :
      |quarticFourWindowJ R (2/3) muTwo 6|
        <=
      |quarticFourAtomicJAt (2/3) muTwo 6|
        + |quarticFourWindowJ R (2/3) muTwo 6
            - quarticFourAtomicJAt (2/3) muTwo 6| := by
    have h :=
      abs_add
        (quarticFourAtomicJAt (2/3) muTwo 6)
        (quarticFourWindowJ R (2/3) muTwo 6
          - quarticFourAtomicJAt (2/3) muTwo 6)
    simpa [add_sub_cancel_left] using h
  constructor
  · have he := eHalf
    dsimp [eps] at he
    nlinarith
  · have he := eTwo
    dsimp [eps] at he
    nlinarith

/--
Clay-facing selected-witness certificate.

This is the quantitative strengthening actually consumed by the terminal
post-sixth source.  The bound 3*pi^6/20 is chosen because it beats the
dominant sixth-vs-quartic balance at the canonical local radius.
-/
theorem exists_quarticFourSignedPolePair_with_strength_floor_and_terminal_M6
    {t : ℝ} (ht : 200 <= t) :
    ∃ W : QuarticFourSignedPolePair t,
      7 * Real.pi^4 / 1600 <= W.targetStrength
        ∧
      -(3/20 : ℝ) * Real.pi^6 <= W.signedProfileMomentSix
        ∧
      W.signedProfileMomentSix < 0 := by
  obtain ⟨R0,hR0,hfamily⟩ :=
    exists_uniform_smooth_quarticFourWindow_family
  obtain ⟨dTarget,hdTarget,hTarget⟩ :=
    exists_radius_quarticFourSmooth_signedPoleTarget_ge_margin ht
  obtain ⟨dJSign,hdJSign,hJSign⟩ :=
    exists_radius_quarticFourWindow_endpointJ6_signs
  obtain ⟨dJAbs,hdJAbs,hJAbs⟩ :=
    exists_radius_quarticFourWindow_endpointJ6_terminal_abs_bounds
  obtain ⟨dPPos,hdPPos,hPPos⟩ :=
    exists_radius_quarticFourSmooth_endpointPole_pos ht
  obtain ⟨dPUp,hdPUp,hPUp⟩ :=
    exists_radius_quarticFourSmooth_endpointPole_le_six_fifths ht

  let d :=
    min dTarget (min dJSign (min dJAbs (min dPPos dPUp)))
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min hdTarget
      (lt_min hdJSign
        (lt_min hdJAbs (lt_min hdPPos hdPUp)))
  let R : ℝ := min 1 (min R0 d) / 2
  have hinner : 0 < min R0 d := lt_min hR0 hd
  have hmin : 0 < min 1 (min R0 d) :=
    lt_min (by norm_num) hinner
  have hR : 0 < R := by
    dsimp [R]
    linarith
  have hRone : R < 1 := by
    dsimp [R]
    have hle := min_le_left 1 (min R0 d)
    linarith
  have hRinner : R < min R0 d := by
    dsimp [R]
    have hle := min_le_right 1 (min R0 d)
    linarith
  have hRR0 : R < R0 :=
    hRinner.trans_le (min_le_left R0 d)
  have hRd : R < d :=
    hRinner.trans_le (min_le_right R0 d)

  have hRTarget : R < dTarget :=
    hRd.trans_le (min_le_left dTarget _)
  have hRest1 :
      R < min dJSign (min dJAbs (min dPPos dPUp)) :=
    hRd.trans_le (min_le_right dTarget _)
  have hRJSign : R < dJSign :=
    hRest1.trans_le (min_le_left dJSign _)
  have hRest2 : R < min dJAbs (min dPPos dPUp) :=
    hRest1.trans_le (min_le_right dJSign _)
  have hRJAbs : R < dJAbs :=
    hRest2.trans_le (min_le_left dJAbs _)
  have hRest3 : R < min dPPos dPUp :=
    hRest2.trans_le (min_le_right dJAbs _)
  have hRPPos : R < dPPos :=
    hRest3.trans_le (min_le_left dPPos dPUp)
  have hRPUp : R < dPUp :=
    hRest3.trans_le (min_le_right dPPos dPUp)

  have hlamHalf : (1/2 : ℝ) ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) :=
    ⟨le_rfl, by norm_num⟩
  have hlamTwo : (2/3 : ℝ) ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) :=
    ⟨by norm_num, le_rfl⟩
  obtain ⟨S1⟩ := hfamily R (1/2) hR hRR0 hlamHalf
  obtain ⟨S2⟩ := hfamily R (2/3) hR hRR0 hlamTwo

  have hfloor :
      7 * Real.pi^4 / 1600 <=
        quarticFourSmoothPoleCancelledTarget
          R S1.mu S2.mu t :=
    hTarget R S1.mu S2.mu hR hRTarget S1.muNear S2.muNear
  have htransPos :
      0 < quarticFourSmoothPoleCancelledTarget
        R S1.mu S2.mu t := by
    have hp4 : 0 < Real.pi^4 := by positivity
    nlinarith
  obtain ⟨eps,heps,hband⟩ :=
    exists_quarticFourSignedPoleCombinedHeightDefect_pos_punctured
      hR S1.J2zero S2.J2zero htransPos

  let W : QuarticFourSignedPolePair t := {
    R := R
    muHalf := S1.mu
    muTwo := S2.mu
    eps := eps
    Rpos := hR
    RltOne := hRone
    muHalfNear := S1.muNear
    muTwoNear := S2.muNear
    J2Half := S1.J2zero
    J2Two := S2.J2zero
    signedTargetStrength := htransPos
    epsPos := heps
    combinedTargetBand := hband
  }

  have hJsign :=
    hJSign R S1.mu S2.mu hR hRJSign S1.muNear S2.muNear
  have hJabs :=
    hJAbs R S1.mu S2.mu hR hRJAbs S1.muNear S2.muNear
  have hPpos :=
    hPPos R S1.mu S2.mu hR hRPPos S1.muNear S2.muNear
  have hPup :=
    hPUp R S1.mu S2.mu hR hRPUp S1.muNear S2.muNear

  have hM6neg : W.signedProfileMomentSix < 0 := by
    rw [W.signedProfileMomentSix_eq_J6_determinant]
    dsimp [W]
    have hterm1 :
        quarticFourSmoothFinitePoleResidual R (2/3) S2.mu t
          * quarticFourWindowJ R (1/2) S1.mu 6 < 0 :=
      mul_neg_of_pos_of_neg hPpos.2 hJsign.1
    have hterm2 :
        0 <
        quarticFourSmoothFinitePoleResidual R (1/2) S1.mu t
          * quarticFourWindowJ R (2/3) S2.mu 6 :=
      mul_pos hPpos.1 hJsign.2
    nlinarith

  have hJHalfMag :
      - quarticFourWindowJ R (1/2) S1.mu 6
        <= Real.pi^6 / 40 := by
    have hab := hJabs.1
    have hneg := hJsign.1
    rw [abs_of_neg hneg] at hab
    exact hab
  have hJTwoMag :
      quarticFourWindowJ R (2/3) S2.mu 6
        <= 3 * Real.pi^6 / 500 := by
    have hab := hJabs.2
    have hpos := hJsign.2
    rw [abs_of_pos hpos] at hab
    exact hab

  have htermHalf :
      quarticFourSmoothFinitePoleResidual R (2/3) S2.mu t
          * (-quarticFourWindowJ R (1/2) S1.mu 6)
        <=
      (6/5 : ℝ) * (Real.pi^6 / 40) := by
    exact mul_le_mul hPup.2 hJHalfMag
      (by linarith [hJsign.1])
      (by norm_num)
  have htermTwo :
      quarticFourSmoothFinitePoleResidual R (1/2) S1.mu t
          * quarticFourWindowJ R (2/3) S2.mu 6
        <=
      (6/5 : ℝ) * (3 * Real.pi^6 / 500) := by
    exact mul_le_mul hPup.1 hJTwoMag
      hJsign.2.le
      (by norm_num)

  have hM6lo :
      -(3/20 : ℝ) * Real.pi^6 <= W.signedProfileMomentSix := by
    rw [W.signedProfileMomentSix_eq_J6_determinant]
    dsimp [W]
    have hp6 : 0 <= Real.pi^6 := by positivity
    nlinarith

  refine ⟨W, ?_, hM6lo, hM6neg⟩
  simpa [W, QuarticFourSignedPolePair.targetStrength] using hfloor

/--
The selected terminal M6 certificate is genuinely below the old dominant
sixth-vs-quartic balance at the canonical local radius.
-/
theorem quarticSignedPole_terminal_M6_cap_pays_dominant_balance :
    (1/24 : ℝ)
        * ((3/20 : ℝ) * Real.pi^6)
        * quarticSignedPoleCanonicalLocalRadius^2
      <
    quarticSignedPoleStrengthFloor := by
  unfold quarticSignedPoleCanonicalLocalRadius
    quarticSignedPoleStrengthFloor
  have hp0 : 0 < Real.pi := Real.pi_pos
  have hp4 : Real.pi < 4 := Real.pi_lt_four
  have hden : 0 < Real.pi + 1 := by positivity
  rw [div_pow]
  rw [div_lt_iff₀ (sq_pos_of_pos hden)]
  have hp4pos : 0 < Real.pi^4 := by positivity
  have hcore :
      3 * Real.pi^2 < 14 * Real.pi + 7 := by
    have hs : Real.pi^2 < 4 * Real.pi := by
      nlinarith
    nlinarith
  nlinarith [hp4pos, hcore]


/-!
## Direct terminal payment of the selected signed-sixth carrier

Do not build another phase-sector taxonomy unless this fails.  The
terminal-strength selected-witness cap is already small enough to try the
literal scalar inequality directly.

On a local physical window |a|<=1/2 and |d|<=r,

  |a^6 - 15 a^4 d^2 + 15 a^2 d^4 - d^6|
    <= 2^-6 + 15*2^-4*r^2 + 15*2^-2*r^4 + r^6.

This is charged against the same expanded literal zero count.  It is a
deliberately coarse *terminal* use of the now-small signed M6; no new witness
constant is introduced.
-/

def quarticSignedPoleLocalSixthPhaseEnvelope
    (t eta : ℝ) : ℝ :=
  let r := quarticSignedPoleLocalHalfWidth t eta
  (1/2 : ℝ)^6
    + 15 * (1/2 : ℝ)^4 * r^2
    + 15 * (1/2 : ℝ)^2 * r^4
    + r^6

theorem quarticSignedPoleLocalSixthPhaseEnvelope_nonneg
    {t eta : ℝ}
    (ht : 0 <= t)
    (heta : 0 <= eta) :
    0 <= quarticSignedPoleLocalSixthPhaseEnvelope t eta := by
  unfold quarticSignedPoleLocalSixthPhaseEnvelope
    quarticSignedPoleLocalHalfWidth
  positivity

theorem QuarticFourSignedPolePair.literalPhysicalSixthPhase_abs_le_localEnvelope
    {t eta : ℝ}
    (ht : 0 < t)
    (heta : 0 <= eta)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hl : quarticSignedPoleLocal t eta rho) :
    |W.literalPhysicalSixthPhase rho|
      <= quarticSignedPoleLocalSixthPhaseEnvelope t eta := by
  have hclosed :=
    (quarticSignedPoleLocal_iff_closed_ordinate_window
      ht heta rho).mp hl
  let r := quarticSignedPoleLocalHalfWidth t eta
  have hr0 : 0 <= r := by
    dsimp [r,quarticSignedPoleLocalHalfWidth]
    positivity
  have hdabs : |(rho : ℂ).im-t| <= r := by
    rw [abs_le]
    constructor <;> dsimp [r] at hclosed ⊢ <;> linarith
  have haabs := zetaZero_height_abs_le_half rho

  have ha2 : heightOf rho^2 <= (1/2 : ℝ)^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (heightOf rho)) haabs 2
    rw [← abs_pow, abs_of_nonneg (sq_nonneg (heightOf rho))] at h
    simpa using h
  have ha4 : heightOf rho^4 <= (1/2 : ℝ)^4 := by
    have h := pow_le_pow_left₀ (abs_nonneg (heightOf rho)) haabs 4
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 <= heightOf rho^4)] at h
    simpa using h
  have ha6 : heightOf rho^6 <= (1/2 : ℝ)^6 := by
    have h := pow_le_pow_left₀ (abs_nonneg (heightOf rho)) haabs 6
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 <= heightOf rho^6)] at h
    simpa using h

  have hd2 : ((rho : ℂ).im-t)^2 <= r^2 := by
    have h := pow_le_pow_left₀
      (abs_nonneg ((rho : ℂ).im-t)) hdabs 2
    rw [← abs_pow, abs_of_nonneg
      (sq_nonneg ((rho : ℂ).im-t))] at h
    simpa using h
  have hd4 : ((rho : ℂ).im-t)^4 <= r^4 := by
    have h := pow_le_pow_left₀
      (abs_nonneg ((rho : ℂ).im-t)) hdabs 4
    rw [← abs_pow, abs_of_nonneg
      (by positivity : 0 <= ((rho : ℂ).im-t)^4)] at h
    simpa using h
  have hd6 : ((rho : ℂ).im-t)^6 <= r^6 := by
    have h := pow_le_pow_left₀
      (abs_nonneg ((rho : ℂ).im-t)) hdabs 6
    rw [← abs_pow, abs_of_nonneg
      (by positivity : 0 <= ((rho : ℂ).im-t)^6)] at h
    simpa using h

  unfold QuarticFourSignedPolePair.literalPhysicalSixthPhase
    quarticSignedPoleLocalSixthPhaseEnvelope
  dsimp [r]
  rw [abs_le]
  constructor <;>
    nlinarith [
      sq_nonneg (heightOf rho),
      sq_nonneg ((rho : ℂ).im-t),
      mul_nonneg ha4 hd2,
      mul_nonneg ha2 hd4]

theorem QuarticFourSignedPolePair.literalLocalSignedSixthHarmonicAt_le_cap_mul_multiplicity
    {t eta C : ℝ}
    (ht : 0 < t)
    (heta : 0 <= eta)
    (hC : 0 <= C)
    (W : QuarticFourSignedPolePair t)
    (hM6 : |W.signedProfileMomentSix| <= C)
    (n : ℕ) :
    W.literalLocalSignedSixthHarmonicAt eta n
      <=
    (C * quarticSignedPoleLocalSixthPhaseEnvelope t eta
        / (720 * (t/16)^8))
      * (W.literalLocalMultiplicityAt eta n : ℝ) := by
  classical
  have henv :=
    quarticSignedPoleLocalSixthPhaseEnvelope_nonneg
      ht.le heta
  have hcoef :
      0 <=
      C * quarticSignedPoleLocalSixthPhaseEnvelope t eta
        / (720 * (t/16)^8) := by
    positivity
  unfold QuarticFourSignedPolePair.literalLocalSignedSixthHarmonicAt
    QuarticFourSignedPolePair.literalLocalMultiplicityAt
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hl : quarticSignedPoleLocal t eta rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · simp [hl,hoff]
      have hp :=
        W.literalPhysicalSixthPhase_abs_le_localEnvelope
          ht heta hl
      rw [W.literalCompleteJointSixthHarmonic_eq_physical ht rho]
      have hm :
          0 <= ((zetaZeroConfig).mult (rho : ℂ) : ℝ) := by
        positivity
      have hden :
          0 < 720 * (t/16)^8 := by positivity
      have habs :
          |((zetaZeroConfig).mult (rho : ℂ) : ℝ)
              * W.signedProfileMomentSix
              * W.literalPhysicalSixthPhase rho
              / (720 * (t/16)^8)|
            <=
          ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
              * C
              * quarticSignedPoleLocalSixthPhaseEnvelope t eta
              / (720 * (t/16)^8) := by
        rw [abs_div, abs_mul, abs_mul,
          abs_of_nonneg hm, abs_of_pos hden]
        apply div_le_div_of_nonneg_right _ hden.le
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hM6 hp
            (abs_nonneg _)
            hC)
          hm
      exact (le_abs_self _).trans
        (by
          simpa [mul_assoc, mul_left_comm, mul_comm] using habs)
    · simp [hl,hoff]
      exact mul_nonneg hcoef (by positivity)
  · simp [hl]
    exact mul_nonneg hcoef (by positivity)

theorem QuarticFourSignedPolePair.literalLocalSignedSixthHarmonicAt_le_cap_expandedWindowN
    {t eta C : ℝ}
    (ht : 0 < t)
    (heta : 0 <= eta)
    (hC : 0 <= C)
    (W : QuarticFourSignedPolePair t)
    (hM6 : |W.signedProfileMomentSix| <= C)
    (n : ℕ) :
    W.literalLocalSignedSixthHarmonicAt eta n
      <=
    (C * quarticSignedPoleLocalSixthPhaseEnvelope t eta
        / (720 * (t/16)^8))
      *
    (zetaZeroConfig.N
      (t - quarticSignedPoleLocalHalfWidth t eta - 1)
      (t + quarticSignedPoleLocalHalfWidth t eta) : ℝ) := by
  have hbase :=
    W.literalLocalSignedSixthHarmonicAt_le_cap_mul_multiplicity
      ht heta hC hM6 n
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
      C * quarticSignedPoleLocalSixthPhaseEnvelope t eta
        / (720 * (t/16)^8) := by
    have henv :=
      quarticSignedPoleLocalSixthPhaseEnvelope_nonneg ht.le heta
    positivity
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hmult hcoef)

def QuarticFourSignedPolePair.postSixthTerminalM6BudgetAt
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
  (((3/20 : ℝ) * Real.pi^6)
      * quarticSignedPoleLocalSixthPhaseEnvelope t eta
      / (720 * (t/16)^8))
    * NZ
    +
  (((Real.pi+1)^2 * W.fourthLipschitz)
      * quarticSignedPoleLocalEighthPhysicalEnvelope t eta
      / (t/16)^10)
    * NZ
    +
  W.literalFarExactAt eta n

theorem QuarticFourSignedPolePair.literalOffOrdExactAt_le_postSixthTerminalM6BudgetAt
    {t EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hM6lo :
      -(3/20 : ℝ) * Real.pi^6 <= W.signedProfileMomentSix)
    (hM6neg : W.signedProfileMomentSix < 0)
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
      <= W.postSixthTerminalM6BudgetAt EV n := by
  have ht0 : 0 < t := by linarith
  have hsource :=
    W.literalOffOrdExactAt_le_postSixthV4H4AbsorbBudgetAt
      ht n hn hV
  have hM6abs :
      |W.signedProfileMomentSix|
        <= (3/20 : ℝ) * Real.pi^6 := by
    rw [abs_of_neg hM6neg]
    nlinarith
  have hsix :=
    W.literalLocalSignedSixthHarmonicAt_le_cap_expandedWindowN
      ht0 quarticSignedPoleCanonicalLocalRadius_pos.le
      (by positivity : 0 <= (3/20 : ℝ) * Real.pi^6)
      hM6abs n
  have heighth :=
    W.literalLocalEighthDebtAt_le_G1_expandedWindowN
      ht0 quarticSignedPoleCanonicalLocalRadius_pos.le n
  unfold QuarticFourSignedPolePair.postSixthV4H4AbsorbBudgetAt at hsource
  unfold QuarticFourSignedPolePair.postSixthTerminalM6BudgetAt
  dsimp at hsource ⊢
  nlinarith

def QuarticFourSignedPolePair.postSixthTerminalDeterministicBudgetAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (CV CN : ℝ) (n : ℕ) : ℝ :=
  let eta := quarticSignedPoleCanonicalLocalRadius
  let r := quarticSignedPoleLocalHalfWidth t eta
  let EV := quarticSignedPoleCanonicalV4Error CV t
  let NZ := quarticSignedPoleCanonicalExpandedCountEnvelope CN t
  (W.targetStrength / (6 * (t/16)^6))
    *
  (
    EV
      + (3/2 : ℝ) * r^2 * NZ
      - (2/5 : ℝ) * r^5
          * quarticSignedPoleMuLowerEnvelope (t-r)
  )
    +
  (((3/20 : ℝ) * Real.pi^6)
      * quarticSignedPoleLocalSixthPhaseEnvelope t eta
      / (720 * (t/16)^8))
    * NZ
    +
  (((Real.pi+1)^2 * W.fourthLipschitz)
      * quarticSignedPoleLocalEighthPhysicalEnvelope t eta
      / (t/16)^10)
    * NZ
    +
  W.literalFarExactAt eta n



/-!
## Direct selected-M6 terminal scalar compiler

This is the Clay-facing compiler surface for the sharpened lane.  Once the
literal terminal budget is eventually strictly below the exact compensation
threshold, no further sixth-order, carrier, or representation theorem is
needed: the existing cofinal exact-source limit and completed-residual weld
compile directly to G3.

FarExact deliberately remains inside the scalar hypothesis with its sign.
-/

def QuarticFourSignedPolePair.PostSixthTerminalStrictAbsorb
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV : ℝ) : Prop :=
  ∃ eps : ℝ, 0 < eps ∧
    ∃ N : ℕ, ∀ n : ℕ, N <= n ->
      quarticSignedPoleLocalHalfWidth
          t quarticSignedPoleCanonicalLocalRadius
        < (n : ℝ)
      ∧
      W.postSixthTerminalM6BudgetAt EV n
        <= W.compensationTargetThreshold rho - eps

theorem QuarticFourSignedPolePair.globalOffOrd_le_target_sub_eps_of_postSixthTerminalStrictAbsorb
    {t EV eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hM6lo :
      -(3/20 : ℝ) * Real.pi^6 <= W.signedProfileMomentSix)
    (hM6neg : W.signedProfileMomentSix < 0)
    (heps : 0 < eps)
    (N : ℕ)
    (hN : ∀ n : ℕ, N <= n ->
      quarticSignedPoleLocalHalfWidth
          t quarticSignedPoleCanonicalLocalRadius
        < (n : ℝ)
      ∧
      W.postSixthTerminalM6BudgetAt EV n
        <= W.compensationTargetThreshold rho - eps)
    (hV :
      |quarticSignedPoleRvMVerticalFourthDiscrepancy
        t
        (quarticSignedPoleLocalHalfWidth
          t quarticSignedPoleCanonicalLocalRadius)|
        <= EV) :
    (∑' z : Zeros, W.literalOffOrdSource z)
      <= W.compensationTargetThreshold rho - eps := by
  have ht0 : 0 < t := by linarith
  have hfinite :
      ∀ᶠ n : ℕ in atTop,
        W.literalOffOrdExactAt n
          <= W.compensationTargetThreshold rho - eps := by
    rw [eventually_atTop]
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨hnRadius,hbudget⟩ := hN n hn
    have hsource :=
      W.literalOffOrdExactAt_le_postSixthTerminalM6BudgetAt
        ht hM6lo hM6neg n hnRadius hV
    exact hsource.trans hbudget
  have hlim :=
    W.literalOffOrdExactAt_tendsto_tsum ht0
  exact le_of_tendsto hlim hfinite

theorem QuarticFourSignedPolePair.completedSignedResidual_lt_target_of_postSixthTerminalStrictAbsorb
    {t EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hM6lo :
      -(3/20 : ℝ) * Real.pi^6 <= W.signedProfileMomentSix)
    (hM6neg : W.signedProfileMomentSix < 0)
    (hV :
      |quarticSignedPoleRvMVerticalFourthDiscrepancy
        t
        (quarticSignedPoleLocalHalfWidth
          t quarticSignedPoleCanonicalLocalRadius)|
        <= EV)
    (hC : W.PostSixthTerminalStrictAbsorb rho EV) :
    W.completedSignedResidual
      < 2 * W.combinedZeroHeightDefect rho := by
  rcases hC with ⟨eps,heps,N,hN⟩
  have hglobal :=
    W.globalOffOrd_le_target_sub_eps_of_postSixthTerminalStrictAbsorb
      ht rho hM6lo hM6neg heps N hN hV
  have hsum :
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        W.signedLiteralPairSourceTerm sigma)
        <= W.compensationTargetThreshold rho - eps := by
    rw [← W.literalOffOrdSource_tsum_eq_signedLiteralPairSource_tsum]
    exact hglobal
  rw [W.completedSignedResidual_eq_jointPairSource ht]
  unfold QuarticFourSignedPolePair.compensationTargetThreshold at hsum
  linarith



/-!
## Exact far base / horizontal split

The remaining literal far coordinate is not primitive.  On the exact literal
carrier, the pair source has an already-defined base zero source; the residual
difference is exactly the horizontal correction.  We expose that split only on
the existing far predicate and the existing centered finite exhaustion.

No absolute value and no new far surrogate is introduced.
-/

def QuarticFourSignedPolePair.literalFarBaseExactTerm
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (rho : Zeros) : ℝ :=
  if quarticSignedPoleFar t eta rho then
    W.signedZeroSourceTerm rho
  else
    0

def QuarticFourSignedPolePair.literalFarHorizontalExactTerm
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (rho : Zeros) : ℝ :=
  if quarticSignedPoleFar t eta rho then
    W.literalOffOrdSource rho - W.signedZeroSourceTerm rho
  else
    0

theorem QuarticFourSignedPolePair.literalFarExactTerm_eq_base_add_horizontal
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.literalFarExactTerm eta rho
      =
    W.literalFarBaseExactTerm eta rho
      + W.literalFarHorizontalExactTerm eta rho := by
  by_cases hf : quarticSignedPoleFar t eta rho
  · simp [QuarticFourSignedPolePair.literalFarExactTerm,
      QuarticFourSignedPolePair.literalFarBaseExactTerm,
      QuarticFourSignedPolePair.literalFarHorizontalExactTerm, hf]
  · simp [QuarticFourSignedPolePair.literalFarExactTerm,
      QuarticFourSignedPolePair.literalFarBaseExactTerm,
      QuarticFourSignedPolePair.literalFarHorizontalExactTerm, hf]

def QuarticFourSignedPolePair.literalFarBaseExactAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ :=
  ∑ rho ∈ centeredZeroFinset t n,
    W.literalFarBaseExactTerm eta rho

def QuarticFourSignedPolePair.literalFarHorizontalExactAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ :=
  ∑ rho ∈ centeredZeroFinset t n,
    W.literalFarHorizontalExactTerm eta rho

theorem QuarticFourSignedPolePair.literalFarExactAt_eq_base_add_horizontal
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalFarExactAt eta n
      =
    W.literalFarBaseExactAt eta n
      + W.literalFarHorizontalExactAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalFarExactAt
    QuarticFourSignedPolePair.literalFarBaseExactAt
    QuarticFourSignedPolePair.literalFarHorizontalExactAt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  exact W.literalFarExactTerm_eq_base_add_horizontal rho

theorem QuarticFourSignedPolePair.literalSharpenedSignedCompensationAt_eq_farSplit
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalSharpenedSignedCompensationAt eta n
      =
    W.literalConeGainAt eta n
      + W.literalGoodQuarticGainAt eta n
      - W.literalFarBaseExactAt eta n
      - W.literalFarHorizontalExactAt eta n := by
  unfold QuarticFourSignedPolePair.literalSharpenedSignedCompensationAt
  rw [W.literalFarExactAt_eq_base_add_horizontal]
  ring

def QuarticFourSignedPolePair.literalFarSplitBudgetAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ :=
  W.literalSharpenedLocalDebtAt eta n
    - W.literalConeGainAt eta n
    - W.literalGoodQuarticGainAt eta n
    + W.literalFarBaseExactAt eta n
    + W.literalFarHorizontalExactAt eta n

theorem QuarticFourSignedPolePair.literalFarSplitBudgetAt_eq_sharpenedJointBudget
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalFarSplitBudgetAt eta n
      = W.literalSharpenedJointBudgetAt eta n := by
  unfold QuarticFourSignedPolePair.literalFarSplitBudgetAt
    QuarticFourSignedPolePair.literalSharpenedJointBudgetAt
  rw [W.literalSharpenedSignedCompensationAt_eq_farSplit]
  ring

theorem QuarticFourSignedPolePair.literalOffOrdExactAt_le_farSplitBudget
    {t eta : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalOffOrdExactAt n
      <= W.literalFarSplitBudgetAt eta n := by
  rw [W.literalFarSplitBudgetAt_eq_sharpenedJointBudget]
  exact W.literalOffOrdExactAt_le_sharpenedJointBudget ht n



/-!
## Uniform shell payment for the exact far base carrier

The base part of the literal far source is the exact signed zero test already
used by the N-mu/Abel stack.  Its pointwise inverse-square decay can therefore
be combined directly with the unconditional literal zero shell bound.

For any natural cutoff J lying inside the physical far boundary eta*(t/16),
the resulting estimate is uniform in the centered exhaustion index n.
-/

open Zeta23Bridge.FarShellCutoffTailBound

theorem QuarticFourSignedPolePair.literalFarBaseExactTerm_abs_le_tailTermFrom
    {t eta : ℝ}
    (ht : 0 < t)
    (heta : 0 <= eta)
    (W : QuarticFourSignedPolePair t)
    {J : ℕ}
    (hJ : 1 <= J)
    (hJcut : (J : ℝ) <= eta * (t/16))
    (rho : Zeros) :
    |W.literalFarBaseExactTerm eta rho|
      <=
    W.signedOrdinateCurvature
      * tailTermFrom t J rho := by
  by_cases hf : quarticSignedPoleFar t eta rho
  · have hr : 0 < t/16 := by positivity
    have hfar := hf
    unfold quarticSignedPoleFar
      quarticSignedPoleNormalizedOrdinateOffset at hfar
    rw [abs_div, abs_of_pos hr] at hfar
    have hphysical :
        eta * (t/16) < |(rho : ℂ).im-t| := by
      exact (lt_div_iff₀ hr).mp hfar
    have hJgap :
        (J : ℝ) <= |(rho : ℂ).im-t| := by
      exact hJcut.trans hphysical.le
    have hJreal : (1 : ℝ) <= (J : ℝ) := by
      exact_mod_cast hJ
    have hgapPos :
        0 < |(rho : ℂ).im-t| := by
      exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 1)
        (hJreal.trans hJgap)
    have hxt : (rho : ℂ).im ≠ t := by
      intro heq
      rw [heq, sub_self, abs_zero] at hgapPos
      linarith
    have hphi :=
      W.signedOrdinateTest_abs_le_gap_sq ht hxt
    have hm :
        0 <= ((zetaZeroConfig).mult (rho : ℂ) : ℝ) := by
      positivity
    have hcurv := W.signedOrdinateCurvature_nonneg
    unfold QuarticFourSignedPolePair.literalFarBaseExactTerm
      QuarticFourSignedPolePair.signedZeroSourceTerm
    rw [if_pos hf, abs_mul, abs_of_nonneg hm]
    unfold tailTermFrom
    rw [if_pos hJgap]
    calc
      ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
          * |W.signedOrdinateTest (rho : ℂ).im|
        <=
      ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
          * (W.signedOrdinateCurvature
              / ((rho : ℂ).im-t)^2) :=
        mul_le_mul_of_nonneg_left hphi hm
      _ =
      W.signedOrdinateCurvature
        * (((zetaZeroConfig).mult (rho : ℂ) : ℝ)
            / ((rho : ℂ).im-t)^2) := by ring
  · simp [QuarticFourSignedPolePair.literalFarBaseExactTerm,
      hf, tailTermFrom_nonneg, W.signedOrdinateCurvature_nonneg]

theorem exists_literalFarBaseExactAt_uniform_shell_bound :
    ∃ A : ℝ, 1 <= A ∧
      ∀ {t eta : ℝ},
        0 < t ->
        0 <= eta ->
        (W : QuarticFourSignedPolePair t) ->
        ∀ {J : ℕ},
          1 <= J ->
          (J : ℝ) <= eta * (t/16) ->
          ∀ n : ℕ,
            |W.literalFarBaseExactAt eta n|
              <=
            W.signedOrdinateCurvature
              * farShellBound A |t| J := by
  obtain ⟨A,hA1,hloc⟩ :=
    Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨A,hA1,?_⟩
  intro t eta ht heta W J hJ hJcut n
  classical
  have hcurv := W.signedOrdinateCurvature_nonneg
  have htail :=
    tsum_tailTermFrom_le hA1 hloc t J hJ
  have hsumTail := summable_tailTermFrom hJ t
  unfold QuarticFourSignedPolePair.literalFarBaseExactAt
  calc
    |∑ rho ∈ centeredZeroFinset t n,
        W.literalFarBaseExactTerm eta rho|
      <=
    ∑ rho ∈ centeredZeroFinset t n,
        |W.literalFarBaseExactTerm eta rho| := by
          exact abs_sum_le_sum_abs _ _
    _ <=
    ∑ rho ∈ centeredZeroFinset t n,
        W.signedOrdinateCurvature * tailTermFrom t J rho := by
          apply Finset.sum_le_sum
          intro rho hrho
          exact W.literalFarBaseExactTerm_abs_le_tailTermFrom
            ht heta hJ hJcut rho
    _ <=
    ∑' rho : Zeros,
      W.signedOrdinateCurvature * tailTermFrom t J rho := by
        exact
          (hsumTail.mul_left W.signedOrdinateCurvature).sum_le_tsum
            (centeredZeroFinset t n)
            (fun rho hrho =>
              mul_nonneg hcurv (tailTermFrom_nonneg t J rho))
    _ =
    W.signedOrdinateCurvature
      * (∑' rho : Zeros, tailTermFrom t J rho) := by
        rw [tsum_mul_left]
    _ <=
    W.signedOrdinateCurvature
      * farShellBound A |t| J :=
        mul_le_mul_of_nonneg_left htail hcurv

theorem exists_canonicalLiteralFarBaseExactAt_uniform_shell_bound :
    ∃ A : ℝ, 1 <= A ∧
      ∀ {t : ℝ},
        0 < t ->
        (W : QuarticFourSignedPolePair t) ->
        ∀ {J : ℕ},
          1 <= J ->
          (J : ℝ)
            <= quarticSignedPoleCanonicalLocalRadius * (t/16) ->
          ∀ n : ℕ,
            |W.literalFarBaseExactAt
                quarticSignedPoleCanonicalLocalRadius n|
              <=
            W.signedOrdinateCurvature
              * farShellBound A |t| J := by
  obtain ⟨A,hA,hbound⟩ :=
    exists_literalFarBaseExactAt_uniform_shell_bound
  refine ⟨A,hA,?_⟩
  intro t ht W J hJ hJcut n
  exact hbound ht quarticSignedPoleCanonicalLocalRadius_pos.le
    W hJ hJcut n



/-!
## Concrete linear high-ordinate cutoff

For a closure-facing scalar interface we choose the deliberately conservative
cutoff floor(t/2000).  It is inside the canonical physical far boundary for
t >= 2000 because eta0 = 1/(pi+1) > 1/80.

The constant 2000 is not optimized; its role is only to remove the auxiliary
cutoff quantifier while retaining an explicit decaying shell bound.
-/

def quarticSignedPoleCanonicalFarCutoff (t : ℝ) : ℕ :=
  ⌊t / 2000⌋₊

theorem quarticSignedPoleCanonicalLocalRadius_gt_one_div_eighty :
    (1/80 : ℝ) < quarticSignedPoleCanonicalLocalRadius := by
  unfold quarticSignedPoleCanonicalLocalRadius
  rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 80)
      (by positivity : 0 < Real.pi + 1)]
  nlinarith [Real.pi_lt_four]

theorem quarticSignedPoleCanonicalFarCutoff_one_le
    {t : ℝ} (ht : 2000 <= t) :
    1 <= quarticSignedPoleCanonicalFarCutoff t := by
  unfold quarticSignedPoleCanonicalFarCutoff
  rw [Nat.le_floor]
  norm_num
  linarith

theorem quarticSignedPoleCanonicalFarCutoff_cast_le
    {t : ℝ} (ht : 2000 <= t) :
    (quarticSignedPoleCanonicalFarCutoff t : ℝ)
      <= quarticSignedPoleCanonicalLocalRadius * (t/16) := by
  have ht0 : 0 <= t := by linarith
  have hfloor :
      (quarticSignedPoleCanonicalFarCutoff t : ℝ) <= t/2000 := by
    unfold quarticSignedPoleCanonicalFarCutoff
    exact Nat.floor_le (by positivity)
  have heta :=
    quarticSignedPoleCanonicalLocalRadius_gt_one_div_eighty
  have hcoeff :
      (1/2000 : ℝ)
        <= quarticSignedPoleCanonicalLocalRadius / 16 := by
    nlinarith
  have hmul :=
    mul_le_mul_of_nonneg_right hcoeff ht0
  have hscale :
      t/2000
        <= quarticSignedPoleCanonicalLocalRadius * (t/16) := by
    calc
      t/2000 = (1/2000 : ℝ) * t := by ring
      _ <= (quarticSignedPoleCanonicalLocalRadius / 16) * t := hmul
      _ = quarticSignedPoleCanonicalLocalRadius * (t/16) := by ring
  exact hfloor.trans hscale

theorem exists_canonicalLiteralFarBaseExactAt_linearCutoff_bound :
    ∃ A : ℝ, 1 <= A ∧
      ∀ {t : ℝ},
        2000 <= t ->
        (W : QuarticFourSignedPolePair t) ->
        ∀ n : ℕ,
          |W.literalFarBaseExactAt
              quarticSignedPoleCanonicalLocalRadius n|
            <=
          W.signedOrdinateCurvature
            *
          farShellBound A |t|
            (quarticSignedPoleCanonicalFarCutoff t) := by
  obtain ⟨A,hA,hbound⟩ :=
    exists_canonicalLiteralFarBaseExactAt_uniform_shell_bound
  refine ⟨A,hA,?_⟩
  intro t ht W n
  have htpos : 0 < t := by linarith
  exact hbound htpos W
    (quarticSignedPoleCanonicalFarCutoff_one_le ht)
    (quarticSignedPoleCanonicalFarCutoff_cast_le ht)
    n

theorem quarticSignedPoleCanonicalFarShellBound_eq
    (A t : ℝ) :
    farShellBound A |t|
        (quarticSignedPoleCanonicalFarCutoff t)
      =
    18 * A * Real.log (|t|+4)
        / quarticSignedPoleCanonicalFarCutoff t
      +
    72 * A
        / Real.sqrt (quarticSignedPoleCanonicalFarCutoff t) := by
  exact farShellBound_eq A |t|
    (quarticSignedPoleCanonicalFarCutoff t)



/-!
## Identify the exact far-horizontal carrier

The difference introduced by the far split is exactly the already-existing
endpoint-linear horizontal source.  This removes the last representation
ambiguity from the literal far-horizontal finite sum.
-/

def QuarticFourSignedPolePair.signedHorizontalSourceTerm
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) : ℝ :=
  W.poleTwo *
      quarticFourHorizontalSourceTerm
        W.R (1/2) W.muHalf t rho
    +
  (-W.poleHalf) *
      quarticFourHorizontalSourceTerm
        W.R (2/3) W.muTwo t rho

theorem QuarticFourSignedPolePair.literalOffOrdSource_sub_zero_eq_horizontalSource
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)) :
    W.literalOffOrdSource rho - W.signedZeroSourceTerm rho
      = W.signedHorizontalSourceTerm rho := by
  unfold QuarticFourSignedPolePair.literalOffOrdSource
  rw [dif_pos hoff]
  unfold QuarticFourSignedPolePair.signedLiteralPairSourceTerm
    QuarticFourSignedPolePair.signedHorizontalSourceTerm
  rw [W.signedZeroSourceTerm_eq_linear,
      quarticFourPairDefect_eq_base_add_horizontal,
      quarticFourPairDefect_eq_base_add_horizontal]
  ring

theorem quarticSignedPoleFar_mem_offOrd
    {t eta : ℝ}
    (heta : 0 < eta)
    (rho : Zeros)
    (hfar : quarticSignedPoleFar t eta rho) :
    rho ∈ ((SameOrd t)ᶜ : Set Zeros) := by
  rw [Set.mem_compl_iff]
  intro hsame
  have him : (rho : ℂ).im = t := by
    exact hsame
  unfold quarticSignedPoleFar
    quarticSignedPoleNormalizedOrdinateOffset at hfar
  rw [him, sub_self, zero_div, abs_zero] at hfar
  linarith

theorem QuarticFourSignedPolePair.literalFarHorizontalExactTerm_eq_horizontalSource
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (heta : 0 < eta)
    (rho : Zeros) :
    W.literalFarHorizontalExactTerm eta rho
      =
    if quarticSignedPoleFar t eta rho then
      W.signedHorizontalSourceTerm rho
    else
      0 := by
  by_cases hfar : quarticSignedPoleFar t eta rho
  · have hoff := quarticSignedPoleFar_mem_offOrd heta rho hfar
    rw [if_pos hfar]
    unfold QuarticFourSignedPolePair.literalFarHorizontalExactTerm
    rw [if_pos hfar]
    exact W.literalOffOrdSource_sub_zero_eq_horizontalSource rho hoff
  · simp [QuarticFourSignedPolePair.literalFarHorizontalExactTerm, hfar]

theorem QuarticFourSignedPolePair.literalFarHorizontalExactAt_eq_horizontalSource
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (heta : 0 < eta)
    (n : ℕ) :
    W.literalFarHorizontalExactAt eta n
      =
    ∑ rho ∈ centeredZeroFinset t n,
      if quarticSignedPoleFar t eta rho then
        W.signedHorizontalSourceTerm rho
      else
        0 := by
  classical
  unfold QuarticFourSignedPolePair.literalFarHorizontalExactAt
  apply Finset.sum_congr rfl
  intro rho hrho
  exact W.literalFarHorizontalExactTerm_eq_horizontalSource heta rho

theorem QuarticFourSignedPolePair.signedHorizontalSourceTerm_summable_offOrd
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    Summable
      (fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
        W.signedHorizontalSourceTerm (sigma : Zeros)) := by
  have h1 :=
    (quarticFourHorizontalSourceTerm_summable_offOrd
      (R:=W.R) (lam:=(1/2 : ℝ)) (mu:=W.muHalf)
      W.Rpos ht).mul_left W.poleTwo
  have h2 :=
    (quarticFourHorizontalSourceTerm_summable_offOrd
      (R:=W.R) (lam:=(2/3 : ℝ)) (mu:=W.muTwo)
      W.Rpos ht).mul_left (-W.poleHalf)
  exact h1.add h2



/-!
## Quadratic q-decay of the exact signed horizontal kernel

For fixed normalized horizontal displacement alpha, the signed horizontal
kernel is the cosine transform of the exact combined projective profile
multiplied by cosh(alpha*u)-1.  Two integrations by parts therefore give
quadratic decay in the normalized ordinate variable q.
-/

open Zeta23Bridge.OscillatoryKernelDecay

def QuarticFourSignedPolePair.signedHorizontalDecayWeight
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (alpha u : ℝ) : ℝ :=
  quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t u
    * (Real.cosh (alpha*u) - 1)

def QuarticFourSignedPolePair.signedHorizontalDecayCurvature
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (alpha : ℝ) : ℝ :=
  ∫ u : ℝ,
    |deriv (deriv (W.signedHorizontalDecayWeight alpha)) u|

theorem QuarticFourSignedPolePair.signedHorizontalDecayCurvature_nonneg
    {t alpha : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.signedHorizontalDecayCurvature alpha := by
  unfold QuarticFourSignedPolePair.signedHorizontalDecayCurvature
  positivity

theorem QuarticFourSignedPolePair.signedHorizontalDecayWeight_contDiff_two
    {t alpha : ℝ}
    (W : QuarticFourSignedPolePair t) :
    ContDiff ℝ 2 (W.signedHorizontalDecayWeight alpha) := by
  unfold QuarticFourSignedPolePair.signedHorizontalDecayWeight
  exact
    (quarticFourSignedPoleCombinedProfile_contDiff_two W.Rpos).mul
      (by fun_prop)

theorem QuarticFourSignedPolePair.signedHorizontalDecayWeight_compact
    {t alpha : ℝ}
    (W : QuarticFourSignedPolePair t) :
    HasCompactSupport (W.signedHorizontalDecayWeight alpha) := by
  unfold QuarticFourSignedPolePair.signedHorizontalDecayWeight
  exact
    (quarticFourSignedPoleCombinedProfile_compact W.Rpos).mul_right

theorem QuarticFourSignedPolePair.signedNormalizedHorizontalKernel_eq_decayIntegral
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.signedNormalizedHorizontalKernel alpha q
      =
    ∫ u : ℝ,
      W.signedHorizontalDecayWeight alpha u
        * Real.cos (q*u) := by
  let P1 :=
    quarticFourNormalizedProjectiveProfile
      W.R (1/2) W.muHalf
  let P2 :=
    quarticFourNormalizedProjectiveProfile
      W.R (2/3) W.muTwo
  have h1 :
      Integrable
        (fun u : ℝ =>
          P1 u * (Real.cosh (alpha*u)-1) * Real.cos (q*u)) :=
    Continuous.integrable_of_hasCompactSupport
      (by dsimp [P1]; fun_prop)
      (((quarticFourNormalizedProjectiveProfile_compact W.Rpos).mul_right).mul_right)
  have h2 :
      Integrable
        (fun u : ℝ =>
          P2 u * (Real.cosh (alpha*u)-1) * Real.cos (q*u)) :=
    Continuous.integrable_of_hasCompactSupport
      (by dsimp [P2]; fun_prop)
      (((quarticFourNormalizedProjectiveProfile_compact W.Rpos).mul_right).mul_right)
  unfold QuarticFourSignedPolePair.signedNormalizedHorizontalKernel
    genericProjectiveHorizontalKernel
    QuarticFourSignedPolePair.signedHorizontalDecayWeight
    quarticFourSignedPoleCombinedProfile profileLinearCombination
  rw [show
      (fun u : ℝ =>
        (W.poleTwo *
            quarticFourNormalizedProjectiveProfile
              W.R (1/2) W.muHalf u
          + (-W.poleHalf) *
            quarticFourNormalizedProjectiveProfile
              W.R (2/3) W.muTwo u)
          * (Real.cosh (alpha*u)-1)
          * Real.cos (q*u))
      =
      fun u =>
        W.poleTwo *
          (P1 u * (Real.cosh (alpha*u)-1) * Real.cos (q*u))
        +
        (-W.poleHalf) *
          (P2 u * (Real.cosh (alpha*u)-1) * Real.cos (q*u)) by
      funext u
      dsimp [P1,P2]
      ring,
      integral_add (h1.const_mul _) (h2.const_mul _),
      integral_const_mul, integral_const_mul]
  ring

theorem QuarticFourSignedPolePair.signedNormalizedHorizontalKernel_abs_le_invSq
    {t alpha q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hq : q ≠ 0) :
    |W.signedNormalizedHorizontalKernel alpha q|
      <= W.signedHorizontalDecayCurvature alpha / q^2 := by
  rw [W.signedNormalizedHorizontalKernel_eq_decayIntegral]
  exact
    abs_integral_mul_cos_le
      (W.signedHorizontalDecayWeight_contDiff_two)
      (W.signedHorizontalDecayWeight_compact)
      hq



/-!
## Physical rescaling of the exact horizontal source

The normalized q^-2 decay is now transported back to the literal zero carrier.
The r^-2 source normalization cancels exactly against q^-2=(delta/r)^-2.
-/

theorem quarticFourHorizontalSourceTerm_eq_normalizedHorizontalKernel
    {R lam mu t : ℝ}
    (hR : 0 < R)
    (ht : 0 < t)
    (rho : Zeros) :
    quarticFourHorizontalSourceTerm R lam mu t rho
      =
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2
      *
    genericProjectiveHorizontalKernel
      (quarticFourWindowProfile R lam mu)
      (heightOf rho / (t/16))
      (((rho : ℂ).im-t)/(t/16)) := by
  unfold quarticFourHorizontalSourceTerm
  rw [literalPairProjectiveDefect_rescale
        (quarticFourWindowProfile_contDiff
          (lam:=lam) (mu:=mu) hR)
        (quarticFourWindowProfile_compact hR)
        (quarticFourWindowProfile_even R lam mu)
        (by positivity : 0 < t/16) t rho,
      quarticFourBaseSourceTerm_eq_normalizedKernel,
      genericProjectivePairKernel_eq_base_add_horizontal
        (quarticFourWindowProfile_continuous hR)
        (quarticFourWindowProfile_compact hR)]
  ring

theorem QuarticFourSignedPolePair.signedHorizontalSourceTerm_eq_normalized
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.signedHorizontalSourceTerm rho
      =
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2
      *
    W.signedNormalizedHorizontalKernel
      (heightOf rho / (t/16))
      (((rho : ℂ).im-t)/(t/16)) := by
  unfold QuarticFourSignedPolePair.signedHorizontalSourceTerm
    QuarticFourSignedPolePair.signedNormalizedHorizontalKernel
  rw [quarticFourHorizontalSourceTerm_eq_normalizedHorizontalKernel
        W.Rpos ht,
      quarticFourHorizontalSourceTerm_eq_normalizedHorizontalKernel
        W.Rpos ht]
  ring

theorem QuarticFourSignedPolePair.signedHorizontalSourceTerm_abs_le_gap_sq
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hdelta : (rho : ℂ).im ≠ t) :
    |W.signedHorizontalSourceTerm rho|
      <=
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * W.signedHorizontalDecayCurvature
          (heightOf rho / (t/16))
      / ((rho : ℂ).im-t)^2 := by
  have hr : 0 < t/16 := by positivity
  have hq :
      ((rho : ℂ).im-t)/(t/16) ≠ 0 := by
    exact div_ne_zero (sub_ne_zero.mpr hdelta) hr.ne'
  have hdec :=
    W.signedNormalizedHorizontalKernel_abs_le_invSq
      (alpha:=heightOf rho/(t/16)) hq
  rw [W.signedHorizontalSourceTerm_eq_normalized ht rho,
      abs_mul]
  have hm :
      0 <= ((zetaZeroConfig).mult (rho : ℂ) : ℝ) := by
    positivity
  have hr2 : 0 < (t/16)^2 := by positivity
  rw [abs_of_nonneg (div_nonneg hm hr2.le)]
  have hmul :=
    mul_le_mul_of_nonneg_left hdec
      (div_nonneg hm hr2.le)
  calc
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2
      *
      |W.signedNormalizedHorizontalKernel
        (heightOf rho/(t/16))
        (((rho : ℂ).im-t)/(t/16))|
      <=
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2
      *
      (W.signedHorizontalDecayCurvature
          (heightOf rho/(t/16))
        / (((rho : ℂ).im-t)/(t/16))^2) := hmul
    _ =
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * W.signedHorizontalDecayCurvature
          (heightOf rho/(t/16))
      / ((rho : ℂ).im-t)^2 := by
        field_simp [show t ≠ 0 by linarith,
          sub_ne_zero.mpr hdelta]
        ring



/-!
## Far-horizontal shell compiler with one explicit curvature coordinate

The exact horizontal per-zero decay is already paid.  The only remaining
uniformity issue is whether the selected witness admits one scalar C_H bounding
its normalized horizontal decay curvature over the literal zero carrier.

We expose exactly that coordinate and no stronger regularity package.
-/

def QuarticFourSignedPolePair.HorizontalFarCurvatureBound
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (CH : ℝ) : Prop :=
  ∀ rho : Zeros,
    W.signedHorizontalDecayCurvature
      (heightOf rho / (t/16)) <= CH

theorem QuarticFourSignedPolePair.literalFarHorizontalExactTerm_abs_le_tailTermFrom
    {t eta CH : ℝ}
    (ht : 0 < t)
    (heta : 0 < eta)
    (hCH : 0 <= CH)
    (W : QuarticFourSignedPolePair t)
    (hCurv : W.HorizontalFarCurvatureBound CH)
    {J : ℕ}
    (hJ : 1 <= J)
    (hJcut : (J : ℝ) <= eta * (t/16))
    (rho : Zeros) :
    |W.literalFarHorizontalExactTerm eta rho|
      <= CH * tailTermFrom t J rho := by
  by_cases hfar : quarticSignedPoleFar t eta rho
  · have hr : 0 < t/16 := by positivity
    have hfar' := hfar
    unfold quarticSignedPoleFar
      quarticSignedPoleNormalizedOrdinateOffset at hfar'
    rw [abs_div, abs_of_pos hr] at hfar'
    have hphysical :
        eta * (t/16) < |(rho : ℂ).im-t| := by
      exact (lt_div_iff₀ hr).mp hfar'
    have hJgap :
        (J : ℝ) <= |(rho : ℂ).im-t| := by
      exact hJcut.trans hphysical.le
    have hJreal : (1 : ℝ) <= (J : ℝ) := by
      exact_mod_cast hJ
    have hgapPos :
        0 < |(rho : ℂ).im-t| := by
      exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 1)
        (hJreal.trans hJgap)
    have hdelta : (rho : ℂ).im ≠ t := by
      intro heq
      rw [heq, sub_self, abs_zero] at hgapPos
      linarith
    have hsrc :=
      W.signedHorizontalSourceTerm_abs_le_gap_sq ht rho hdelta
    have hcurv :=
      hCurv rho
    have hm :
        0 <= ((zetaZeroConfig).mult (rho : ℂ) : ℝ) := by
      positivity
    have hd2 :
        0 < ((rho : ℂ).im-t)^2 := by
      positivity
    have hpoint :
        ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
            * W.signedHorizontalDecayCurvature
                (heightOf rho/(t/16))
            / ((rho : ℂ).im-t)^2
          <=
        ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
            * CH
            / ((rho : ℂ).im-t)^2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcurv hm) hd2.le
    rw [W.literalFarHorizontalExactTerm_eq_horizontalSource heta rho]
    rw [if_pos hfar]
    unfold tailTermFrom
    rw [if_pos hJgap]
    exact hsrc.trans (hpoint.trans_eq (by ring))
  · simp [QuarticFourSignedPolePair.literalFarHorizontalExactTerm,
      hfar, tailTermFrom_nonneg, hCH]

theorem exists_literalFarHorizontalExactAt_uniform_shell_bound :
    ∃ A : ℝ, 1 <= A ∧
      ∀ {t eta CH : ℝ},
        0 < t ->
        0 < eta ->
        0 <= CH ->
        (W : QuarticFourSignedPolePair t) ->
        W.HorizontalFarCurvatureBound CH ->
        ∀ {J : ℕ},
          1 <= J ->
          (J : ℝ) <= eta * (t/16) ->
          ∀ n : ℕ,
            |W.literalFarHorizontalExactAt eta n|
              <=
            CH * farShellBound A |t| J := by
  obtain ⟨A,hA1,hloc⟩ :=
    Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨A,hA1,?_⟩
  intro t eta CH ht heta hCH W hCurv J hJ hJcut n
  classical
  have htail :=
    tsum_tailTermFrom_le hA1 hloc t J hJ
  have hsumTail := summable_tailTermFrom hJ t
  unfold QuarticFourSignedPolePair.literalFarHorizontalExactAt
  calc
    |∑ rho ∈ centeredZeroFinset t n,
        W.literalFarHorizontalExactTerm eta rho|
      <=
    ∑ rho ∈ centeredZeroFinset t n,
        |W.literalFarHorizontalExactTerm eta rho| := by
          exact abs_sum_le_sum_abs _ _
    _ <=
    ∑ rho ∈ centeredZeroFinset t n,
        CH * tailTermFrom t J rho := by
          apply Finset.sum_le_sum
          intro rho hrho
          exact W.literalFarHorizontalExactTerm_abs_le_tailTermFrom
            ht heta hCH hCurv hJ hJcut rho
    _ <=
    ∑' rho : Zeros, CH * tailTermFrom t J rho := by
        exact
          (hsumTail.mul_left CH).sum_le_tsum
            (centeredZeroFinset t n)
            (fun rho hrho =>
              mul_nonneg hCH (tailTermFrom_nonneg t J rho))
    _ =
    CH * (∑' rho : Zeros, tailTermFrom t J rho) := by
        rw [tsum_mul_left]
    _ <= CH * farShellBound A |t| J :=
      mul_le_mul_of_nonneg_left htail hCH

/--
Combined theorem: once one horizontal-curvature scalar is supplied, the whole
literal FarExact coordinate is bounded by the same explicit zero-shell tail.
-/
theorem exists_literalFarExactAt_uniform_shell_bound_of_horizontalCurvature :
    ∃ A : ℝ, 1 <= A ∧
      ∀ {t eta CH : ℝ},
        0 < t ->
        0 < eta ->
        0 <= CH ->
        (W : QuarticFourSignedPolePair t) ->
        W.HorizontalFarCurvatureBound CH ->
        ∀ {J : ℕ},
          1 <= J ->
          (J : ℝ) <= eta * (t/16) ->
          ∀ n : ℕ,
            |W.literalFarExactAt eta n|
              <=
            (W.signedOrdinateCurvature + CH)
              * farShellBound A |t| J := by
  obtain ⟨A,hA1,hloc⟩ :=
    Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨A,hA1,?_⟩
  intro t eta CH ht heta hCH W hCurv J hJ hJcut n
  classical
  have htail :=
    tsum_tailTermFrom_le hA1 hloc t J hJ
  have hsumTail := summable_tailTermFrom hJ t
  have hbaseTerm :
      ∀ rho : Zeros,
        |W.literalFarBaseExactTerm eta rho|
          <= W.signedOrdinateCurvature * tailTermFrom t J rho :=
    fun rho =>
      W.literalFarBaseExactTerm_abs_le_tailTermFrom
        ht heta.le hJ hJcut rho
  have hhorTerm :
      ∀ rho : Zeros,
        |W.literalFarHorizontalExactTerm eta rho|
          <= CH * tailTermFrom t J rho :=
    fun rho =>
      W.literalFarHorizontalExactTerm_abs_le_tailTermFrom
        ht heta hCH hCurv hJ hJcut rho
  have hcoef :
      0 <= W.signedOrdinateCurvature + CH := by
    exact add_nonneg W.signedOrdinateCurvature_nonneg hCH
  rw [W.literalFarExactAt_eq_base_add_horizontal]
  calc
    |W.literalFarBaseExactAt eta n
        + W.literalFarHorizontalExactAt eta n|
      <=
    |W.literalFarBaseExactAt eta n|
      + |W.literalFarHorizontalExactAt eta n| :=
        abs_add _ _
    _ <=
    ∑ rho ∈ centeredZeroFinset t n,
      ((W.signedOrdinateCurvature + CH)
        * tailTermFrom t J rho) := by
      unfold QuarticFourSignedPolePair.literalFarBaseExactAt
        QuarticFourSignedPolePair.literalFarHorizontalExactAt
      have hb :
          |∑ rho ∈ centeredZeroFinset t n,
              W.literalFarBaseExactTerm eta rho|
            <=
          ∑ rho ∈ centeredZeroFinset t n,
              W.signedOrdinateCurvature * tailTermFrom t J rho := by
        calc
          |∑ rho ∈ centeredZeroFinset t n,
              W.literalFarBaseExactTerm eta rho|
            <= ∑ rho ∈ centeredZeroFinset t n,
              |W.literalFarBaseExactTerm eta rho| :=
                abs_sum_le_sum_abs _ _
          _ <= ∑ rho ∈ centeredZeroFinset t n,
              W.signedOrdinateCurvature * tailTermFrom t J rho := by
                apply Finset.sum_le_sum
                intro rho hrho
                exact hbaseTerm rho
      have hh :
          |∑ rho ∈ centeredZeroFinset t n,
              W.literalFarHorizontalExactTerm eta rho|
            <=
          ∑ rho ∈ centeredZeroFinset t n,
              CH * tailTermFrom t J rho := by
        calc
          |∑ rho ∈ centeredZeroFinset t n,
              W.literalFarHorizontalExactTerm eta rho|
            <= ∑ rho ∈ centeredZeroFinset t n,
              |W.literalFarHorizontalExactTerm eta rho| :=
                abs_sum_le_sum_abs _ _
          _ <= ∑ rho ∈ centeredZeroFinset t n,
              CH * tailTermFrom t J rho := by
                apply Finset.sum_le_sum
                intro rho hrho
                exact hhorTerm rho
      rw [← Finset.sum_add_distrib]
      refine (add_le_add hb hh).trans_eq ?_
      apply Finset.sum_congr rfl
      intro rho hrho
      ring
    _ <=
    ∑' rho : Zeros,
      (W.signedOrdinateCurvature + CH)
        * tailTermFrom t J rho := by
      exact
        (hsumTail.mul_left
          (W.signedOrdinateCurvature + CH)).sum_le_tsum
          (centeredZeroFinset t n)
          (fun rho hrho =>
            mul_nonneg hcoef (tailTermFrom_nonneg t J rho))
    _ =
    (W.signedOrdinateCurvature + CH)
      * (∑' rho : Zeros, tailTermFrom t J rho) := by
        rw [tsum_mul_left]
    _ <=
    (W.signedOrdinateCurvature + CH)
      * farShellBound A |t| J :=
        mul_le_mul_of_nonneg_left htail hcoef

theorem exists_canonicalLiteralFarExactAt_linearCutoff_bound_of_horizontalCurvature :
    ∃ A : ℝ, 1 <= A ∧
      ∀ {t CH : ℝ},
        2000 <= t ->
        0 <= CH ->
        (W : QuarticFourSignedPolePair t) ->
        W.HorizontalFarCurvatureBound CH ->
        ∀ n : ℕ,
          |W.literalFarExactAt
              quarticSignedPoleCanonicalLocalRadius n|
            <=
          (W.signedOrdinateCurvature + CH)
            *
          farShellBound A |t|
            (quarticSignedPoleCanonicalFarCutoff t) := by
  obtain ⟨A,hA,hbound⟩ :=
    exists_literalFarExactAt_uniform_shell_bound_of_horizontalCurvature
  refine ⟨A,hA,?_⟩
  intro t CH ht hCH W hCurv n
  have ht0 : 0 < t := by linarith
  exact hbound ht0 quarticSignedPoleCanonicalLocalRadius_pos
    hCH W hCurv
    (quarticSignedPoleCanonicalFarCutoff_one_le ht)
    (quarticSignedPoleCanonicalFarCutoff_cast_le ht)
    n



/-!
## Far-paid terminal scalar surface

The terminal source can now forget the finite FarExact carrier entirely once a
single horizontal curvature bound CH is supplied.  We retain the exact literal
zero count in the local terms and replace only FarExact by its theorem-bearing
canonical shell envelope.

This is deliberately the narrowest compiler needed for the remaining scalar
inequality.
-/

def QuarticFourSignedPolePair.postSixthTerminalFarPaidBudget
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (EV A CH : ℝ) : ℝ :=
  let eta := quarticSignedPoleCanonicalLocalRadius
  let r := quarticSignedPoleLocalHalfWidth t eta
  let NZ : ℝ :=
    (zetaZeroConfig.N (t-r-1) (t+r) : ℝ)
  let J := quarticSignedPoleCanonicalFarCutoff t
  (W.targetStrength / (6 * (t/16)^6))
    *
  (
    EV
      + (3/2 : ℝ) * r^2 * NZ
      - (2/5 : ℝ) * r^5
          * quarticSignedPoleMuLowerEnvelope (t-r)
  )
    +
  (((3/20 : ℝ) * Real.pi^6)
      * quarticSignedPoleLocalSixthPhaseEnvelope t eta
      / (720 * (t/16)^8))
    * NZ
    +
  (((Real.pi+1)^2 * W.fourthLipschitz)
      * quarticSignedPoleLocalEighthPhysicalEnvelope t eta
      / (t/16)^10)
    * NZ
    +
  (W.signedOrdinateCurvature + CH)
    * farShellBound A |t| J

theorem exists_postSixthTerminalM6BudgetAt_le_farPaidBudget :
    ∃ A : ℝ, 1 <= A ∧
      ∀ {t EV CH : ℝ},
        2000 <= t ->
        0 <= CH ->
        (W : QuarticFourSignedPolePair t) ->
        W.HorizontalFarCurvatureBound CH ->
        ∀ n : ℕ,
          W.postSixthTerminalM6BudgetAt EV n
            <= W.postSixthTerminalFarPaidBudget EV A CH := by
  obtain ⟨A,hA,hfar⟩ :=
    exists_canonicalLiteralFarExactAt_linearCutoff_bound_of_horizontalCurvature
  refine ⟨A,hA,?_⟩
  intro t EV CH ht hCH W hCurv n
  have hfarAbs :=
    hfar ht hCH W hCurv n
  have hfarLe :
      W.literalFarExactAt
          quarticSignedPoleCanonicalLocalRadius n
        <=
      (W.signedOrdinateCurvature + CH)
        * farShellBound A |t|
          (quarticSignedPoleCanonicalFarCutoff t) :=
    (le_abs_self _).trans hfarAbs
  unfold QuarticFourSignedPolePair.postSixthTerminalM6BudgetAt
    QuarticFourSignedPolePair.postSixthTerminalFarPaidBudget
  dsimp
  linarith

def QuarticFourSignedPolePair.PostSixthTerminalFarPaidStrictAbsorb
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV A CH : ℝ) : Prop :=
  W.postSixthTerminalFarPaidBudget EV A CH
    < W.compensationTargetThreshold rho

theorem QuarticFourSignedPolePair.postSixthTerminalStrictAbsorb_of_farPaid
    {t EV A CH : ℝ}
    (ht : 2000 <= t)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hCH : 0 <= CH)
    (hCurv : W.HorizontalFarCurvatureBound CH)
    (hA : 1 <= A)
    (hFar :
      ∀ n : ℕ,
        |W.literalFarExactAt
            quarticSignedPoleCanonicalLocalRadius n|
          <=
        (W.signedOrdinateCurvature + CH)
          * farShellBound A |t|
            (quarticSignedPoleCanonicalFarCutoff t))
    (hscalar :
      W.PostSixthTerminalFarPaidStrictAbsorb rho EV A CH) :
    W.PostSixthTerminalStrictAbsorb rho EV := by
  let B := W.postSixthTerminalFarPaidBudget EV A CH
  let T := W.compensationTargetThreshold rho
  let eps := (T-B)/2
  have heps : 0 < eps := by
    dsimp [eps,B,T,
      QuarticFourSignedPolePair.PostSixthTerminalFarPaidStrictAbsorb] at *
    linarith
  obtain ⟨N,hN⟩ :=
    exists_nat_gt
      (quarticSignedPoleLocalHalfWidth
        t quarticSignedPoleCanonicalLocalRadius)
  refine ⟨eps,heps,N,?_⟩
  intro n hn
  have hnRadius :
      quarticSignedPoleLocalHalfWidth
          t quarticSignedPoleCanonicalLocalRadius
        < (n : ℝ) := by
    exact lt_of_lt_of_le hN (by exact_mod_cast hn)
  have hfarLe :
      W.literalFarExactAt
          quarticSignedPoleCanonicalLocalRadius n
        <=
      (W.signedOrdinateCurvature + CH)
        * farShellBound A |t|
          (quarticSignedPoleCanonicalFarCutoff t) :=
    (le_abs_self _).trans (hFar n)
  have hbudget :
      W.postSixthTerminalM6BudgetAt EV n
        <= W.postSixthTerminalFarPaidBudget EV A CH := by
    unfold QuarticFourSignedPolePair.postSixthTerminalM6BudgetAt
      QuarticFourSignedPolePair.postSixthTerminalFarPaidBudget
    dsimp
    linarith
  constructor
  · exact hnRadius
  · dsimp [eps,B,T,
      QuarticFourSignedPolePair.PostSixthTerminalFarPaidStrictAbsorb] at hscalar ⊢
    linarith

theorem exists_postSixthTerminalStrictAbsorb_of_horizontalCurvature_and_scalar :
    ∃ A : ℝ, 1 <= A ∧
      ∀ {t EV CH : ℝ},
        2000 <= t ->
        0 <= CH ->
        (W : QuarticFourSignedPolePair t) ->
        W.HorizontalFarCurvatureBound CH ->
        ∀ {rho : Zeros},
          W.PostSixthTerminalFarPaidStrictAbsorb rho EV A CH ->
          W.PostSixthTerminalStrictAbsorb rho EV := by
  obtain ⟨A,hA,hfar⟩ :=
    exists_canonicalLiteralFarExactAt_linearCutoff_bound_of_horizontalCurvature
  refine ⟨A,hA,?_⟩
  intro t EV CH ht hCH W hCurv rho hscalar
  exact W.postSixthTerminalStrictAbsorb_of_farPaid
    ht hCH hCurv hA
    (hfar ht hCH W hCurv)
    hscalar

theorem exists_completedSignedResidual_lt_target_of_horizontalCurvature_and_scalar :
    ∃ A : ℝ, 1 <= A ∧
      ∀ {t EV CH : ℝ},
        2000 <= t ->
        0 <= CH ->
        (W : QuarticFourSignedPolePair t) ->
        W.HorizontalFarCurvatureBound CH ->
        ∀ {rho : Zeros},
          (-(3/20 : ℝ) * Real.pi^6
              <= W.signedProfileMomentSix) ->
          W.signedProfileMomentSix < 0 ->
          (|quarticSignedPoleRvMVerticalFourthDiscrepancy
              t
              (quarticSignedPoleLocalHalfWidth
                t quarticSignedPoleCanonicalLocalRadius)|
            <= EV) ->
          W.PostSixthTerminalFarPaidStrictAbsorb rho EV A CH ->
          W.completedSignedResidual
            < 2 * W.combinedZeroHeightDefect rho := by
  obtain ⟨A,hA,hcompile⟩ :=
    exists_postSixthTerminalStrictAbsorb_of_horizontalCurvature_and_scalar
  refine ⟨A,hA,?_⟩
  intro t EV CH ht hCH W hCurv rho hM6lo hM6neg hV hscalar
  have hstrict :=
    hcompile ht hCH W hCurv hscalar
  exact
    W.completedSignedResidual_lt_target_of_postSixthTerminalStrictAbsorb
      (by linarith : 200 <= t)
      hM6lo hM6neg hV hstrict



/-!
## Far carrier is genuinely off-ordinate

For every positive normalized radius, the far predicate forces Im rho != t.
Thus on the canonical positive radius the zero-extension in literalOffOrdSource
is never active on the far carrier.
-/

theorem quarticSignedPoleFar_im_ne
    {t eta : ℝ} {rho : Zeros}
    (heta : 0 < eta)
    (hfar : quarticSignedPoleFar t eta rho) :
    (rho : ℂ).im ≠ t := by
  intro him
  have hzero :
      quarticSignedPoleNormalizedOrdinateOffset t rho = 0 := by
    unfold quarticSignedPoleNormalizedOrdinateOffset
    rw [him]
    simp
  unfold quarticSignedPoleFar at hfar
  rw [hzero, abs_zero] at hfar
  linarith

theorem quarticSignedPoleFar_mem_offOrd
    {t eta : ℝ} {rho : Zeros}
    (heta : 0 < eta)
    (hfar : quarticSignedPoleFar t eta rho) :
    rho ∈ ((SameOrd t)ᶜ : Set Zeros) := by
  have himne := quarticSignedPoleFar_im_ne heta hfar
  simpa [SameOrd] using himne

def QuarticFourSignedPolePair.signedHorizontalOffOrdSourceTerm
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (sigma : ((SameOrd t)ᶜ : Set Zeros)) : ℝ :=
  W.poleTwo *
      quarticFourHorizontalSourceTerm
        W.R (1/2) W.muHalf t (sigma : Zeros)
    +
  (-W.poleHalf) *
      quarticFourHorizontalSourceTerm
        W.R (2/3) W.muTwo t (sigma : Zeros)

theorem QuarticFourSignedPolePair.signedHorizontalOffOrdSourceTerm_summable
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    Summable W.signedHorizontalOffOrdSourceTerm := by
  have h1 :=
    (quarticFourHorizontalSourceTerm_summable_offOrd
      (R:=W.R) (lam:=(1/2 : ℝ)) (mu:=W.muHalf)
      W.Rpos ht).mul_left W.poleTwo
  have h2 :=
    (quarticFourHorizontalSourceTerm_summable_offOrd
      (R:=W.R) (lam:=(2/3 : ℝ)) (mu:=W.muTwo)
      W.Rpos ht).mul_left (-W.poleHalf)
  exact h1.add h2

theorem QuarticFourSignedPolePair.signedHorizontalRemainder_eq_half_tsum
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.signedHorizontalRemainder
      =
    (1/2 : ℝ) *
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        W.signedHorizontalOffOrdSourceTerm sigma) := by
  have h1 :=
    quarticFourHorizontalSourceTerm_summable_offOrd
      (R:=W.R) (lam:=(1/2 : ℝ)) (mu:=W.muHalf)
      W.Rpos ht
  have h2 :=
    quarticFourHorizontalSourceTerm_summable_offOrd
      (R:=W.R) (lam:=(2/3 : ℝ)) (mu:=W.muTwo)
      W.Rpos ht
  unfold QuarticFourSignedPolePair.signedHorizontalRemainder
    quarticFourHorizontalRemainder
    QuarticFourSignedPolePair.signedHorizontalOffOrdSourceTerm
  rw [(h1.mul_left W.poleTwo).tsum_add
      (h2.mul_left (-W.poleHalf)),
      tsum_mul_left, tsum_mul_left]
  ring

theorem QuarticFourSignedPolePair.signedLiteralPairSourceTerm_eq_base_add_horizontal
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (sigma : ((SameOrd t)ᶜ : Set Zeros)) :
    W.signedLiteralPairSourceTerm sigma
      =
    W.signedZeroSourceTerm (sigma : Zeros)
      + W.signedHorizontalOffOrdSourceTerm sigma := by
  unfold QuarticFourSignedPolePair.signedLiteralPairSourceTerm
    QuarticFourSignedPolePair.signedHorizontalOffOrdSourceTerm
  rw [quarticFourPairDefect_eq_base_add_horizontal
        W.R (1/2) W.muHalf t (sigma : Zeros),
      quarticFourPairDefect_eq_base_add_horizontal
        W.R (2/3) W.muTwo t (sigma : Zeros),
      W.signedZeroSourceTerm_eq_linear (sigma : Zeros)]
  ring

theorem QuarticFourSignedPolePair.literalOffOrdSource_eq_base_add_horizontal_of_offOrd
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)) :
    W.literalOffOrdSource rho
      =
    W.signedZeroSourceTerm rho
      +
    W.signedHorizontalOffOrdSourceTerm
        (⟨rho,hoff⟩ : ((SameOrd t)ᶜ : Set Zeros)) := by
  simp [QuarticFourSignedPolePair.literalOffOrdSource, hoff]
  exact
    W.signedLiteralPairSourceTerm_eq_base_add_horizontal
      (⟨rho,hoff⟩ : ((SameOrd t)ᶜ : Set Zeros))

theorem QuarticFourSignedPolePair.literalFarHorizontalExactTerm_eq_existing
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (heta : 0 < eta)
    {rho : Zeros}
    (hfar : quarticSignedPoleFar t eta rho) :
    W.literalFarHorizontalExactTerm eta rho
      =
    W.signedHorizontalOffOrdSourceTerm
      (⟨rho, quarticSignedPoleFar_mem_offOrd heta hfar⟩ :
        ((SameOrd t)ᶜ : Set Zeros)) := by
  let hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros) :=
    quarticSignedPoleFar_mem_offOrd heta hfar
  unfold QuarticFourSignedPolePair.literalFarHorizontalExactTerm
  rw [if_pos hfar]
  rw [W.literalOffOrdSource_eq_base_add_horizontal_of_offOrd hoff]
  ring

theorem QuarticFourSignedPolePair.literalFarExactTerm_eq_existing_base_horizontal
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (heta : 0 < eta)
    {rho : Zeros}
    (hfar : quarticSignedPoleFar t eta rho) :
    W.literalFarExactTerm eta rho
      =
    W.signedZeroSourceTerm rho
      +
    W.signedHorizontalOffOrdSourceTerm
      (⟨rho, quarticSignedPoleFar_mem_offOrd heta hfar⟩ :
        ((SameOrd t)ᶜ : Set Zeros)) := by
  rw [W.literalFarExactTerm_eq_base_add_horizontal]
  unfold QuarticFourSignedPolePair.literalFarBaseExactTerm
  rw [if_pos hfar,
      W.literalFarHorizontalExactTerm_eq_existing heta hfar]



/-!
## Canonical same-object far compensation

The discrete far zero source must not be estimated in isolation: the terminal
G3 object already contains the matching mu/Gamma channel.  We therefore cut
the exact signed N-mu scalar at the same canonical physical half-width used by
the local quartic source.

The remaining far coordinate is the complement of that finite centered N-mu
residual inside W.signedNMuPair.  This is exactly the object controlled by the
existing centered Abel tail machinery.
-/

def quarticSignedPoleCanonicalPhysicalHalfWidth
    (t : ℝ) : ℝ :=
  (t/16) * quarticSignedPoleCanonicalLocalRadius

theorem quarticSignedPoleCanonicalPhysicalHalfWidth_pos
    {t : ℝ} (ht : 0 < t) :
    0 < quarticSignedPoleCanonicalPhysicalHalfWidth t := by
  unfold quarticSignedPoleCanonicalPhysicalHalfWidth
  exact mul_pos (by positivity)
    quarticSignedPoleCanonicalLocalRadius_pos

def QuarticFourSignedPolePair.canonicalLocalNMuResidual
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  let h := quarticSignedPoleCanonicalPhysicalHalfWidth t
  W.signedCenteredWindowResidual (t-h) (t+h)

def QuarticFourSignedPolePair.canonicalFarNMuCompensation
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  W.signedNMuPair - W.canonicalLocalNMuResidual

def QuarticFourSignedPolePair.canonicalFarCompletedCompensation
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  (1/2 : ℝ) * W.canonicalFarNMuCompensation
    + W.signedHorizontalRemainder

theorem QuarticFourSignedPolePair.signedNMuPair_eq_canonicalLocal_add_far
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.signedNMuPair
      =
    W.canonicalLocalNMuResidual
      + W.canonicalFarNMuCompensation := by
  unfold QuarticFourSignedPolePair.canonicalFarNMuCompensation
  ring

theorem QuarticFourSignedPolePair.completedSignedResidual_eq_canonicalLocal_add_far
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.completedSignedResidual
      =
    (1/2 : ℝ) * W.canonicalLocalNMuResidual
      + W.canonicalFarCompletedCompensation := by
  unfold QuarticFourSignedPolePair.completedSignedResidual
    QuarticFourSignedPolePair.canonicalFarCompletedCompensation
    QuarticFourSignedPolePair.canonicalFarNMuCompensation
  ring

def QuarticFourSignedPolePair.canonicalLocalLeftBoundary
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  let h := quarticSignedPoleCanonicalPhysicalHalfWidth t
  W.signedOrdinateTest (t-h)
    * zetaMuCumulativeDiscrepancy (t-h) t

def QuarticFourSignedPolePair.canonicalLocalRightBoundary
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  let h := quarticSignedPoleCanonicalPhysicalHalfWidth t
  W.signedOrdinateTest (t+h)
    * centeredZetaMuDiscrepancy t (t+h)

def QuarticFourSignedPolePair.canonicalLocalLeftAbel
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  let h := quarticSignedPoleCanonicalPhysicalHalfWidth t
  ∫ x in (t-h)..t, W.centeredAbelIntegrand x

def QuarticFourSignedPolePair.canonicalLocalRightAbel
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  let h := quarticSignedPoleCanonicalPhysicalHalfWidth t
  ∫ x in t..(t+h), W.centeredAbelIntegrand x

theorem QuarticFourSignedPolePair.canonicalLocalNMuResidual_eq_centeredAbel
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.canonicalLocalNMuResidual
      =
    W.canonicalLocalLeftBoundary
      + W.canonicalLocalRightBoundary
      - W.canonicalLocalLeftAbel
      - W.canonicalLocalRightAbel := by
  let h := quarticSignedPoleCanonicalPhysicalHalfWidth t
  have hh : 0 <= h :=
    (quarticSignedPoleCanonicalPhysicalHalfWidth_pos ht).le
  have hA : t-h <= t := by linarith
  have hB : t <= t+h := by linarith
  have habel :=
    W.signedCenteredWindowResidual_eq_centeredAbel
      ht hA hB
  unfold QuarticFourSignedPolePair.canonicalLocalNMuResidual
    QuarticFourSignedPolePair.canonicalLocalLeftBoundary
    QuarticFourSignedPolePair.canonicalLocalRightBoundary
    QuarticFourSignedPolePair.canonicalLocalLeftAbel
    QuarticFourSignedPolePair.canonicalLocalRightAbel
    QuarticFourSignedPolePair.centeredAbelIntegrand
  dsimp [h] at habel ⊢
  exact habel

theorem QuarticFourSignedPolePair.canonicalFarNMuCompensation_eq_centeredAbel_tail
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (E : W.CenteredAbelExhaustion) :
    W.canonicalFarNMuCompensation
      =
    - E.leftLimit - E.rightLimit
      - W.canonicalLocalLeftBoundary
      - W.canonicalLocalRightBoundary
      + W.canonicalLocalLeftAbel
      + W.canonicalLocalRightAbel := by
  unfold QuarticFourSignedPolePair.canonicalFarNMuCompensation
  rw [W.signedNMuPair_eq_centeredAbel_limits ht E,
      W.canonicalLocalNMuResidual_eq_centeredAbel ht]
  ring

theorem QuarticFourSignedPolePair.canonicalFarCompletedCompensation_eq_centeredAbel_tail
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (E : W.CenteredAbelExhaustion) :
    W.canonicalFarCompletedCompensation
      =
    (1/2 : ℝ) *
      (
        - E.leftLimit - E.rightLimit
        - W.canonicalLocalLeftBoundary
        - W.canonicalLocalRightBoundary
        + W.canonicalLocalLeftAbel
        + W.canonicalLocalRightAbel
      )
      + W.signedHorizontalRemainder := by
  unfold QuarticFourSignedPolePair.canonicalFarCompletedCompensation
  rw [W.canonicalFarNMuCompensation_eq_centeredAbel_tail ht E]



/-!
## Canonical normalized compensation carrier

At the Clay-facing local cut the physical half-width is

  h = r * eta0,     r = t/16,
  eta0 = quarticSignedPoleCanonicalLocalRadius.

Thus the boundary is at the fixed normalized coordinate q = +/- eta0, not at a
large Fourier frequency.  This records the scale exactly and prevents a false
"more integrations by parts will pay the far tail" detour.

The exact signed ordinate test and its first derivative scale as r^-2 and r^-3
under x = t + r*q.  After dx = r dq, every centered Abel correlation therefore
has the global prefactor r^-2.  Since the target quartic signal is r^-6, the
remaining compensated discrepancy theorem must supply four additional inverse
powers of r by cancellation/sign, not by remote Fourier decay alone.
-/

theorem quarticSignedPoleCanonicalPhysicalHalfWidth_eq
    (t : ℝ) :
    quarticSignedPoleCanonicalPhysicalHalfWidth t
      =
    (t/16) * quarticSignedPoleCanonicalLocalRadius := by
  rfl

theorem quarticSignedPoleCanonicalRight_normalized
    {t : ℝ} (ht : 0 < t) :
    ((t + quarticSignedPoleCanonicalPhysicalHalfWidth t) - t) / (t/16)
      =
    quarticSignedPoleCanonicalLocalRadius := by
  unfold quarticSignedPoleCanonicalPhysicalHalfWidth
  field_simp [show t/16 ≠ 0 by positivity]
  ring

theorem quarticSignedPoleCanonicalLeft_normalized
    {t : ℝ} (ht : 0 < t) :
    ((t - quarticSignedPoleCanonicalPhysicalHalfWidth t) - t) / (t/16)
      =
    - quarticSignedPoleCanonicalLocalRadius := by
  unfold quarticSignedPoleCanonicalPhysicalHalfWidth
  field_simp [show t/16 ≠ 0 by positivity]
  ring

def QuarticFourSignedPolePair.normalizedOrdinateCosine
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (q : ℝ) : ℝ :=
  compactCosineTransform
    (quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t) q

def QuarticFourSignedPolePair.normalizedOrdinateCosineD1
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (q : ℝ) : ℝ :=
  compactCosineD1
    (quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t) q

def QuarticFourSignedPolePair.normalizedCenteredDiscrepancy
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (q : ℝ) : ℝ :=
  centeredZetaMuDiscrepancy t (t + (t/16)*q)

theorem QuarticFourSignedPolePair.signedOrdinateTest_normalized
    {t q : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.signedOrdinateTest (t + (t/16)*q)
      =
    (1/(t/16)^2) * W.normalizedOrdinateCosine q := by
  rw [W.signedOrdinateTest_eq_combinedCosine]
  unfold QuarticFourSignedPolePair.normalizedOrdinateCosine
  field_simp [show t/16 ≠ 0 by positivity]
  congr 2
  field_simp [show t/16 ≠ 0 by positivity]
  ring

theorem QuarticFourSignedPolePair.signedOrdinateTestDeriv_normalized
    {t q : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.signedOrdinateTestDeriv (t + (t/16)*q)
      =
    (1/(t/16)^3) * W.normalizedOrdinateCosineD1 q := by
  rw [W.signedOrdinateTestDeriv_eq_combinedD1 ht]
  unfold QuarticFourSignedPolePair.normalizedOrdinateCosineD1
  field_simp [show t/16 ≠ 0 by positivity]
  congr 2
  field_simp [show t/16 ≠ 0 by positivity]
  ring

theorem QuarticFourSignedPolePair.canonicalLocalRightBoundary_normalized
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.canonicalLocalRightBoundary
      =
    (1/(t/16)^2)
      *
    (
      W.normalizedOrdinateCosine
        quarticSignedPoleCanonicalLocalRadius
      *
      W.normalizedCenteredDiscrepancy
        quarticSignedPoleCanonicalLocalRadius
    ) := by
  unfold QuarticFourSignedPolePair.canonicalLocalRightBoundary
    QuarticFourSignedPolePair.normalizedCenteredDiscrepancy
  dsimp
  rw [W.signedOrdinateTest_normalized ht]
  ring

theorem QuarticFourSignedPolePair.canonicalLocalLeftBoundary_normalized
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.canonicalLocalLeftBoundary
      =
    (1/(t/16)^2)
      *
    (
      W.normalizedOrdinateCosine
        (-quarticSignedPoleCanonicalLocalRadius)
      *
      centeredZetaMuDiscrepancy
        t
        (t - quarticSignedPoleCanonicalPhysicalHalfWidth t)
    ) := by
  unfold QuarticFourSignedPolePair.canonicalLocalLeftBoundary
  dsimp
  have hx :
      t - quarticSignedPoleCanonicalPhysicalHalfWidth t
        =
      t + (t/16) * (-quarticSignedPoleCanonicalLocalRadius) := by
    unfold quarticSignedPoleCanonicalPhysicalHalfWidth
    ring
  rw [hx, W.signedOrdinateTest_normalized ht]
  ring

/--
The exact scale-normalized terminal compensation coordinate.

Multiplying the far completed compensation by r^2 removes the unavoidable
physical r^-2 scaling of a generic centered N-mu correlation.  The final
quartic target comparison therefore requires this normalized scalar to be
O(r^-4), with sign/constant strong enough to preserve the strict margin.
-/
def QuarticFourSignedPolePair.normalizedCanonicalFarCompletedCompensation
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  (t/16)^2 * W.canonicalFarCompletedCompensation

theorem QuarticFourSignedPolePair.canonicalFarCompletedCompensation_eq_normalized
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.canonicalFarCompletedCompensation
      =
    (1/(t/16)^2)
      * W.normalizedCanonicalFarCompletedCompensation := by
  unfold QuarticFourSignedPolePair.normalizedCanonicalFarCompletedCompensation
  field_simp [show t/16 ≠ 0 by positivity]
  ring

def QuarticFourSignedPolePair.CanonicalFarQuarticScaleBound
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (B : ℝ) : Prop :=
  |W.normalizedCanonicalFarCompletedCompensation|
    <= B / (t/16)^4

theorem QuarticFourSignedPolePair.canonicalFarCompletedCompensation_abs_le_of_quarticScale
    {t B : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hB : W.CanonicalFarQuarticScaleBound B) :
    |W.canonicalFarCompletedCompensation|
      <= B / (t/16)^6 := by
  rw [W.canonicalFarCompletedCompensation_eq_normalized ht,
      abs_mul, abs_of_nonneg (by positivity : 0 <= 1/(t/16)^2)]
  unfold QuarticFourSignedPolePair.CanonicalFarQuarticScaleBound at hB
  have hfac : 0 <= 1/(t/16)^2 := by positivity
  calc
    (1/(t/16)^2) *
        |W.normalizedCanonicalFarCompletedCompensation|
      <=
    (1/(t/16)^2) * (B/(t/16)^4) :=
      mul_le_mul_of_nonneg_left hB hfac
    _ = B/(t/16)^6 := by
      field_simp [show t/16 ≠ 0 by positivity]
      ring



/-!
## One-inequality terminal compensation compiler

The selected-M6 terminal budget already has the form

  local deterministic budget + literalFarExactAt.

Since the exact finite source is

  literalLocalExactAt + literalFarExactAt,

the far term cancels algebraically and yields a theorem-bearing upper bound for
the exact local pair source alone.  No new local analysis is required.

We then compare the global completed residual with one half of that finite local
pair source.  The difference is the exact compensated far remainder at the
same cut.  Multiplying by r^6 puts both sides on the quartic target scale.

The resulting normalized compensation cut is the single Clay-facing
high-ordinate inequality: once it holds at one cut beyond the canonical local
radius, the existing source estimates compile directly to strict G3.
-/

def QuarticFourSignedPolePair.postSixthTerminalLocalM6Budget
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (EV : ℝ) : ℝ :=
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
  (((3/20 : ℝ) * Real.pi^6)
      * quarticSignedPoleLocalSixthPhaseEnvelope t eta
      / (720 * (t/16)^8))
    * NZ
    +
  (((Real.pi+1)^2 * W.fourthLipschitz)
      * quarticSignedPoleLocalEighthPhysicalEnvelope t eta
      / (t/16)^10)
    * NZ

theorem QuarticFourSignedPolePair.postSixthTerminalM6BudgetAt_eq_local_add_far
    {t EV : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.postSixthTerminalM6BudgetAt EV n
      =
    W.postSixthTerminalLocalM6Budget EV
      + W.literalFarExactAt
          quarticSignedPoleCanonicalLocalRadius n := by
  unfold QuarticFourSignedPolePair.postSixthTerminalM6BudgetAt
    QuarticFourSignedPolePair.postSixthTerminalLocalM6Budget
  dsimp
  ring

theorem QuarticFourSignedPolePair.literalLocalExactAt_le_postSixthTerminalLocalM6Budget
    {t EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hM6lo :
      -(3/20 : ℝ) * Real.pi^6 <= W.signedProfileMomentSix)
    (hM6neg : W.signedProfileMomentSix < 0)
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
    W.literalLocalExactAt
        quarticSignedPoleCanonicalLocalRadius n
      <=
    W.postSixthTerminalLocalM6Budget EV := by
  have hsource :=
    W.literalOffOrdExactAt_le_postSixthTerminalM6BudgetAt
      ht hM6lo hM6neg n hn hV
  rw [W.literalOffOrdExactAt_eq_local_add_far
      (eta:=quarticSignedPoleCanonicalLocalRadius)] at hsource
  rw [W.postSixthTerminalM6BudgetAt_eq_local_add_far] at hsource
  linarith

def QuarticFourSignedPolePair.finiteCutCompensatedFar
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (n : ℕ) : ℝ :=
  W.completedSignedResidual
    - (1/2 : ℝ) *
      W.literalLocalExactAt
        quarticSignedPoleCanonicalLocalRadius n

def QuarticFourSignedPolePair.normalizedFiniteCutCompensatedFar
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (n : ℕ) : ℝ :=
  (t/16)^2 * W.finiteCutCompensatedFar n

theorem QuarticFourSignedPolePair.completedSignedResidual_eq_local_half_add_finiteCutFar
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.completedSignedResidual
      =
    (1/2 : ℝ) *
      W.literalLocalExactAt
        quarticSignedPoleCanonicalLocalRadius n
      + W.finiteCutCompensatedFar n := by
  unfold QuarticFourSignedPolePair.finiteCutCompensatedFar
  ring

theorem QuarticFourSignedPolePair.finiteCutCompensatedFar_eq_normalized
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.finiteCutCompensatedFar n
      =
    (1/(t/16)^2) *
      W.normalizedFiniteCutCompensatedFar n := by
  unfold QuarticFourSignedPolePair.normalizedFiniteCutCompensatedFar
  field_simp [show t/16 ≠ 0 by positivity]
  ring

def QuarticFourSignedPolePair.postSixthTerminalResidualMargin
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV : ℝ) : ℝ :=
  2 * W.combinedZeroHeightDefect rho
    - (1/2 : ℝ) * W.postSixthTerminalLocalM6Budget EV

def QuarticFourSignedPolePair.PostSixthNormalizedCompensationCut
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV : ℝ) : Prop :=
  ∃ n : ℕ,
    quarticSignedPoleLocalHalfWidth
        t quarticSignedPoleCanonicalLocalRadius
      < (n : ℝ)
    ∧
    (t/16)^4
        * |W.normalizedFiniteCutCompensatedFar n|
      <
    (t/16)^6
        * W.postSixthTerminalResidualMargin rho EV

theorem QuarticFourSignedPolePair.finiteCutCompensatedFar_lt_margin_of_normalizedCut
    {t EV : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    {n : ℕ}
    (hcut :
      (t/16)^4
          * |W.normalizedFiniteCutCompensatedFar n|
        <
      (t/16)^6
          * W.postSixthTerminalResidualMargin rho EV) :
    W.finiteCutCompensatedFar n
      <
    W.postSixthTerminalResidualMargin rho EV := by
  have hr : 0 < t/16 := by positivity
  have hr4 : 0 < (t/16)^4 := by positivity
  have hr6 : 0 < (t/16)^6 := by positivity
  have hnormNonneg :
      0 <= |W.normalizedFiniteCutCompensatedFar n| :=
    abs_nonneg _
  have hmarginPos :
      0 < W.postSixthTerminalResidualMargin rho EV := by
    by_contra hnot
    have hmarginNonpos :
        W.postSixthTerminalResidualMargin rho EV <= 0 :=
      le_of_not_gt hnot
    have hright :
        (t/16)^6
            * W.postSixthTerminalResidualMargin rho EV <= 0 :=
      mul_nonpos_of_nonneg_of_nonpos hr6.le hmarginNonpos
    have hleft :
        0 <=
        (t/16)^4
            * |W.normalizedFiniteCutCompensatedFar n| :=
      mul_nonneg hr4.le hnormNonneg
    linarith
  have habsScaled :
      |W.normalizedFiniteCutCompensatedFar n|
        <
      (t/16)^2
        * W.postSixthTerminalResidualMargin rho EV := by
    have hdiv :=
      (lt_div_iff₀ hr4).2 hcut
    convert hdiv using 1
    field_simp [hr.ne']
    ring
  have hnormLe :
      W.normalizedFiniteCutCompensatedFar n
        <
      (t/16)^2
        * W.postSixthTerminalResidualMargin rho EV :=
    (le_abs_self _).trans_lt habsScaled
  rw [W.finiteCutCompensatedFar_eq_normalized ht n]
  have hfac : 0 < 1/(t/16)^2 := by positivity
  have hscaled :=
    mul_lt_mul_of_pos_left hnormLe hfac
  calc
    (1/(t/16)^2)
        * W.normalizedFiniteCutCompensatedFar n
      <
    (1/(t/16)^2)
        * ((t/16)^2
          * W.postSixthTerminalResidualMargin rho EV) := hscaled
    _ = W.postSixthTerminalResidualMargin rho EV := by
      field_simp [hr.ne']

theorem QuarticFourSignedPolePair.completedSignedResidual_lt_target_of_normalizedCompensationCut
    {t EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hM6lo :
      -(3/20 : ℝ) * Real.pi^6 <= W.signedProfileMomentSix)
    (hM6neg : W.signedProfileMomentSix < 0)
    (hV :
      |quarticSignedPoleRvMVerticalFourthDiscrepancy
        t
        (quarticSignedPoleLocalHalfWidth
          t quarticSignedPoleCanonicalLocalRadius)|
        <= EV)
    (hC : W.PostSixthNormalizedCompensationCut rho EV) :
    W.completedSignedResidual
      < 2 * W.combinedZeroHeightDefect rho := by
  rcases hC with ⟨n,hn,hcut⟩
  have hlocal :=
    W.literalLocalExactAt_le_postSixthTerminalLocalM6Budget
      ht hM6lo hM6neg n hn hV
  have hfar :=
    W.finiteCutCompensatedFar_lt_margin_of_normalizedCut
      (by linarith : 0 < t) hcut
  rw [W.completedSignedResidual_eq_local_half_add_finiteCutFar n]
  unfold QuarticFourSignedPolePair.postSixthTerminalResidualMargin at hfar
  nlinarith

theorem QuarticFourSignedPolePair.postSixthNormalizedCompensationCut_compiles_G3
    {t EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hM6lo :
      -(3/20 : ℝ) * Real.pi^6 <= W.signedProfileMomentSix)
    (hM6neg : W.signedProfileMomentSix < 0)
    (hV :
      |quarticSignedPoleRvMVerticalFourthDiscrepancy
        t
        (quarticSignedPoleLocalHalfWidth
          t quarticSignedPoleCanonicalLocalRadius)|
        <= EV)
    (hC : W.PostSixthNormalizedCompensationCut rho EV) :
    W.completedSignedResidual
      < 2 * W.combinedZeroHeightDefect rho :=
  W.completedSignedResidual_lt_target_of_normalizedCompensationCut
    ht hM6lo hM6neg hV hC



/-!
## Literal normalized-cut expansion and terminal contradiction

The finite-cut compensated far remainder has no hidden semantic content:

  F_n
    = 1/2 * (global exact pair source
              - finite exact local pair source
              - full Gamma/mu ordinate integral).

This is exactly the manuscript-style compensated high-ordinate carrier.
The final theorem below sends the one normalized compensation cut directly
through the existing completed-residual G3 theorem to contradiction.
-/

theorem QuarticFourSignedPolePair.finiteCutCompensatedFar_eq_pairTail_sub_mu
    {t : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.finiteCutCompensatedFar n
      =
    (1/2 : ℝ)
      *
    (
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        W.signedLiteralPairSourceTerm sigma)
      -
      W.literalLocalExactAt
        quarticSignedPoleCanonicalLocalRadius n
      -
      ∫ tau : ℝ,
        W.signedOrdinateTest tau * Zeta23.mu tau
    ) := by
  unfold QuarticFourSignedPolePair.finiteCutCompensatedFar
  rw [W.completedSignedResidual_eq_jointPairSource ht]
  ring

theorem QuarticFourSignedPolePair.normalizedFiniteCutCompensatedFar_eq_pairTail_sub_mu
    {t : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.normalizedFiniteCutCompensatedFar n
      =
    ((t/16)^2 / 2)
      *
    (
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        W.signedLiteralPairSourceTerm sigma)
      -
      W.literalLocalExactAt
        quarticSignedPoleCanonicalLocalRadius n
      -
      ∫ tau : ℝ,
        W.signedOrdinateTest tau * Zeta23.mu tau
    ) := by
  unfold QuarticFourSignedPolePair.normalizedFiniteCutCompensatedFar
  rw [W.finiteCutCompensatedFar_eq_pairTail_sub_mu ht n]
  ring

def QuarticFourSignedPolePair.PostSixthLiteralCompensationCut
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV : ℝ) : Prop :=
  ∃ n : ℕ,
    quarticSignedPoleLocalHalfWidth
        t quarticSignedPoleCanonicalLocalRadius
      < (n : ℝ)
    ∧
    ((t/16)^6 / 2)
      *
    |
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        W.signedLiteralPairSourceTerm sigma)
      -
      W.literalLocalExactAt
        quarticSignedPoleCanonicalLocalRadius n
      -
      ∫ tau : ℝ,
        W.signedOrdinateTest tau * Zeta23.mu tau
    |
      <
    (t/16)^6
      * W.postSixthTerminalResidualMargin rho EV

theorem QuarticFourSignedPolePair.postSixthLiteralCompensationCut_iff_normalized
    {t EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.PostSixthLiteralCompensationCut rho EV
      ↔
    W.PostSixthNormalizedCompensationCut rho EV := by
  constructor
  · rintro ⟨n,hn,hcut⟩
    refine ⟨n,hn,?_⟩
    rw [W.normalizedFiniteCutCompensatedFar_eq_pairTail_sub_mu ht n]
    rw [abs_mul]
    have hr2non :
        0 <= (t/16)^2 / 2 := by positivity
    rw [abs_of_nonneg hr2non]
    convert hcut using 1
    · ring
    · rfl
  · rintro ⟨n,hn,hcut⟩
    refine ⟨n,hn,?_⟩
    rw [W.normalizedFiniteCutCompensatedFar_eq_pairTail_sub_mu ht n] at hcut
    rw [abs_mul] at hcut
    have hr2non :
        0 <= (t/16)^2 / 2 := by positivity
    rw [abs_of_nonneg hr2non] at hcut
    convert hcut using 1
    · ring
    · rfl

theorem QuarticFourSignedPolePair.completedSignedResidual_lt_target_of_literalCompensationCut
    {t EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hM6lo :
      -(3/20 : ℝ) * Real.pi^6 <= W.signedProfileMomentSix)
    (hM6neg : W.signedProfileMomentSix < 0)
    (hV :
      |quarticSignedPoleRvMVerticalFourthDiscrepancy
        t
        (quarticSignedPoleLocalHalfWidth
          t quarticSignedPoleCanonicalLocalRadius)|
        <= EV)
    (hC : W.PostSixthLiteralCompensationCut rho EV) :
    W.completedSignedResidual
      < 2 * W.combinedZeroHeightDefect rho := by
  apply W.completedSignedResidual_lt_target_of_normalizedCompensationCut
    ht hM6lo hM6neg hV
  exact
    (W.postSixthLiteralCompensationCut_iff_normalized
      ht rho).mp hC

theorem QuarticFourSignedPolePair.false_of_postSixthLiteralCompensationCut
    {t EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.quantitativeTargetRadius)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0)
    (hM6lo :
      -(3/20 : ℝ) * Real.pi^6 <= W.signedProfileMomentSix)
    (hM6neg : W.signedProfileMomentSix < 0)
    (hV :
      |quarticSignedPoleRvMVerticalFourthDiscrepancy
        t
        (quarticSignedPoleLocalHalfWidth
          t quarticSignedPoleCanonicalLocalRadius)|
        <= EV)
    (hC : W.PostSixthLiteralCompensationCut rho EV) :
    False := by
  have hstrict :=
    W.completedSignedResidual_lt_target_of_literalCompensationCut
      ht hM6lo hM6neg hV hC
  exact
    false_of_quarticFourSignedPole_completedResidual_strict
      ht W hhigh him hoff hstrict



/-!
## Selected witness + target-band weld

The terminal-M6 witness is also admissible for the already-paid G1 quantitative
band.  The explicit K0 theorem is universal over every four-window witness at
t >= 200, so no second existential witness is needed.

Above the existing quantitative threshold, the very same witness carries:

* the target-strength floor;
* the terminal signed-sixth certificate;
* the full-strip quantitative target radius.
-/

theorem exists_quarticFourSignedPolePair_with_terminal_M6_and_band_of_threshold
    {t : ℝ}
    (ht200 : 200 <= t)
    (htQ : quarticSignedPoleQuantitativeThreshold < t) :
    ∃ W : QuarticFourSignedPolePair t,
      quarticSignedPoleStrengthFloor <= W.targetStrength
        ∧
      -(3/20 : ℝ) * Real.pi^6 <= W.signedProfileMomentSix
        ∧
      W.signedProfileMomentSix < 0
        ∧
      8/t < W.quantitativeTargetRadius := by
  obtain ⟨W,hSraw,hM6lo,hM6neg⟩ :=
    exists_quarticFourSignedPolePair_with_strength_floor_and_terminal_M6
      ht200
  have hS :
      quarticSignedPoleStrengthFloor <= W.targetStrength := by
    simpa [quarticSignedPoleStrengthFloor] using hSraw
  have hK :
      W.fourthLipschitz <= quarticSignedPoleExplicitK0 :=
    W.fourthLipschitz_le_explicitK0 ht200
  have hthreshold :
      4 * (quarticSignedPoleExplicitK0 + 1) / t
        < quarticSignedPoleStrengthFloor :=
    quarticSignedPole_scalar_threshold_of_gt htQ
  have hband :
      8/t < W.quantitativeTargetRadius :=
    quarticSignedPole_quantitativeBand_covers_strip
      (by
        have hqpos := quarticSignedPoleQuantitativeThreshold_pos
        linarith)
      W
      quarticSignedPoleStrengthFloor_pos
      quarticSignedPoleExplicitK0_nonneg
      hS hK hthreshold
  exact ⟨W,hS,hM6lo,hM6neg,hband⟩

theorem exists_quarticFourSignedPolePair_with_terminal_M6_and_band_above_PT
    {t : ℝ}
    (htPT : quarticPlattTrudgianCutoff < t) :
    ∃ W : QuarticFourSignedPolePair t,
      quarticSignedPoleStrengthFloor <= W.targetStrength
        ∧
      -(3/20 : ℝ) * Real.pi^6 <= W.signedProfileMomentSix
        ∧
      W.signedProfileMomentSix < 0
        ∧
      8/t < W.quantitativeTargetRadius := by
  have ht200 : 200 <= t := by
    have hPT := quarticPlattTrudgianCutoff_gt_twoHundred
    linarith
  have htQ : quarticSignedPoleQuantitativeThreshold < t :=
    lt_trans quarticSignedPoleThresholdBelowPlattTrudgian_proved htPT
  exact
    exists_quarticFourSignedPolePair_with_terminal_M6_and_band_of_threshold
      ht200 htQ

/-!
## One remaining high-ordinate predicate

The V4 discrepancy producer is witness-independent.  For a fixed producer
constant CV, the only witness-dependent high assertion left is that one
already-certified selected witness satisfies the literal compensated cut.

This predicate intentionally bundles the already-paid witness certificates so
that there is no hidden same-witness matching obligation.
-/

def quarticSignedPoleSelectedLiteralHighCut
    (CV t : ℝ) (rho : Zeros) : Prop :=
  ∃ W : QuarticFourSignedPolePair t,
    quarticSignedPoleStrengthFloor <= W.targetStrength
      ∧
    -(3/20 : ℝ) * Real.pi^6 <= W.signedProfileMomentSix
      ∧
    W.signedProfileMomentSix < 0
      ∧
    8/t < W.quantitativeTargetRadius
      ∧
    W.PostSixthLiteralCompensationCut rho
      (quarticSignedPoleCanonicalV4Error CV t)

/--
Global V4 producer + one literal compensation cut -> contradiction.

Everything except the selected literal high cut is supplied by existing
theorem-bearing infrastructure.  The lower-end condition is exactly the
threshold required by the arbitrary-endpoint V4 producer and is independent
of the selected witness.
-/
theorem exists_quarticSignedPoleV4Producer_compiles_selectedLiteralHighCut :
    ∃ CV TV : ℝ,
      0 <= CV
        ∧
      ∀ {t : ℝ},
        200 <= t ->
        max TV 4
            <=
          t - quarticSignedPoleLocalHalfWidth
                t quarticSignedPoleCanonicalLocalRadius ->
        ∀ {rho : Zeros},
          (rho : ℂ).im = t ->
          heightOf rho ≠ 0 ->
          quarticSignedPoleSelectedLiteralHighCut CV t rho ->
          False := by
  obtain ⟨CV,TV,hCV,hVprod⟩ :=
    exists_quarticSignedPoleRvMVerticalFourthDiscrepancy_bound
  refine ⟨CV,TV,hCV,?_⟩
  intro t ht hleft rho him hoff hcut
  rcases hcut with
    ⟨W,hS,hM6lo,hM6neg,hband,hcomp⟩
  let r :=
    quarticSignedPoleLocalHalfWidth
      t quarticSignedPoleCanonicalLocalRadius
  have hr : 0 < r := by
    dsimp [r,quarticSignedPoleLocalHalfWidth]
    positivity
  have hVraw :=
    hVprod t r hr (by simpa [r] using hleft)
  have hV :
      |quarticSignedPoleRvMVerticalFourthDiscrepancy t r|
        <= quarticSignedPoleCanonicalV4Error CV t := by
    simpa [quarticSignedPoleCanonicalV4Error,r] using hVraw
  exact
    W.false_of_postSixthLiteralCompensationCut
      ht hband him hoff hM6lo hM6neg
      (by simpa [r] using hV)
      hcomp



/-!
## Final fixed-high-threshold compiler

Absorb the V4 producer's lower-end threshold into one fixed global cutoff.
Because eta0 = 1/(pi+1) < 1,

  r = (t/16) eta0 < t/16,

so t-r > 15t/16.  Taking t above twice max(TV,4) is therefore more than
enough to satisfy the V4 producer's left-end condition.

The resulting theorem has exactly one substantive high-ordinate premise:
the selected literal compensation cut.
-/

theorem quarticSignedPoleCanonicalLocalRadius_lt_one :
    quarticSignedPoleCanonicalLocalRadius < 1 := by
  unfold quarticSignedPoleCanonicalLocalRadius
  have hp : 0 < Real.pi := Real.pi_pos
  have hden : 1 < Real.pi + 1 := by linarith
  rw [div_lt_one (by positivity : 0 < Real.pi + 1)]
  exact hden

theorem quarticSignedPoleLocalHalfWidth_lt_sixteenth
    {t : ℝ} (ht : 0 < t) :
    quarticSignedPoleLocalHalfWidth
        t quarticSignedPoleCanonicalLocalRadius
      < t/16 := by
  unfold quarticSignedPoleLocalHalfWidth
  have hr0 : 0 < t/16 := by positivity
  have heta :=
    quarticSignedPoleCanonicalLocalRadius_lt_one
  nlinarith

theorem exists_quarticSignedPoleFixedHigh_compiles_selectedLiteralHighCut :
    ∃ CV T : ℝ,
      0 <= CV
        ∧ quarticPlattTrudgianCutoff <= T
        ∧
      ∀ {t : ℝ},
        T < t ->
        ∀ {rho : Zeros},
          (rho : ℂ).im = t ->
          heightOf rho ≠ 0 ->
          quarticSignedPoleSelectedLiteralHighCut CV t rho ->
          False := by
  obtain ⟨CV,TV,hCV,hcompile⟩ :=
    exists_quarticSignedPoleV4Producer_compiles_selectedLiteralHighCut
  let M : ℝ := max TV 4
  let T : ℝ := max quarticPlattTrudgianCutoff (2*M + 1)
  refine ⟨CV,T,hCV,?_,?_⟩
  · dsimp [T]
    exact le_max_left _ _
  · intro t ht rho him hoff hcut
    have hPT : quarticPlattTrudgianCutoff < t := by
      have hle : quarticPlattTrudgianCutoff <= T := by
        dsimp [T]
        exact le_max_left _ _
      exact lt_of_le_of_lt hle ht
    have ht200 : 200 <= t := by
      have h200 := quarticPlattTrudgianCutoff_gt_twoHundred
      linarith
    have hM0 : 0 <= M := by
      dsimp [M]
      have : (0 : ℝ) <= 4 := by norm_num
      exact this.trans (le_max_right TV 4)
    have htM : 2*M + 1 < t := by
      have hle : 2*M + 1 <= T := by
        dsimp [T]
        exact le_max_right _ _
      exact lt_of_le_of_lt hle ht
    have ht0 : 0 < t := by linarith
    have hrlt :=
      quarticSignedPoleLocalHalfWidth_lt_sixteenth ht0
    have hhalf : M < t/2 := by
      nlinarith
    have hremain :
        M <=
          t - quarticSignedPoleLocalHalfWidth
                t quarticSignedPoleCanonicalLocalRadius := by
      have hrt :
          quarticSignedPoleLocalHalfWidth
              t quarticSignedPoleCanonicalLocalRadius
            < t/2 := by
        nlinarith
      linarith
    exact
      hcompile ht200
        (by simpa [M] using hremain)
        him hoff hcut



/-!
## Quartic-scale centered discrepancy coordinate

The remaining high-ordinate compensation problem is not a missing decay lemma.
At the canonical physical scaling x = t + r*q, r=t/16, the exact derivative
already contributes r^-3.  To compare the centered Abel correlation with the
quartic r^-6 target after dx = r dq, the discrepancy itself must supply four
additional inverse powers of r.

We expose that requirement as the dimensionless coordinate

  E4_W(q) = r^4 * E_t(t+r*q).

The pointwise identity below is exact:

  r^7 * centeredAbelIntegrand(t+r*q)
    = normalizedOrdinateCosineD1(q) * E4_W(q).

Thus the remaining Clay-facing high inequality is genuinely a cancellation /
sign estimate for this quartic-scale centered discrepancy (together with the
already-existing horizontal remainder), not another oscillatory tail problem.
-/

def QuarticFourSignedPolePair.quarticScaleCenteredDiscrepancy
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (q : ℝ) : ℝ :=
  (t/16)^4 * W.normalizedCenteredDiscrepancy q

theorem QuarticFourSignedPolePair.quarticScaleCenteredDiscrepancy_eq
    {t q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.quarticScaleCenteredDiscrepancy q
      =
    (t/16)^4
      * centeredZetaMuDiscrepancy
          t (t + (t/16)*q) := by
  rfl

theorem QuarticFourSignedPolePair.centeredAbelIntegrand_quarticScale_normalized
    {t q : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    (t/16)^7
      * W.centeredAbelIntegrand (t + (t/16)*q)
      =
    W.normalizedOrdinateCosineD1 q
      * W.quarticScaleCenteredDiscrepancy q := by
  unfold QuarticFourSignedPolePair.centeredAbelIntegrand
    QuarticFourSignedPolePair.quarticScaleCenteredDiscrepancy
    QuarticFourSignedPolePair.normalizedCenteredDiscrepancy
  rw [W.signedOrdinateTestDeriv_normalized ht]
  have hr : t/16 ≠ 0 := by positivity
  field_simp [hr]
  ring

def QuarticFourSignedPolePair.quarticScaleHorizontalRemainder
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  (t/16)^6 * W.signedHorizontalRemainder

def QuarticFourSignedPolePair.quarticScaleCompletedResidual
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  (t/16)^6 * W.completedSignedResidual

theorem QuarticFourSignedPolePair.quarticScaleCompletedResidual_eq
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.quarticScaleCompletedResidual
      =
    ((t/16)^6 / 2) * W.signedNMuPair
      + W.quarticScaleHorizontalRemainder := by
  unfold QuarticFourSignedPolePair.quarticScaleCompletedResidual
    QuarticFourSignedPolePair.quarticScaleHorizontalRemainder
    QuarticFourSignedPolePair.completedSignedResidual
  ring

def QuarticFourSignedPolePair.quarticScaleFiniteCutCompensatedFar
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (n : ℕ) : ℝ :=
  (t/16)^6 * W.finiteCutCompensatedFar n

theorem QuarticFourSignedPolePair.quarticScaleFiniteCutCompensatedFar_eq_normalized
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.quarticScaleFiniteCutCompensatedFar n
      =
    (t/16)^4 * W.normalizedFiniteCutCompensatedFar n := by
  unfold QuarticFourSignedPolePair.quarticScaleFiniteCutCompensatedFar
    QuarticFourSignedPolePair.normalizedFiniteCutCompensatedFar
  ring

theorem QuarticFourSignedPolePair.postSixthNormalizedCompensationCut_iff_quarticScale
    {t EV : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.PostSixthNormalizedCompensationCut rho EV
      ↔
    ∃ n : ℕ,
      quarticSignedPoleLocalHalfWidth
          t quarticSignedPoleCanonicalLocalRadius
        < (n : ℝ)
      ∧
      |W.quarticScaleFiniteCutCompensatedFar n|
        <
      (t/16)^6
        * W.postSixthTerminalResidualMargin rho EV := by
  constructor
  · rintro ⟨n,hn,hcut⟩
    refine ⟨n,hn,?_⟩
    rw [W.quarticScaleFiniteCutCompensatedFar_eq_normalized]
    rw [abs_mul]
    have hr4 : 0 <= (t/16)^4 := by positivity
    rw [abs_of_nonneg hr4]
    exact hcut
  · rintro ⟨n,hn,hcut⟩
    refine ⟨n,hn,?_⟩
    rw [W.quarticScaleFiniteCutCompensatedFar_eq_normalized] at hcut
    rw [abs_mul] at hcut
    have hr4 : 0 <= (t/16)^4 := by positivity
    rw [abs_of_nonneg hr4] at hcut
    exact hcut



theorem QuarticFourSignedPolePair.postSixthLiteralCompensationCut_iff_quarticScale
    {t EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.PostSixthLiteralCompensationCut rho EV
      ↔
    ∃ n : ℕ,
      quarticSignedPoleLocalHalfWidth
          t quarticSignedPoleCanonicalLocalRadius
        < (n : ℝ)
      ∧
      |W.quarticScaleFiniteCutCompensatedFar n|
        <
      (t/16)^6
        * W.postSixthTerminalResidualMargin rho EV := by
  rw [W.postSixthLiteralCompensationCut_iff_normalized ht rho]
  exact W.postSixthNormalizedCompensationCut_iff_quarticScale rho

def quarticSignedPoleSelectedQuarticScaleHighCut
    (CV t : ℝ) (rho : Zeros) : Prop :=
  ∃ W : QuarticFourSignedPolePair t,
    quarticSignedPoleStrengthFloor <= W.targetStrength
      ∧
    -(3/20 : ℝ) * Real.pi^6 <= W.signedProfileMomentSix
      ∧
    W.signedProfileMomentSix < 0
      ∧
    8/t < W.quantitativeTargetRadius
      ∧
    ∃ n : ℕ,
      quarticSignedPoleLocalHalfWidth
          t quarticSignedPoleCanonicalLocalRadius
        < (n : ℝ)
      ∧
      |W.quarticScaleFiniteCutCompensatedFar n|
        <
      (t/16)^6
        * W.postSixthTerminalResidualMargin rho
          (quarticSignedPoleCanonicalV4Error CV t)

theorem quarticSignedPoleSelectedLiteralHighCut_iff_quarticScale
    {CV t : ℝ}
    (ht : 200 <= t)
    (rho : Zeros) :
    quarticSignedPoleSelectedLiteralHighCut CV t rho
      ↔
    quarticSignedPoleSelectedQuarticScaleHighCut CV t rho := by
  constructor
  · rintro ⟨W,hS,hM6lo,hM6neg,hband,hcut⟩
    refine ⟨W,hS,hM6lo,hM6neg,hband,?_⟩
    exact
      (W.postSixthLiteralCompensationCut_iff_quarticScale
        ht rho).mp hcut
  · rintro ⟨W,hS,hM6lo,hM6neg,hband,hcut⟩
    refine ⟨W,hS,hM6lo,hM6neg,hband,?_⟩
    exact
      (W.postSixthLiteralCompensationCut_iff_quarticScale
        ht rho).mpr hcut

theorem exists_quarticSignedPoleFixedHigh_compiles_selectedQuarticScaleHighCut :
    ∃ CV T : ℝ,
      0 <= CV
        ∧ quarticPlattTrudgianCutoff <= T
        ∧
      ∀ {t : ℝ},
        T < t ->
        ∀ {rho : Zeros},
          (rho : ℂ).im = t ->
          heightOf rho ≠ 0 ->
          quarticSignedPoleSelectedQuarticScaleHighCut CV t rho ->
          False := by
  obtain ⟨CV,T,hCV,hPT,hcompile⟩ :=
    exists_quarticSignedPoleFixedHigh_compiles_selectedLiteralHighCut
  refine ⟨CV,T,hCV,hPT,?_⟩
  intro t ht rho him hoff hcut
  have ht200 : 200 <= t := by
    have hPTgt := quarticPlattTrudgianCutoff_gt_twoHundred
    linarith
  apply hcompile ht him hoff
  exact
    (quarticSignedPoleSelectedLiteralHighCut_iff_quarticScale
      ht200 rho).mpr hcut



/-!
## Odd pairing and cubic-leading derivative jet

The normalized cosine derivative is odd.  On the selected witness its first
nonzero Taylor coefficient is cubic, with the sign forced by

  M4(W) = -4 * targetStrength(W).

Hence

  C'_W(q) = -(2/3) * targetStrength(W) * q^3 + R5_W(q).

The sign here is important: C'_W(q) is negative for small positive q, in
agreement with the already-certified radial derivative theorem.

The remainder is controlled directly by Mathlib's unit-ball sine remainder
and the same selected absolute sixth moment already welded to G1.
-/

theorem real_sin_sub_cubic_abs_le_fifth
    {x : ℝ}
    (hx : |x| <= 1) :
    |Real.sin x - (x - x^3/6)|
      <= |x|^5 / 100 := by
  have h :=
    Complex.sin_bound (x := (x : ℂ)) (by simpa using hx)
  simpa [Real.norm_eq_abs] using h

theorem QuarticFourSignedPolePair.normalizedOrdinateCosineD1_odd
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (q : ℝ) :
    W.normalizedOrdinateCosineD1 (-q)
      = - W.normalizedOrdinateCosineD1 q := by
  unfold QuarticFourSignedPolePair.normalizedOrdinateCosineD1
  exact compactCosineD1_odd _ q

def QuarticFourSignedPolePair.normalizedOrdinateD1QuinticRemainder
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (q : ℝ) : ℝ :=
  W.normalizedOrdinateCosineD1 q
    + (2/3 : ℝ) * W.targetStrength * q^3

theorem QuarticFourSignedPolePair.normalizedOrdinateCosineD1_eq_cubic_add_remainder
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (q : ℝ) :
    W.normalizedOrdinateCosineD1 q
      =
    -(2/3 : ℝ) * W.targetStrength * q^3
      + W.normalizedOrdinateD1QuinticRemainder q := by
  unfold QuarticFourSignedPolePair.normalizedOrdinateD1QuinticRemainder
  ring

theorem QuarticFourSignedPolePair.normalizedOrdinateD1QuinticRemainder_odd
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (q : ℝ) :
    W.normalizedOrdinateD1QuinticRemainder (-q)
      =
    - W.normalizedOrdinateD1QuinticRemainder q := by
  unfold QuarticFourSignedPolePair.normalizedOrdinateD1QuinticRemainder
  rw [W.normalizedOrdinateCosineD1_odd]
  ring

theorem QuarticFourSignedPolePair.normalizedOrdinateD1QuinticRemainder_eq_integral
    {t q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.normalizedOrdinateD1QuinticRemainder q
      =
    ∫ u : ℝ,
      - quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t u
      *
      (Real.sin (q*u) - ((q*u) - (q*u)^3/6))
      * u := by
  let P :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  have hP : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hsin :
      Integrable (fun u : ℝ => -P u * Real.sin (q*u) * u) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hPc.neg.mul_right).mul_right)
  have h2 :
      Integrable (fun u : ℝ => P u * u^2) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) hPc.mul_right
  have h4 :
      Integrable (fun u : ℝ => P u * u^4) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) hPc.mul_right
  have hM2 :
      ∫ u : ℝ, P u * u^2 = 0 := by
    change profileSecondMoment P = 0
    exact quarticFourSignedPoleCombinedProfile_second_zero
      W.Rpos W.J2Half W.J2Two
  have hM4 :
      ∫ u : ℝ, P u * u^4 = -4 * W.targetStrength := by
    change profileFourthMoment P = -4 * W.targetStrength
    simpa [QuarticFourSignedPolePair.targetStrength] using
      quarticFourSignedPoleCombinedProfile_fourth
        (R:=W.R) (muHalf:=W.muHalf) (muTwo:=W.muTwo)
        (t:=t) W.Rpos
  unfold QuarticFourSignedPolePair.normalizedOrdinateD1QuinticRemainder
    QuarticFourSignedPolePair.normalizedOrdinateCosineD1
    compactCosineD1
  change
    (∫ u : ℝ, -P u * Real.sin (q*u) * u)
      + (2/3 : ℝ) * W.targetStrength * q^3
      =
    ∫ u : ℝ,
      -P u * (Real.sin (q*u) - ((q*u) - (q*u)^3/6)) * u
  have hpoly :
      (fun u : ℝ =>
        -P u * (Real.sin (q*u) - ((q*u) - (q*u)^3/6)) * u)
      =
      fun u =>
        (-P u * Real.sin (q*u) * u)
          + q * (P u * u^2)
          - (q^3/6) * (P u * u^4) := by
    funext u
    ring
  rw [hpoly]
  have hq2 := h2.const_mul q
  have hq4 := h4.const_mul (q^3/6)
  rw [integral_sub (hsin.add hq2) hq4,
      integral_add hsin hq2,
      integral_const_mul, integral_const_mul,
      hM2, hM4]
  ring

theorem QuarticFourSignedPolePair.normalizedOrdinateD1QuinticRemainder_abs_le
    {t q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hq : |q| <= quarticSignedPoleCanonicalLocalRadius) :
    |W.normalizedOrdinateD1QuinticRemainder q|
      <=
    (1/100 : ℝ) * |q|^5 * W.signedProfileAbsMomentSix := by
  let P :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  have hP : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hi :
      Integrable
        (fun u : ℝ =>
          -P u
            * (Real.sin (q*u) - ((q*u) - (q*u)^3/6))
            * u) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hPc.neg.mul_right).mul_right)
  have hmaj :
      Integrable
        (fun u : ℝ =>
          (1/100 : ℝ) * |q|^5 * (|P u| * |u|^6)) :=
    (compactProfile_absMoment_integrable hP hPc 6).const_mul
      ((1/100 : ℝ) * |q|^5)
  rw [W.normalizedOrdinateD1QuinticRemainder_eq_integral]
  calc
    |∫ u : ℝ,
      -P u
        * (Real.sin (q*u) - ((q*u) - (q*u)^3/6))
        * u|
      <=
    ∫ u : ℝ,
      |-P u
        * (Real.sin (q*u) - ((q*u) - (q*u)^3/6))
        * u| :=
      abs_integral_le_integral_abs
    _ <=
    ∫ u : ℝ,
      (1/100 : ℝ) * |q|^5 * (|P u| * |u|^6) := by
      apply integral_mono hi.abs hmaj
      intro u
      by_cases hzero : P u = 0
      · simp [hzero]
      · have hqu := W.abs_q_mul_u_le_one_of_local hq hzero
        have hs := real_sin_sub_cubic_abs_le_fifth hqu
        rw [abs_mul, abs_mul, abs_neg]
        have hqupow : |q*u|^5 = |q|^5 * |u|^5 := by
          rw [abs_mul, mul_pow]
        rw [hqupow] at hs
        have hP0 : 0 <= |P u| := abs_nonneg _
        have hu0 : 0 <= |u| := abs_nonneg _
        calc
          |P u|
              * |Real.sin (q*u) - ((q*u) - (q*u)^3/6)|
              * |u|
            <=
          |P u| * ((|q|^5 * |u|^5) / 100) * |u| := by
            gcongr
          _ =
          (1/100 : ℝ) * |q|^5 * (|P u| * |u|^6) := by
            ring
    _ =
    (1/100 : ℝ) * |q|^5 * compactProfileAbsMoment P 6 := by
      rw [integral_const_mul]
      rfl
    _ =
    (1/100 : ℝ) * |q|^5 * W.signedProfileAbsMomentSix := by
      rfl


/-!
## Antisymmetric quartic-scale centered discrepancy

Because C'_W is odd, the selected vertical correlation sees only the
antisymmetric component of the centered discrepancy.  For q >= 0 that
antisymmetric component is exactly one symmetric literal N-mu window.
-/

def QuarticFourSignedPolePair.quarticScaleAntisymmetricDiscrepancy
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (q : ℝ) : ℝ :=
  W.quarticScaleCenteredDiscrepancy q
    - W.quarticScaleCenteredDiscrepancy (-q)

theorem QuarticFourSignedPolePair.quarticScaleAntisymmetricDiscrepancy_eq_symmetricWindow
    {t q : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hq : 0 <= q) :
    W.quarticScaleAntisymmetricDiscrepancy q
      =
    (t/16)^4
      *
    zetaMuCumulativeDiscrepancy
      (t - (t/16)*q)
      (t + (t/16)*q) := by
  by_cases hq0 : q = 0
  · subst q
    simp [QuarticFourSignedPolePair.quarticScaleAntisymmetricDiscrepancy,
      QuarticFourSignedPolePair.quarticScaleCenteredDiscrepancy,
      QuarticFourSignedPolePair.normalizedCenteredDiscrepancy,
      centeredZetaMuDiscrepancy_self,
      zetaMuCumulativeDiscrepancy,
      zetaMuPrimitive_self]
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    have hr : 0 < t/16 := by positivity
    have hleft : t - (t/16)*q < t := by positivity
    have hright : t <= t + (t/16)*q := by positivity
    have hadd :=
      zetaMuCumulativeDiscrepancy_add
        (A:=t-(t/16)*q)
        (B:=t)
        (C:=t+(t/16)*q)
        (by linarith)
        hright
    unfold QuarticFourSignedPolePair.quarticScaleAntisymmetricDiscrepancy
      QuarticFourSignedPolePair.quarticScaleCenteredDiscrepancy
      QuarticFourSignedPolePair.normalizedCenteredDiscrepancy
    rw [centeredZetaMuDiscrepancy_of_le hright,
      centeredZetaMuDiscrepancy_of_lt hleft]
    rw [hadd]
    ring

theorem QuarticFourSignedPolePair.normalizedPairedIntegrand_eq_cubic_add_quintic
    {t q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.normalizedOrdinateCosineD1 q
      * W.quarticScaleAntisymmetricDiscrepancy q
      =
    (-(2/3 : ℝ) * W.targetStrength * q^3)
      * W.quarticScaleAntisymmetricDiscrepancy q
      +
    W.normalizedOrdinateD1QuinticRemainder q
      * W.quarticScaleAntisymmetricDiscrepancy q := by
  rw [W.normalizedOrdinateCosineD1_eq_cubic_add_remainder]
  ring



/-!
## The cubic paired discrepancy is exactly the centered V4 Abel coordinate

The symmetric discrepancy exposed above is not merely analogous to V4.
For a physical symmetric half-width h, the quartic Abel derivative can be
recentered from the left endpoint to t exactly:

  V4(t,h)
    = h^4 D(t-h,t+h)
      - ∫_{t-h}^{t+h} 4(x-t)^3 E_t(x) dx.

The constant left-anchor discrepancy disappears because the cubic derivative
has zero integral on the symmetric interval.  Thus the leading cubic part of
the selected C'_W correlation is literally a scalar multiple of the already
owned V4 coordinate plus one explicit symmetric boundary term.
-/

theorem zetaMuCumulativeDiscrepancy_leftAnchor_eq_const_add_centered
    {t h x : ℝ}
    (hh : 0 <= h)
    (hx : x ∈ Set.Icc (t-h) (t+h)) :
    zetaMuCumulativeDiscrepancy (t-h) x
      =
    zetaMuCumulativeDiscrepancy (t-h) t
      + centeredZetaMuDiscrepancy t x := by
  by_cases hxt : x <= t
  · exact
      zetaMuCumulativeDiscrepancy_left_eq_centered
        hx.1 hxt
  · have htx : t <= x := le_of_not_ge hxt
    have hAt : t-h <= t := by linarith
    have hadd :=
      zetaMuCumulativeDiscrepancy_add
        (A:=t-h) (B:=t) (C:=x) hAt htx
    rw [centeredZetaMuDiscrepancy_of_le htx]
    exact hadd

def quarticSignedPoleCenteredFourthAbelCorrelation
    (t h : ℝ) : ℝ :=
  ∫ x in (t-h)..(t+h),
    quarticSignedPoleVerticalFourthWeightDeriv t x
      * centeredZetaMuDiscrepancy t x

theorem quarticSignedPoleCenteredFourthAbelCorrelation_intervalIntegrable
    {t h : ℝ}
    (hh : 0 <= h) :
    IntervalIntegrable
      (fun x : ℝ =>
        quarticSignedPoleVerticalFourthWeightDeriv t x
          * centeredZetaMuDiscrepancy t x)
      volume (t-h) (t+h) := by
  have hAB : t-h <= t+h := by linarith
  have hder :=
    quarticSignedPoleVerticalFourthWeightDeriv_intervalIntegrable
      t (t-h) (t+h)
  have hN :
      IntervalIntegrable
        (fun x : ℝ =>
          quarticSignedPoleVerticalFourthWeightDeriv t x
            * (Ncount (t-h) x : ℝ))
        volume (t-h) (t+h) :=
    phi_mul_Ncount_intervalIntegrable hAB hder
  have hM :
      IntervalIntegrable
        (fun x : ℝ =>
          quarticSignedPoleVerticalFourthWeightDeriv t x
            * zetaMuPrimitive (t-h) x)
        volume (t-h) (t+h) :=
    phi_mul_zetaMuPrimitive_intervalIntegrable hder
  have hCum :
      IntervalIntegrable
        (fun x : ℝ =>
          quarticSignedPoleVerticalFourthWeightDeriv t x
            * zetaMuCumulativeDiscrepancy (t-h) x)
        volume (t-h) (t+h) := by
    unfold zetaMuCumulativeDiscrepancy
    simpa [mul_sub] using hN.sub hM
  have hConst :
      IntervalIntegrable
        (fun x : ℝ =>
          quarticSignedPoleVerticalFourthWeightDeriv t x
            * zetaMuCumulativeDiscrepancy (t-h) t)
        volume (t-h) (t+h) := by
    exact hder.mul_const _
  have hSub := hCum.sub hConst
  refine hSub.congr_ae ?_
  rw [Filter.EventuallyEq,
    MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  filter_upwards with x hx
  have hxI : x ∈ Set.Icc (t-h) (t+h) := by
    simpa [Set.uIoc_of_le hAB] using ⟨hx.1.le,hx.2⟩
  rw [zetaMuCumulativeDiscrepancy_leftAnchor_eq_const_add_centered
      hh hxI]
  ring

theorem quarticSignedPoleRvMVerticalFourthDiscrepancy_eq_centeredAbel
    {t h : ℝ}
    (hh : 0 <= h) :
    quarticSignedPoleRvMVerticalFourthDiscrepancy t h
      =
    h^4
      * zetaMuCumulativeDiscrepancy (t-h) (t+h)
      -
    quarticSignedPoleCenteredFourthAbelCorrelation t h := by
  have hAB : t-h <= t+h := by linarith
  have hraw :=
    quarticSignedPoleRvMVerticalFourthDiscrepancy_eq_abel
      (t:=t) (r:=h) hh
  have hder :=
    quarticSignedPoleVerticalFourthWeightDeriv_intervalIntegrable
      t (t-h) (t+h)
  have hcenter :=
    quarticSignedPoleCenteredFourthAbelCorrelation_intervalIntegrable
      (t:=t) hh
  have hconst :
      IntervalIntegrable
        (fun x : ℝ =>
          quarticSignedPoleVerticalFourthWeightDeriv t x
            * zetaMuCumulativeDiscrepancy (t-h) t)
        volume (t-h) (t+h) :=
    hder.mul_const _
  have hFTC :=
    intervalIntegral.integral_deriv_eq_sub'
      (fun x hx =>
        quarticSignedPoleVerticalFourthWeight_hasDerivAt t x)
      hder
  have hDerivZero :
      (∫ x in (t-h)..(t+h),
        quarticSignedPoleVerticalFourthWeightDeriv t x) = 0 := by
    rw [hFTC]
    unfold quarticSignedPoleVerticalFourthWeight
    ring
  have hConstZero :
      (∫ x in (t-h)..(t+h),
        quarticSignedPoleVerticalFourthWeightDeriv t x
          * zetaMuCumulativeDiscrepancy (t-h) t) = 0 := by
    rw [show
        (fun x : ℝ =>
          quarticSignedPoleVerticalFourthWeightDeriv t x
            * zetaMuCumulativeDiscrepancy (t-h) t)
        =
        fun x =>
          zetaMuCumulativeDiscrepancy (t-h) t
            * quarticSignedPoleVerticalFourthWeightDeriv t x by
      funext x
      ring]
    rw [intervalIntegral.integral_const_mul, hDerivZero, mul_zero]
  have hCum :
      IntervalIntegrable
        (fun x : ℝ =>
          quarticSignedPoleVerticalFourthWeightDeriv t x
            * zetaMuCumulativeDiscrepancy (t-h) x)
        volume (t-h) (t+h) := by
    have hN :
        IntervalIntegrable
          (fun x : ℝ =>
            quarticSignedPoleVerticalFourthWeightDeriv t x
              * (Ncount (t-h) x : ℝ))
          volume (t-h) (t+h) :=
      phi_mul_Ncount_intervalIntegrable hAB hder
    have hM :
        IntervalIntegrable
          (fun x : ℝ =>
            quarticSignedPoleVerticalFourthWeightDeriv t x
              * zetaMuPrimitive (t-h) x)
          volume (t-h) (t+h) :=
      phi_mul_zetaMuPrimitive_intervalIntegrable hder
    unfold zetaMuCumulativeDiscrepancy
    simpa [mul_sub] using hN.sub hM
  have hsplit :
      (∫ x in (t-h)..(t+h),
        quarticSignedPoleVerticalFourthWeightDeriv t x
          * zetaMuCumulativeDiscrepancy (t-h) x)
        =
      (∫ x in (t-h)..(t+h),
        quarticSignedPoleVerticalFourthWeightDeriv t x
          * zetaMuCumulativeDiscrepancy (t-h) t)
        +
      quarticSignedPoleCenteredFourthAbelCorrelation t h := by
    unfold quarticSignedPoleCenteredFourthAbelCorrelation
    rw [← intervalIntegral.integral_add hconst hcenter]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxI : x ∈ Set.Icc (t-h) (t+h) := by
      simpa [Set.uIcc_of_le hAB] using hx
    rw [zetaMuCumulativeDiscrepancy_leftAnchor_eq_const_add_centered
      hh hxI]
    ring
  rw [hsplit, hConstZero, zero_add] at hraw
  exact hraw

def QuarticFourSignedPolePair.canonicalCenteredFourthAbelCorrelation
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) : ℝ :=
  quarticSignedPoleCenteredFourthAbelCorrelation
    t (quarticSignedPoleCanonicalPhysicalHalfWidth t)

theorem QuarticFourSignedPolePair.canonicalCenteredFourthAbelCorrelation_eq_boundary_sub_V4
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.canonicalCenteredFourthAbelCorrelation
      =
    (quarticSignedPoleCanonicalPhysicalHalfWidth t)^4
      *
      zetaMuCumulativeDiscrepancy
        (t - quarticSignedPoleCanonicalPhysicalHalfWidth t)
        (t + quarticSignedPoleCanonicalPhysicalHalfWidth t)
      -
    quarticSignedPoleRvMVerticalFourthDiscrepancy
      t (quarticSignedPoleCanonicalPhysicalHalfWidth t) := by
  have hh :
      0 <= quarticSignedPoleCanonicalPhysicalHalfWidth t :=
    (quarticSignedPoleCanonicalPhysicalHalfWidth_pos ht).le
  have h :=
    quarticSignedPoleRvMVerticalFourthDiscrepancy_eq_centeredAbel
      (t:=t)
      (h:=quarticSignedPoleCanonicalPhysicalHalfWidth t)
      hh
  unfold QuarticFourSignedPolePair.canonicalCenteredFourthAbelCorrelation
  linarith

def QuarticFourSignedPolePair.cubicLeadingCanonicalCorrelation
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) : ℝ :=
  -(W.targetStrength / 6)
    * W.canonicalCenteredFourthAbelCorrelation

theorem QuarticFourSignedPolePair.cubicLeadingCanonicalCorrelation_eq_V4_boundary
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.cubicLeadingCanonicalCorrelation
      =
    -(W.targetStrength / 6)
      *
    (
      (quarticSignedPoleCanonicalPhysicalHalfWidth t)^4
        *
        zetaMuCumulativeDiscrepancy
          (t - quarticSignedPoleCanonicalPhysicalHalfWidth t)
          (t + quarticSignedPoleCanonicalPhysicalHalfWidth t)
      -
      quarticSignedPoleRvMVerticalFourthDiscrepancy
        t (quarticSignedPoleCanonicalPhysicalHalfWidth t)
    ) := by
  unfold QuarticFourSignedPolePair.cubicLeadingCanonicalCorrelation
  rw [W.canonicalCenteredFourthAbelCorrelation_eq_boundary_sub_V4 ht]



/-!
## Fail-fast separation: local cubic/V4 versus the genuinely open complement

Oddness is global, so it is useful to expose the exact paired Abel integrand at
a physical offset s.  For s >= 0,

  Psi'_t(t-s) = - Psi'_t(t+s)

and

  E_t(t+s) - E_t(t-s) = D(t-s,t+s).

Thus the paired centered-Abel integrand is exactly the derivative at the right
endpoint times one symmetric N-mu window discrepancy.

However, the cubic Taylor estimate proved above is only certified on the
canonical local normalized interval |q| <= eta0.  That is precisely the local
source already subtracted in finiteCutCompensatedFar.  The quartic-scale
completed residual therefore decomposes exactly into the already-paid local
source plus the still-open complementary finite-cut compensation.

This prevents the local cubic/V4 diagnostic from being mistaken for a payment
of the remaining high cut.
-/

theorem QuarticFourSignedPolePair.signedOrdinateTestDeriv_reflect
    {t s : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.signedOrdinateTestDeriv (t-s)
      = - W.signedOrdinateTestDeriv (t+s) := by
  rw [W.signedOrdinateTestDeriv_eq_combinedD1 ht,
      W.signedOrdinateTestDeriv_eq_combinedD1 ht]
  dsimp
  have hr : t/16 ≠ 0 := by positivity
  have hleft :
      ((t-s)-t)/(t/16) = -(s/(t/16)) := by
    field_simp [hr]
    ring
  have hright :
      ((t+s)-t)/(t/16) = s/(t/16) := by
    field_simp [hr]
    ring
  rw [hleft, hright, compactCosineD1_odd]
  ring

theorem centeredZetaMuDiscrepancy_sub_reflect_eq_symmetricWindow
    {t s : ℝ}
    (hs : 0 <= s) :
    centeredZetaMuDiscrepancy t (t+s)
      - centeredZetaMuDiscrepancy t (t-s)
      =
    zetaMuCumulativeDiscrepancy (t-s) (t+s) := by
  by_cases hs0 : s = 0
  · subst s
    simp [centeredZetaMuDiscrepancy_self,
      zetaMuCumulativeDiscrepancy,
      zetaMuPrimitive_self]
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    have hleft : t-s < t := by linarith
    have hright : t <= t+s := by linarith
    have hadd :=
      zetaMuCumulativeDiscrepancy_add
        (A:=t-s) (B:=t) (C:=t+s)
        (by linarith) hright
    rw [centeredZetaMuDiscrepancy_of_le hright,
      centeredZetaMuDiscrepancy_of_lt hleft]
    rw [hadd]
    ring

def QuarticFourSignedPolePair.pairedCenteredAbelOffset
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (s : ℝ) : ℝ :=
  W.signedOrdinateTestDeriv (t+s)
    *
  (
    centeredZetaMuDiscrepancy t (t+s)
      - centeredZetaMuDiscrepancy t (t-s)
  )

theorem QuarticFourSignedPolePair.pairedCenteredAbelOffset_eq_symmetricWindow
    {t s : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hs : 0 <= s) :
    W.pairedCenteredAbelOffset s
      =
    W.signedOrdinateTestDeriv (t+s)
      * zetaMuCumulativeDiscrepancy (t-s) (t+s) := by
  unfold QuarticFourSignedPolePair.pairedCenteredAbelOffset
  rw [centeredZetaMuDiscrepancy_sub_reflect_eq_symmetricWindow hs]

theorem QuarticFourSignedPolePair.pairedCenteredAbelOffset_quarticScale
    {t q : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hq : 0 <= q) :
    (t/16)^7
      * W.pairedCenteredAbelOffset ((t/16)*q)
      =
    W.normalizedOrdinateCosineD1 q
      * W.quarticScaleAntisymmetricDiscrepancy q := by
  unfold QuarticFourSignedPolePair.pairedCenteredAbelOffset
  have hr : 0 < t/16 := by positivity
  have hqphys : 0 <= (t/16)*q := mul_nonneg hr.le hq
  rw [W.signedOrdinateTestDeriv_normalized ht]
  have hplus :
      t + (t/16)*q = t + (t/16)*q := rfl
  have hminus :
      t - (t/16)*q = t + (t/16)*(-q) := by ring
  unfold QuarticFourSignedPolePair.quarticScaleAntisymmetricDiscrepancy
    QuarticFourSignedPolePair.quarticScaleCenteredDiscrepancy
    QuarticFourSignedPolePair.normalizedCenteredDiscrepancy
  rw [hminus]
  have hr0 : t/16 ≠ 0 := by positivity
  field_simp [hr0]
  ring

theorem QuarticFourSignedPolePair.quarticScaleCompletedResidual_eq_localExact_add_finiteCutComplement
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.quarticScaleCompletedResidual
      =
    ((t/16)^6 / 2)
      * W.literalLocalExactAt
          quarticSignedPoleCanonicalLocalRadius n
      +
    W.quarticScaleFiniteCutCompensatedFar n := by
  unfold QuarticFourSignedPolePair.quarticScaleCompletedResidual
    QuarticFourSignedPolePair.quarticScaleFiniteCutCompensatedFar
  rw [W.completedSignedResidual_eq_local_half_add_finiteCutFar n]
  ring

/--
Audit theorem: every local cubic/V4 sharpening can only improve the first term
in the exact decomposition above.  The selected quartic-scale high cut still
requires an independent estimate of the complementary finite-cut compensation.
-/
theorem QuarticFourSignedPolePair.quarticScaleFiniteCutComplement_eq_completed_sub_local
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.quarticScaleFiniteCutCompensatedFar n
      =
    W.quarticScaleCompletedResidual
      -
    ((t/16)^6 / 2)
      * W.literalLocalExactAt
          quarticSignedPoleCanonicalLocalRadius n := by
  have h :=
    W.quarticScaleCompletedResidual_eq_localExact_add_finiteCutComplement n
  linarith



/-!
## Global symmetric Abel pairing and canonical local/high split

The preferred symmetric Abel exhaustion can be reflected exactly onto positive
physical offsets.  This exposes the global analytic object as

  ∫_0^n Psi'_t(t+s) D(t-s,t+s) ds.

Splitting at the canonical physical half-width h0 therefore separates:

* the local paired correlation, where the cubic + quintic witness jet is valid
  and the cubic term is the V4 boundary-minus-moment coordinate above;
* the outer paired correlation, where the exact C'_W kernel must be retained.

This is the genuine high-ordinate remainder after the local quartic programme.
-/

def QuarticFourSignedPolePair.pairedCenteredAbelPartial
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) : ℝ :=
  ∫ s in (0:ℝ)..(n:ℝ), W.pairedCenteredAbelOffset s

theorem QuarticFourSignedPolePair.combinedCenteredAbelPartial_eq_paired
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.combinedCenteredAbelPartial n
      =
    W.pairedCenteredAbelPartial n := by
  let f : ℝ -> ℝ := W.centeredAbelIntegrand
  have hleft :
      IntervalIntegrable f volume (t-(n:ℝ)) t :=
    W.centeredAbelIntegrand_intervalIntegrable
      ht (A:=t-(n:ℝ)) (B:=t)
  have hright :
      IntervalIntegrable f volume t (t+(n:ℝ)) :=
    W.centeredAbelIntegrand_intervalIntegrable
      ht (A:=t) (B:=t+(n:ℝ))
  have hleft' :
      IntervalIntegrable (fun s : ℝ => f (t-s))
        volume 0 (n:ℝ) := by
    simpa using hleft.comp_sub_left t
  have hright' :
      IntervalIntegrable (fun s : ℝ => f (t+s))
        volume 0 (n:ℝ) := by
    simpa using hright.comp_add_left t
  have hL :
      (∫ x in (t-(n:ℝ))..t, f x)
        =
      ∫ s in (0:ℝ)..(n:ℝ), f (t-s) := by
    symm
    simpa using
      (intervalIntegral.integral_comp_sub_mul
        (f:=f) (a:=(0:ℝ)) (b:=(n:ℝ))
        (c:=(1:ℝ)) (by norm_num) t)
  have hR :
      (∫ x in t..(t+(n:ℝ)), f x)
        =
      ∫ s in (0:ℝ)..(n:ℝ), f (t+s) := by
    symm
    simpa using
      (intervalIntegral.integral_comp_add_left
        (f:=f) (a:=(0:ℝ)) (b:=(n:ℝ)) t)
  unfold QuarticFourSignedPolePair.combinedCenteredAbelPartial
    QuarticFourSignedPolePair.leftCenteredAbelPartial
    QuarticFourSignedPolePair.rightCenteredAbelPartial
    QuarticFourSignedPolePair.pairedCenteredAbelPartial
  rw [hL,hR, ← intervalIntegral.integral_add hleft' hright']
  apply intervalIntegral.integral_congr
  intro s hs
  unfold f QuarticFourSignedPolePair.centeredAbelIntegrand
    QuarticFourSignedPolePair.pairedCenteredAbelOffset
  rw [W.signedOrdinateTestDeriv_reflect ht]
  ring

def QuarticFourSignedPolePair.canonicalOuterPairedAbelAt
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) : ℝ :=
  ∫ s in quarticSignedPoleCanonicalPhysicalHalfWidth t..(n:ℝ),
    W.pairedCenteredAbelOffset s

def QuarticFourSignedPolePair.canonicalLocalPairedAbel
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) : ℝ :=
  ∫ s in (0:ℝ)..quarticSignedPoleCanonicalPhysicalHalfWidth t,
    W.pairedCenteredAbelOffset s

theorem QuarticFourSignedPolePair.pairedCenteredAbelPartial_eq_local_add_outer
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hn :
      quarticSignedPoleCanonicalPhysicalHalfWidth t
        <= (n : ℝ)) :
    W.pairedCenteredAbelPartial n
      =
    W.canonicalLocalPairedAbel
      + W.canonicalOuterPairedAbelAt n := by
  have hpair :
      IntervalIntegrable W.pairedCenteredAbelOffset
        volume 0 (n:ℝ) := by
    rw [← W.combinedCenteredAbelPartial_eq_paired ht n]
    -- Integrability is inherited from the reflected left/right centered-Abel
    -- pieces used in the preceding theorem.
    let f : ℝ -> ℝ := W.centeredAbelIntegrand
    have hleft :
        IntervalIntegrable (fun s : ℝ => f (t-s))
          volume 0 (n:ℝ) := by
      have h :=
        W.centeredAbelIntegrand_intervalIntegrable
          ht (A:=t-(n:ℝ)) (B:=t)
      simpa using h.comp_sub_left t
    have hright :
        IntervalIntegrable (fun s : ℝ => f (t+s))
          volume 0 (n:ℝ) := by
      have h :=
        W.centeredAbelIntegrand_intervalIntegrable
          ht (A:=t) (B:=t+(n:ℝ))
      simpa using h.comp_add_left t
    have hadd := hleft.add hright
    refine hadd.congr_ae ?_
    rw [Filter.EventuallyEq,
      MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with s hs
    unfold f QuarticFourSignedPolePair.centeredAbelIntegrand
      QuarticFourSignedPolePair.pairedCenteredAbelOffset
    rw [W.signedOrdinateTestDeriv_reflect ht]
    ring
  unfold QuarticFourSignedPolePair.pairedCenteredAbelPartial
    QuarticFourSignedPolePair.canonicalLocalPairedAbel
    QuarticFourSignedPolePair.canonicalOuterPairedAbelAt
  exact intervalIntegral.integral_add_adjacent_intervals
    hpair.mono_set
    hpair.mono_set



def QuarticFourSignedPolePair.canonicalOuterPairedHorizontalAt
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) : ℝ :=
  -(1/2 : ℝ) * W.canonicalOuterPairedAbelAt n
    + W.signedHorizontalRemainder

def QuarticFourSignedPolePair.canonicalLocalPairedContribution
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) : ℝ :=
  -(1/2 : ℝ) * W.canonicalLocalPairedAbel

theorem QuarticFourSignedPolePair.centeredCompletedResidualAt_eq_localPaired_add_outerHorizontal
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hn :
      quarticSignedPoleCanonicalPhysicalHalfWidth t
        <= (n : ℝ)) :
    W.centeredCompletedResidualAt n
      =
    W.canonicalLocalPairedContribution
      + W.canonicalOuterPairedHorizontalAt n := by
  unfold QuarticFourSignedPolePair.centeredCompletedResidualAt
    QuarticFourSignedPolePair.canonicalLocalPairedContribution
    QuarticFourSignedPolePair.canonicalOuterPairedHorizontalAt
  rw [W.combinedCenteredAbelPartial_eq_paired ht n,
      W.pairedCenteredAbelPartial_eq_local_add_outer ht n hn]
  ring

/--
The remaining paired high object after the local cubic/V4 sector is removed.
No estimate is asserted here.

A terminal proof through the paired-Abel lane must control this exact object,
not the already-paid local cubic correlation:

  -1/2 * outer paired symmetric N-mu correlation
    + signed horizontal remainder.
-/
def QuarticFourSignedPolePair.PairedOuterHorizontalHighCut
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (localAllowance : ℝ) : Prop :=
  ∃ eps : ℝ, 0 < eps ∧
    ∀ᶠ n : ℕ in Filter.atTop,
      W.canonicalOuterPairedHorizontalAt n
        <=
      2 * W.combinedZeroHeightDefect rho
        - localAllowance - eps


/-!
## Asymptotic outer-paired recut onto the manuscript far carrier

The finite outer paired presentation is useful for exposing the signed
symmetric-window correlation, but the Clay-facing asymptotic object should be
compared with the already-owned canonical far completed compensation rather
than treated as a second analytic invariant.

For one centered-Abel exhaustion E, define the limiting outer paired +
horizontal coordinate by removing the canonical local paired Abel integral
from the exhausted centered Abel correlation.  Existing Abel bookkeeping then
gives the exact same-object identity

  outerPairedHorizontalLimit
    = canonicalFarCompletedCompensation
      + 1/2 * (canonical left boundary + canonical right boundary).

Thus the only difference between the new outer-paired carrier and the
manuscript far carrier is an explicit canonical boundary coordinate.  No
estimate is asserted here.
-/

def QuarticFourSignedPolePair.canonicalOuterPairedHorizontalLimit
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (E : W.CenteredAbelExhaustion) : ℝ :=
  (1/2 : ℝ) *
    (
      - E.leftLimit - E.rightLimit
      + W.canonicalLocalLeftAbel
      + W.canonicalLocalRightAbel
    )
    + W.signedHorizontalRemainder

theorem QuarticFourSignedPolePair.canonicalOuterPairedHorizontalLimit_eq_far_add_boundary
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (E : W.CenteredAbelExhaustion) :
    W.canonicalOuterPairedHorizontalLimit E
      =
    W.canonicalFarCompletedCompensation
      + (1/2 : ℝ) *
        (W.canonicalLocalLeftBoundary
          + W.canonicalLocalRightBoundary) := by
  rw [W.canonicalFarCompletedCompensation_eq_centeredAbel_tail ht E]
  unfold QuarticFourSignedPolePair.canonicalOuterPairedHorizontalLimit
  ring

/--
Equivalent form isolating the manuscript far carrier.  Any terminal estimate
for the asymptotic outer paired+horizontal object may therefore be transferred
without a new representation theorem; only the explicit canonical boundary
pair must be accounted for.
-/
theorem QuarticFourSignedPolePair.canonicalFarCompletedCompensation_eq_outerLimit_sub_boundary
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (E : W.CenteredAbelExhaustion) :
    W.canonicalFarCompletedCompensation
      =
    W.canonicalOuterPairedHorizontalLimit E
      - (1/2 : ℝ) *
        (W.canonicalLocalLeftBoundary
          + W.canonicalLocalRightBoundary) := by
  rw [W.canonicalOuterPairedHorizontalLimit_eq_far_add_boundary ht E]
  ring


end Synthesis
