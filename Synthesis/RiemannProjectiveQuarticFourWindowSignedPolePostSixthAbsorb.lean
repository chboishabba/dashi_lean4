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


end Synthesis
