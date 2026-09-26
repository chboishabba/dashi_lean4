import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleBidiMarkedFourth

/-!
# Quartic signed-pole H4: signed horizontal adverse-cone reduction

This file isolates the genuinely off-line horizontal payment left after the
literal V4 Riemann--von Mangoldt/Abel specialization.

For one zero write

  a     = Re rho - 1/2,
  delta = Im rho - t.

The exact horizontal fourth-angular term is

  H_rho = a^2 (a^2 - 6 delta^2).

Its sign is useful and must not be destroyed by an early absolute value.
Define the adverse cone by

  6 delta^2 < a^2.

Outside that cone every term is nonpositive.  Inside the cone,

  H_rho <= a^4.

Hence the full finite local horizontal debt is bounded above by only the
multiplicity-weighted fourth horizontal mass of the adverse cone.  The
complementary cone remains a signed favorable contribution.

This is a source-level compiler, not the missing analytic estimate for the
adverse-cone mass.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Real

namespace Synthesis

def quarticSignedPoleHorizontalFourthTerm
    (t : ℝ) (rho : Zeros) : ℝ :=
  heightOf rho^2
    * (heightOf rho^2 - 6 * ((rho : ℂ).im - t)^2)

def quarticSignedPoleHorizontalFourthAdverse
    (t : ℝ) (rho : Zeros) : Prop :=
  6 * ((rho : ℂ).im - t)^2 < heightOf rho^2

theorem quarticSignedPoleHorizontalFourthTerm_nonpos_of_not_adverse
    {t : ℝ} {rho : Zeros}
    (h : ¬ quarticSignedPoleHorizontalFourthAdverse t rho) :
    quarticSignedPoleHorizontalFourthTerm t rho <= 0 := by
  unfold quarticSignedPoleHorizontalFourthAdverse at h
  unfold quarticSignedPoleHorizontalFourthTerm
  have ha2 : 0 <= heightOf rho^2 := sq_nonneg _
  have hdiff :
      heightOf rho^2 - 6 * ((rho : ℂ).im - t)^2 <= 0 := by
    have : heightOf rho^2 <= 6 * ((rho : ℂ).im - t)^2 := by
      exact le_of_not_gt h
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos ha2 hdiff

theorem quarticSignedPoleHorizontalFourthTerm_le_fourth
    (t : ℝ) (rho : Zeros) :
    quarticSignedPoleHorizontalFourthTerm t rho
      <= heightOf rho^4 := by
  unfold quarticSignedPoleHorizontalFourthTerm
  have ha2 : 0 <= heightOf rho^2 := sq_nonneg _
  have hd2 : 0 <= ((rho : ℂ).im - t)^2 := sq_nonneg _
  nlinarith [mul_nonneg ha2 hd2]

theorem quarticSignedPoleHorizontalFourthAdverse_implies_delta_sq_lt
    {t : ℝ} {rho : Zeros}
    (h : quarticSignedPoleHorizontalFourthAdverse t rho) :
    ((rho : ℂ).im - t)^2 < heightOf rho^2 := by
  unfold quarticSignedPoleHorizontalFourthAdverse at h
  have hd2 : 0 <= ((rho : ℂ).im - t)^2 := sq_nonneg _
  nlinarith

theorem quarticSignedPoleHorizontalFourthAdverse_implies_abs_delta_lt_abs_height
    {t : ℝ} {rho : Zeros}
    (h : quarticSignedPoleHorizontalFourthAdverse t rho) :
    |(rho : ℂ).im - t| < |heightOf rho| := by
  have hsq :=
    quarticSignedPoleHorizontalFourthAdverse_implies_delta_sq_lt h
  nlinarith [sq_abs ((rho : ℂ).im - t), sq_abs (heightOf rho),
    abs_nonneg ((rho : ℂ).im - t), abs_nonneg (heightOf rho)]

def QuarticFourSignedPolePair.literalLocalHorizontalFourthAdverseAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ := by
  classical
  exact
    ∑ rho ∈ centeredZeroFinset t n,
      if quarticSignedPoleLocal t eta rho then
        if _h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
          if quarticSignedPoleHorizontalFourthAdverse t rho then
            ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
              * quarticSignedPoleHorizontalFourthTerm t rho
          else
            0
        else
          0
      else
        0

def QuarticFourSignedPolePair.literalLocalHorizontalFourthFavorableAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ := by
  classical
  exact
    ∑ rho ∈ centeredZeroFinset t n,
      if quarticSignedPoleLocal t eta rho then
        if _h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
          if quarticSignedPoleHorizontalFourthAdverse t rho then
            0
          else
            ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
              * quarticSignedPoleHorizontalFourthTerm t rho
        else
          0
      else
        0

def QuarticFourSignedPolePair.literalLocalHorizontalFourthAdverseEnvelopeAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ := by
  classical
  exact
    ∑ rho ∈ centeredZeroFinset t n,
      if quarticSignedPoleLocal t eta rho then
        if _h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
          if quarticSignedPoleHorizontalFourthAdverse t rho then
            ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
              * heightOf rho^4
          else
            0
        else
          0
      else
        0

theorem QuarticFourSignedPolePair.literalLocalHorizontalFourthCorrectionAt_eq_adverse_add_favorable
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalHorizontalFourthCorrectionAt eta n
      =
    W.literalLocalHorizontalFourthAdverseAt eta n
      + W.literalLocalHorizontalFourthFavorableAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalHorizontalFourthCorrectionAt
    QuarticFourSignedPolePair.literalLocalHorizontalFourthAdverseAt
    QuarticFourSignedPolePair.literalLocalHorizontalFourthFavorableAt
    quarticSignedPoleHorizontalFourthTerm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hl : quarticSignedPoleLocal t eta rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · by_cases hadv : quarticSignedPoleHorizontalFourthAdverse t rho
      · simp [hl, hoff, hadv]
      · simp [hl, hoff, hadv]
    · simp [hl, hoff]
  · simp [hl]

theorem QuarticFourSignedPolePair.literalLocalHorizontalFourthFavorableAt_nonpos
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalHorizontalFourthFavorableAt eta n <= 0 := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalHorizontalFourthFavorableAt
  apply Finset.sum_nonpos
  intro rho hrho
  by_cases hl : quarticSignedPoleLocal t eta rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · by_cases hadv : quarticSignedPoleHorizontalFourthAdverse t rho
      · simp [hl, hoff, hadv]
      · simp [hl, hoff, hadv]
        exact mul_nonpos_of_nonneg_of_nonpos
          (by positivity)
          (quarticSignedPoleHorizontalFourthTerm_nonpos_of_not_adverse hadv)
    · simp [hl, hoff]
  · simp [hl]

theorem QuarticFourSignedPolePair.literalLocalHorizontalFourthAdverseAt_le_envelope
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalHorizontalFourthAdverseAt eta n
      <=
    W.literalLocalHorizontalFourthAdverseEnvelopeAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalHorizontalFourthAdverseAt
    QuarticFourSignedPolePair.literalLocalHorizontalFourthAdverseEnvelopeAt
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hl : quarticSignedPoleLocal t eta rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · by_cases hadv : quarticSignedPoleHorizontalFourthAdverse t rho
      · simp [hl, hoff, hadv]
        exact mul_le_mul_of_nonneg_left
          (quarticSignedPoleHorizontalFourthTerm_le_fourth t rho)
          (by positivity)
      · simp [hl, hoff, hadv]
    · simp [hl, hoff]
  · simp [hl]

/--
H4 compiler preserving the sign of the favorable cone.

Only the adverse cone 6*delta^2 < a^2 survives in the upper budget, and even
there the exact term is replaced only by the pointwise envelope a^4.
-/
theorem QuarticFourSignedPolePair.literalLocalHorizontalFourthCorrectionAt_le_adverseEnvelope
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalHorizontalFourthCorrectionAt eta n
      <=
    W.literalLocalHorizontalFourthAdverseEnvelopeAt eta n := by
  rw [W.literalLocalHorizontalFourthCorrectionAt_eq_adverse_add_favorable]
  have hfav :=
    W.literalLocalHorizontalFourthFavorableAt_nonpos
      (eta:=eta) n
  have hadv :=
    W.literalLocalHorizontalFourthAdverseAt_le_envelope
      (eta:=eta) n
  linarith

/--
Producer-facing H4 interface.  A bound on the adverse horizontal fourth mass is
sufficient for the exact signed horizontal correction.
-/
theorem QuarticFourSignedPolePair.literalLocalHorizontalFourthCorrectionAt_le_of_adverseEnvelope_bound
    {t eta H : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hH :
      W.literalLocalHorizontalFourthAdverseEnvelopeAt eta n <= H) :
    W.literalLocalHorizontalFourthCorrectionAt eta n <= H :=
  le_trans
    (W.literalLocalHorizontalFourthCorrectionAt_le_adverseEnvelope
      (eta:=eta) n)
    hH


/-!
## Unconditional H4 payment from the existing broader cone count

The adverse cone is strictly narrower than the already-owned local cone

  delta^2 <= 6 a^2.

Hence the existing strip and fixed-window counting theorems apply without any
new horizontal-distribution hypothesis.
-/

theorem quarticSignedPoleHorizontalFourthAdverse_local_subset_localCone
    {t eta : ℝ} {rho : Zeros}
    (hl : quarticSignedPoleLocal t eta rho)
    (hadv : quarticSignedPoleHorizontalFourthAdverse t rho) :
    quarticSignedPoleLocalCone t eta rho := by
  refine ⟨hl, ?_⟩
  unfold quarticSignedPoleHorizontalFourthAdverse at hadv
  have hd2 : 0 <= ((rho : ℂ).im - t)^2 := sq_nonneg _
  have ha2 : 0 <= heightOf rho^2 := sq_nonneg _
  nlinarith

theorem QuarticFourSignedPolePair.literalLocalHorizontalFourthAdverseEnvelopeAt_le_sixteenth_coneMultiplicity
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalHorizontalFourthAdverseEnvelopeAt eta n
      <=
    (1/16 : ℝ) * (W.literalConeMultiplicityAt eta n : ℝ) := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalHorizontalFourthAdverseEnvelopeAt
    QuarticFourSignedPolePair.literalConeMultiplicityAt
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hl : quarticSignedPoleLocal t eta rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · by_cases hadv : quarticSignedPoleHorizontalFourthAdverse t rho
      · have hcone :=
          quarticSignedPoleHorizontalFourthAdverse_local_subset_localCone
            hl hadv
        have ha :=
          quarticSignedPoleLocalCone_height_abs_le_half hcone
        have ha4 : heightOf rho^4 <= (1/16 : ℝ) := by
          have ha2 : heightOf rho^2 <= (1/4 : ℝ) := by
            nlinarith [sq_abs (heightOf rho), sq_nonneg (heightOf rho)]
          have ha2non : 0 <= heightOf rho^2 := sq_nonneg _
          nlinarith [sq_nonneg (heightOf rho^2 - (1/4 : ℝ))]
        simp [hl, hoff, hadv, hcone]
        simpa [mul_comm] using
          (mul_le_mul_of_nonneg_left ha4
            (by positivity :
              0 <= ((zetaZeroConfig).mult (rho : ℂ) : ℝ)))
      · simp [hl, hoff, hadv]
        by_cases hcone : quarticSignedPoleLocalCone t eta rho
        · positivity
        · simp [hcone]
    · simp [hl, hoff]
      by_cases hcone : quarticSignedPoleLocalCone t eta rho
      · positivity
      · simp [hcone]
  · have hnotcone : ¬ quarticSignedPoleLocalCone t eta rho := by
      intro hcone
      exact hl hcone.1
    simp [hl, hnotcone]

theorem QuarticFourSignedPolePair.literalLocalHorizontalFourthAdverseEnvelopeAt_le_fixedWindowN
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalHorizontalFourthAdverseEnvelopeAt eta n
      <=
    (1/16 : ℝ)
      * (zetaZeroConfig.N
          (t - (3/2 : ℝ)) (t + (3/2 : ℝ)) : ℝ) := by
  have henv :=
    W.literalLocalHorizontalFourthAdverseEnvelopeAt_le_sixteenth_coneMultiplicity
      (eta:=eta) n
  have hmult :=
    W.literalConeMultiplicityAt_le_fixedWindowN
      (eta:=eta) n
  have hcast :
      (W.literalConeMultiplicityAt eta n : ℝ)
        <=
      (zetaZeroConfig.N
        (t - (3/2 : ℝ)) (t + (3/2 : ℝ)) : ℝ) := by
    exact_mod_cast hmult
  exact henv.trans
    (mul_le_mul_of_nonneg_left hcast (by norm_num))

theorem QuarticFourSignedPolePair.literalLocalHorizontalFourthCorrectionAt_le_fixedWindowN
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalHorizontalFourthCorrectionAt eta n
      <=
    (1/16 : ℝ)
      * (zetaZeroConfig.N
          (t - (3/2 : ℝ)) (t + (3/2 : ℝ)) : ℝ) := by
  exact
    (W.literalLocalHorizontalFourthCorrectionAt_le_adverseEnvelope
      (eta:=eta) n).trans
      (W.literalLocalHorizontalFourthAdverseEnvelopeAt_le_fixedWindowN
        (eta:=eta) n)

/--
Unconditional finite H4 bound on the literal local carrier.

No Montgomery/pair-correlation input appears: the only analytic producer is
the already-owned fixed-window local zero count.
-/
theorem exists_quarticFourSignedPole_horizontalFourthAt_le_log :
    ∃ A0 : ℝ, 0 <= A0 ∧
      ∀ {t eta : ℝ},
        200 <= t ->
        (W : QuarticFourSignedPolePair t) ->
        ∀ n : ℕ,
          W.literalLocalHorizontalFourthCorrectionAt eta n
            <=
          (3/16 : ℝ) * A0 * Real.log (t + 5) := by
  obtain ⟨A0,hA0,hcount⟩ :=
    exists_quarticSignedPole_fixedConeWindow_zeroCount_bound
  refine ⟨A0,hA0,?_⟩
  intro t eta ht W n
  have hH :=
    W.literalLocalHorizontalFourthCorrectionAt_le_fixedWindowN
      (eta:=eta) n
  have hN := hcount ht
  have hscaled :=
    mul_le_mul_of_nonneg_left hN (by norm_num : (0:ℝ) <= 1/16)
  exact hH.trans (by
    calc
      (1/16 : ℝ)
          * (zetaZeroConfig.N
              (t - (3/2 : ℝ)) (t + (3/2 : ℝ)) : ℝ)
        <=
      (1/16 : ℝ) * (3 * A0 * Real.log (t+5)) := hscaled
      _ = (3/16 : ℝ) * A0 * Real.log (t+5) := by ring)

/--
Direct V4+H4 consumer shape before the final sixth-order/FarExact absorption.

The vertical discrepancy may be estimated in absolute value, while H4 keeps its
one-sided signed estimate.
-/
theorem QuarticFourSignedPolePair.literalLocalCenteredFourthAngularAt_le_verticalAbs_add_adverseEnvelope
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalCenteredFourthAngularAt eta n
      <=
    |W.literalLocalVerticalFourthZeroMomentAt eta n
      - quarticSignedPoleLocalMuVerticalFourthMoment t eta|
      +
    W.literalLocalHorizontalFourthAdverseEnvelopeAt eta n := by
  rw [W.literalLocalCenteredFourthAngularAt_eq]
  have hv :
      W.literalLocalVerticalFourthZeroMomentAt eta n
        - quarticSignedPoleLocalMuVerticalFourthMoment t eta
      <=
      |W.literalLocalVerticalFourthZeroMomentAt eta n
        - quarticSignedPoleLocalMuVerticalFourthMoment t eta| :=
    le_abs_self _
  have hh :=
    W.literalLocalHorizontalFourthCorrectionAt_le_adverseEnvelope
      (eta:=eta) n
  linarith

end Synthesis
