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
  apply Finset.sum_nonpos
  intro _ hmem
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
  apply Finset.sum_le_sum
  intro _ hmem
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

end Synthesis
