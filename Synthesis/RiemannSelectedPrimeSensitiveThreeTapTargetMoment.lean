import Synthesis.RiemannSelectedPrimeSensitiveThreeTapTerminalTest
import Synthesis.RiemannProjectiveQuarticTargetLocalSign

/-!
# Three-tap transformed target and normalized-support audit

This file pays two outstanding debts from the terminal-margin test.

1. The same-ordinate height defect of the translated detector is expanded
   exactly as a quadratic polynomial in the tap strength.  No affine
   assumption is made.
2. The fixed physical translation L = log 2 becomes the normalized shift
   B(t) = (t/16) * log 2.  For t >= 200 this lies strictly outside the
   original quartic support radius pi+1.  Therefore the old local M6/M8
   budget cannot be reused definitionally for the translated detector.

No RH sign estimate is claimed here.
-/

noncomputable section
namespace Synthesis

open MeasureTheory
open scoped Real

def threeTapShiftPair (g : ℝ → ℝ) (L u : ℝ) : ℝ :=
  g (u-L) + g (u+L)

theorem detectorThreeTap_eq_base_add_shiftPair
    (g : ℝ → ℝ) (eps L u : ℝ) :
    detectorThreeTap g eps L u
      = g u + eps * threeTapShiftPair g L u := by
  unfold detectorThreeTap threeTapShiftPair
  ring

theorem threeTapShiftPair_continuous
    {g : ℝ → ℝ} (hg : Continuous g) (L : ℝ) :
    Continuous (threeTapShiftPair g L) := by
  unfold threeTapShiftPair
  fun_prop

theorem threeTapShiftPair_compact
    {g : ℝ → ℝ} (hg : HasCompactSupport g) (L : ℝ) :
    HasCompactSupport (threeTapShiftPair g L) := by
  have hminus : HasCompactSupport (fun u : ℝ => g (u-L)) := by
    have heq : (fun u : ℝ => g (u-L))
        = g ∘ (Homeomorph.addRight (-L) : ℝ ≃ₜ ℝ) := by
      funext u
      simp [Function.comp_def, sub_eq_add_neg]
    rw [heq]
    exact hg.comp_homeomorph _
  have hplus : HasCompactSupport (fun u : ℝ => g (u+L)) := by
    have heq : (fun u : ℝ => g (u+L))
        = g ∘ (Homeomorph.addRight L : ℝ ≃ₜ ℝ) := by
      rfl
    rw [heq]
    exact hg.comp_homeomorph _
  exact hminus.add hplus

/-- Exact linear response of evenResp to the three-tap detector. -/
theorem evenResp_detectorThreeTap_eq
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (eps L a s : ℝ) :
    Zeta23Bridge.LiteralWeilParityBalance.evenResp
        (detectorThreeTap g eps L) a s
      =
    Zeta23Bridge.LiteralWeilParityBalance.evenResp g a s
      + eps *
        Zeta23Bridge.LiteralWeilParityBalance.evenResp
          (threeTapShiftPair g L) a s := by
  have hshiftc := threeTapShiftPair_continuous hg L
  have hshiftk := threeTapShiftPair_compact hgc L
  have hi0 :=
    Zeta23Bridge.LiteralWeilParityBalance.taper_integrable
      hg hgc (by fun_prop :
        Continuous (fun u : ℝ => Real.cosh (a*u) * Real.cos (s*u)))
  have hi1 :=
    Zeta23Bridge.LiteralWeilParityBalance.taper_integrable
      hshiftc hshiftk (by fun_prop :
        Continuous (fun u : ℝ => Real.cosh (a*u) * Real.cos (s*u)))
  unfold Zeta23Bridge.LiteralWeilParityBalance.evenResp
  rw [show
      (fun u : ℝ =>
        detectorThreeTap g eps L u
          * (Real.cosh (a*u) * Real.cos (s*u)))
      =
      fun u =>
        g u * (Real.cosh (a*u) * Real.cos (s*u))
        + eps *
          (threeTapShiftPair g L u
            * (Real.cosh (a*u) * Real.cos (s*u))) by
      funext u
      rw [detectorThreeTap_eq_base_add_shiftPair]
      ring]
  rw [integral_add hi0 (hi1.const_mul eps), integral_const_mul]

def threeTapHeightDefectLinearCoeff
    (g : ℝ → ℝ) (L r a b : ℝ) : ℝ :=
  let S := threeTapShiftPair g L
  Zeta23Bridge.LiteralWeilParityBalance.evenResp S a (2*r)
      * Zeta23Bridge.LiteralWeilParityBalance.evenResp g b r
    +
  Zeta23Bridge.LiteralWeilParityBalance.evenResp g a (2*r)
      * Zeta23Bridge.LiteralWeilParityBalance.evenResp S b r
    -
  Zeta23Bridge.LiteralWeilParityBalance.evenResp S a r
      * Zeta23Bridge.LiteralWeilParityBalance.evenResp g b (2*r)
    -
  Zeta23Bridge.LiteralWeilParityBalance.evenResp g a r
      * Zeta23Bridge.LiteralWeilParityBalance.evenResp S b (2*r)

def threeTapHeightDefectQuadraticCoeff
    (g : ℝ → ℝ) (L r a b : ℝ) : ℝ :=
  let S := threeTapShiftPair g L
  Zeta23Bridge.LiteralWeilParityBalance.evenResp S a (2*r)
      * Zeta23Bridge.LiteralWeilParityBalance.evenResp S b r
    -
  Zeta23Bridge.LiteralWeilParityBalance.evenResp S a r
      * Zeta23Bridge.LiteralWeilParityBalance.evenResp S b (2*r)

/-- The transformed target is exactly quadratic in eps. -/
theorem heightDefect_detectorThreeTap_quadratic
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (eps L r a b : ℝ) :
    Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.heightDefect
        (detectorThreeTap g eps L) r a b
      =
    Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.heightDefect
        g r a b
      + eps * threeTapHeightDefectLinearCoeff g L r a b
      + eps^2 * threeTapHeightDefectQuadraticCoeff g L r a b := by
  unfold Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.heightDefect
    threeTapHeightDefectLinearCoeff
    threeTapHeightDefectQuadraticCoeff
  dsimp
  rw [evenResp_detectorThreeTap_eq hg hgc,
      evenResp_detectorThreeTap_eq hg hgc,
      evenResp_detectorThreeTap_eq hg hgc,
      evenResp_detectorThreeTap_eq hg hgc]
  ring

theorem heightDefect_detectorThreeTap_zero_height
    {g : ℝ → ℝ}
    (eps L r : ℝ) :
    Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.heightDefect
      (detectorThreeTap g eps L) r 0 0 = 0 := by
  exact heightDefect_at_zero_height _ _

/-! ## Physical-to-normalized shift firewall -/

def threeTapNormalizedShift (t L : ℝ) : ℝ :=
  (t/16) * L

theorem threeTapNormalizedShift_logTwo_gt_pi_add_one
    {t : ℝ} (ht : 200 ≤ t) :
    Real.pi + 1 < threeTapNormalizedShift t (Real.log 2) := by
  have hlog : (1/2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos
      (show (0:ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hpi : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  unfold threeTapNormalizedShift
  have ht0 : 0 ≤ t/16 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlog ht0
  nlinarith

theorem threeTapNormalizedShift_logTwo_gt_canonicalSupport
    {t : ℝ} (ht : 200 ≤ t) :
    Real.pi + 1
      < threeTapNormalizedShift t (Real.log 2) :=
  threeTapNormalizedShift_logTwo_gt_pi_add_one ht

/-- Any local budget proved only for normalized support |v| <= pi+1
cannot be reused for the shifted copies at t>=200 without a new estimate. -/
theorem threeTap_shift_not_in_canonical_normalized_support
    {t : ℝ} (ht : 200 ≤ t) :
    ¬ |threeTapNormalizedShift t (Real.log 2)| ≤ Real.pi + 1 := by
  have hpos : 0 < threeTapNormalizedShift t (Real.log 2) := by
    unfold threeTapNormalizedShift
    have htpos : 0 < t := by linarith
    positivity
  rw [abs_of_pos hpos]
  exact not_le.mpr (threeTapNormalizedShift_logTwo_gt_pi_add_one ht)

end Synthesis
