import Mathlib
import Synthesis.RiemannFarShellQuarticCutoff

/-!
# Sign-window / quartic-cutoff incompatibility

The centered near-pair sign theorem is valid only while

    J * Λ ≤ π/2.

For the canonical support radius Λ = 9π/(4t), this forces

    J ≤ 2t/9.

Hence a quartic cutoff J ≥ t^4 cannot simultaneously inhabit the same signed
near window once t ≥ 1.  This closes a misleading route in the RH R2 search:
the O(t^-2) quartic far-shell donor cannot simply be substituted for the
sign-compatible J=O(t) cutoff.  Any successful use of a larger cutoff needs an
independent intermediate-shell theorem, or else a sharper tail estimate at a
sign-compatible cutoff.
-/

noncomputable section

open scoped Real

namespace Synthesis

theorem signedWindow_forces_cutoff_le_two_ninths
    {t J : ℝ}
    (ht : 0 < t)
    (hwindow : J * (9 * Real.pi / (4 * t)) ≤ Real.pi / 2) :
    J ≤ 2 * t / 9 := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hscale : 0 ≤ 4 * t / (9 * Real.pi) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hwindow hscale
  have hleft :
      (J * (9 * Real.pi / (4 * t))) * (4 * t / (9 * Real.pi)) = J := by
    field_simp [ne_of_gt ht, ne_of_gt hp]
    <;> ring
  have hright :
      (Real.pi / 2) * (4 * t / (9 * Real.pi)) = 2 * t / 9 := by
    field_simp [ne_of_gt hp]
    <;> ring
  rw [hleft, hright] at hmul
  exact hmul

theorem pow_four_gt_two_ninths_mul
    {t : ℝ} (ht : 1 ≤ t) :
    2 * t / 9 < t ^ 4 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hfac : 0 ≤ t * (t - 1) * (t^2 + t + 1) := by
    positivity
  have hpow : t ≤ t^4 := by
    nlinarith [hfac]
  nlinarith

theorem quartic_cutoff_cannot_stay_in_canonical_sign_window
    {t J : ℝ}
    (ht : 1 ≤ t)
    (hquartic : t ^ 4 ≤ J) :
    ¬ (J * (9 * Real.pi / (4 * t)) ≤ Real.pi / 2) := by
  intro hwindow
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hupper := signedWindow_forces_cutoff_le_two_ninths ht0 hwindow
  have hstrict := pow_four_gt_two_ninths_mul ht
  linarith

end Synthesis
