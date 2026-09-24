import Mathlib

/-!
# Adaptive natural cutoff compatibility

The RH Off lane needs one natural cutoff J which does two things at once:

1. crosses the quarter-period threshold: pi/2 < J * Lambda;
2. makes a chosen far-error envelope smaller than epsilon.

There is no asymptotic conflict between these requirements.  For every
Lambda > 0 the crossing condition holds eventually as J -> infinity, and any
far envelope tending to zero is eventually below every epsilon > 0.  Their
intersection therefore contains a natural cutoff.

This theorem is domain-neutral.  Instantiating it with the literal
FarShellCutoffTailBound and transporting the selected J into the final Agda
carrier remain separate same-object/replay payments.
-/

namespace Synthesis

theorem eventually_quarterPeriodCrossing {Λ : ℝ} (hΛ : 0 < Λ) :
    ∀ᶠ J : ℕ in Filter.atTop, Real.pi / 2 < (J : ℝ) * Λ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.pi / (2 * Λ))
  filter_upwards [Filter.eventually_ge_atTop N] with J hNJ
  have hcast : (N : ℝ) ≤ (J : ℝ) := by
    exact_mod_cast hNJ
  have hmul :
      (Real.pi / (2 * Λ)) * Λ < (N : ℝ) * Λ :=
    mul_lt_mul_of_pos_right hN hΛ
  have hΛne : Λ ≠ 0 := ne_of_gt hΛ
  have hsimp : (Real.pi / (2 * Λ)) * Λ = Real.pi / 2 := by
    field_simp [hΛne]
  rw [hsimp] at hmul
  exact lt_of_lt_of_le hmul (mul_le_mul_of_nonneg_right hcast hΛ.le)

theorem exists_nat_cutoff_crossing_and_small
    {Λ ε : ℝ} (hΛ : 0 < Λ) (hε : 0 < ε)
    {far : ℕ → ℝ}
    (hfar : Filter.Tendsto far Filter.atTop (nhds 0)) :
    ∃ J : ℕ, 1 ≤ J ∧ Real.pi / 2 < (J : ℝ) * Λ ∧ far J < ε := by
  have hsmall : ∀ᶠ J : ℕ in Filter.atTop, far J < ε := by
    simpa using hfar.eventually (eventually_lt_nhds hε)
  have hcross := eventually_quarterPeriodCrossing hΛ
  obtain ⟨J, hJone, hJcross, hJsmall⟩ :=
    ((Filter.eventually_ge_atTop 1).and (hcross.and hsmall)).exists
  exact ⟨J, hJone, hJcross, hJsmall⟩

end Synthesis
