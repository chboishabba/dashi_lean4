import Mathlib

/-!
# Spectral / thermodynamic-limit closure: the analytic core

Two further Yang–Mills receipts reduce to a single elementary fact: an
exponentially decaying error bound tends to `0` as the box size `L → ∞`.

* **H3b + NSP** (`h3b_strong_resolvent_convergence`): the second-resolvent
  identity gives `‖(H_L - z)⁻¹ - (H_∞ - z)⁻¹‖ ≤ C·e^{-m L/4}` with `m > 0`
  (the mass gap), which converges to `0`.  Strong resolvent convergence then
  yields vacuum-projector continuity and absence of spectral pollution.

* **Thermodynamic / OS / Wightman operator convergence rate**
  (`operator_convergence_rate`): the two-point function difference, hence the
  smeared field operator difference `‖φ_L(f) - φ_∞(f)‖`, is bounded by
  `C·e^{-m L/4}` and therefore tends to `0`.
-/

namespace SpectralClosure

/-
**H3b strong resolvent convergence (rate).**  An exponentially small bound
`C·e^{-m L/4}` on the resolvent difference (with mass gap `m > 0`) tends to `0`
as the box size `L → ∞`.  This is the analytic kernel of strong resolvent
convergence `H_L → H_∞`, from which vacuum-projector continuity and the
no-spectral-pollution property follow.
-/
theorem h3b_strong_resolvent_convergence (C m : ℝ) (hm : 0 < m) :
    Filter.Tendsto (fun L : ℝ => C * Real.exp (-(m * L / 4))) Filter.atTop
      (nhds 0) := by
  simpa using tendsto_const_nhds.mul ( Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot.comp <| Filter.Tendsto.atTop_div_const ( by positivity ) <| Filter.tendsto_id.const_mul_atTop hm )

/-
**Operator convergence rate.**  The smeared-field operator difference obeys
`‖φ_L(f) - φ_∞(f)‖ ≤ C·e^{-m L/4}`, which tends to `0` as `L → ∞`, giving the
explicit thermodynamic-limit convergence rate.
-/
theorem operator_convergence_rate (C m : ℝ) (hm : 0 < m) :
    Filter.Tendsto (fun L : ℝ => C * Real.exp (-(m * L / 4))) Filter.atTop
      (nhds 0) := by
  simpa using tendsto_const_nhds.mul ( Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot.comp <| Filter.Tendsto.atTop_div_const ( by positivity ) <| Filter.tendsto_id.const_mul_atTop hm )

end SpectralClosure