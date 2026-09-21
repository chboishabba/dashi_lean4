import Zeta23.GammaFacts.StirlingVert
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Explicit positivity of the theorem-bearing RvM density at high ordinate

Zeta23's retained vertical Stirling proof gives the concrete estimate

  |mu(t) - (1/(2*pi)) log(|t|/(2*pi))|
    <= (20/(2*pi))/t^2.

The packaged GammaFacts field intentionally hides this behind an existential
constant.  For the signed Goal-1 consumer we keep the proved concrete constant.

At t >= 18 the main logarithm is already larger than log 2, while 20/t^2 is
less than 20/18^2.  The standard Mathlib numerical lower bound for log 2 then
gives mu(t)>0.

No asymptotic threshold is postulated.
-/

noncomputable section

open scoped Real

namespace Synthesis

/-- The concrete Stirling estimate already proved in Zeta23, with its explicit
constant retained rather than existentially packaged. -/
theorem zetaMu_stirling_explicit
    {tau : ℝ} (htau : 1 <= |tau|) :
    |Zeta23.mu tau
        - (1 / (2 * Real.pi))
          * Real.log (|tau| / (2 * Real.pi))|
      <= (20 / (2 * Real.pi)) / tau^2 := by
  have hhalf : 1 / 2 <= |tau / 2| := by
    rw [abs_div, abs_two]
    linarith
  have hdig :=
    Zeta23.StirlingVert.re_digamma_stirling'
      (a := 1 / 4) (by norm_num) (by norm_num) hhalf
  have htau0 : 0 < |tau| := by linarith
  let D : ℝ :=
    (Complex.digamma
      ((((1 : ℝ) / 4 : ℝ) : ℂ)
        + Complex.I * ((tau / 2 : ℝ) : ℂ))).re
      - Real.log |tau / 2|
  have hD5 : |D| <= 5 / (tau / 2)^2 := by
    simpa [D] using hdig
  have hlogs :
      Real.log (|tau| / (2 * Real.pi))
        = Real.log |tau / 2| - Real.log Real.pi := by
    rw [abs_div, abs_two,
      Real.log_div htau0.ne' (by positivity : (0 : ℝ) < 2 * Real.pi).ne',
      Real.log_div htau0.ne' two_ne_zero,
      Real.log_mul two_ne_zero Real.pi_ne_zero]
    ring
  have hkey :
      Zeta23.mu tau
        - (1 / (2 * Real.pi))
          * Real.log (|tau| / (2 * Real.pi))
        =
      (1 / (2 * Real.pi)) * D := by
    rw [Zeta23.MuFields.mu_eq tau, hlogs]
    dsimp [D]
    ring
  rw [hkey, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  calc
    1 / (2 * Real.pi) * |D|
        <= 1 / (2 * Real.pi) * (5 / (tau / 2)^2) := by
          gcongr
    _ = (20 / (2 * Real.pi)) / tau^2 := by
          field_simp
          ring

/-- For every positive ordinate at least 18, the exact RvM density is strictly
positive. -/
theorem zetaMu_pos_of_eighteen_le
    {tau : ℝ} (htau : 18 <= tau) :
    0 < Zeta23.mu tau := by
  have htauPos : 0 < tau := by linarith
  have habs : |tau| = tau := abs_of_pos htauPos
  have h1 : 1 <= |tau| := by rw [habs]; linarith
  have hst := zetaMu_stirling_explicit h1
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hratio2 : 2 < |tau| / (2 * Real.pi) := by
    rw [habs]
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith [Real.pi_pos]
  have hlog :
      Real.log 2 < Real.log (|tau| / (2 * Real.pi)) := by
    exact Real.log_lt_log (by norm_num) hratio2
  have hlogLower :
      (0.6931471803 : ℝ)
        < Real.log (|tau| / (2 * Real.pi)) := by
    exact Real.log_two_gt_d9.trans hlog
  have htauSq : (18 : ℝ)^2 <= tau^2 := by
    nlinarith
  have herr :
      (20 : ℝ) / tau^2 < 0.6931471803 := by
    have hsqpos : 0 < tau^2 := sq_pos_of_pos htauPos
    rw [div_lt_iff₀ hsqpos]
    have : (20 : ℝ) < 0.6931471803 * 18^2 := by norm_num
    nlinarith
  have hcoef : 0 < 1 / (2 * Real.pi) := by positivity
  have hmain :
      (20 / (2 * Real.pi)) / tau^2
        <
      (1 / (2 * Real.pi))
        * Real.log (|tau| / (2 * Real.pi)) := by
    have hscaled := mul_lt_mul_of_pos_left
      (lt_trans herr hlogLower) hcoef
    convert hscaled using 1 <;> field_simp <;> ring
  have habsBound := (abs_le.mp hst).1
  linarith

/-- Positivity persists on every interval to the right of a high target
ordinate. -/
theorem zetaMu_pos_of_high_right
    {t x : ℝ} (ht : 18 <= t) (htx : t <= x) :
    0 < Zeta23.mu x :=
  zetaMu_pos_of_eighteen_le (ht.trans htx)

end Synthesis
