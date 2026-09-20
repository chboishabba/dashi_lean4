import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

open Set MeasureTheory

namespace Synthesis.NavierStokes

/-- Positive-rate Laplace authority used by the NS Cauchy-resolvent lane:
    ∫₀^∞ exp (-r t) dt = 1 / r. -/
theorem integral_exp_neg_rate_Ioi {r : ℝ} (hr : 0 < r) :
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-(r * t))) = 1 / r := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (1 : ℝ)) (r := r) zero_lt_one hr
  simpa using h

/-- The positive Cauchy kernel is exactly the Gram/Laplace kernel. -/
theorem cauchy_kernel_eq_laplace {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ t : ℝ in Set.Ioi 0,
        Real.exp (-(x * t)) * Real.exp (-(y * t))) =
      1 / (x + y) := by
  have hxy : 0 < x + y := add_pos hx hy
  have hfun :
      (fun t : ℝ => Real.exp (-(x * t)) * Real.exp (-(y * t))) =
        (fun t : ℝ => Real.exp (-((x + y) * t))) := by
    funext t
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfun, integral_exp_neg_rate_Ioi hxy]

/-- Symmetric orientation, useful when welding the Lean identity to the
    pair-rate kernel used by the Agda R490/R491 lane. -/
theorem cauchy_kernel_eq_laplace_symm {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ t : ℝ in Set.Ioi 0,
        Real.exp (-(y * t)) * Real.exp (-(x * t))) =
      1 / (x + y) := by
  simpa [add_comm, mul_comm] using cauchy_kernel_eq_laplace hy hx

end Synthesis.NavierStokes
