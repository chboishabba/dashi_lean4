/-
A summable complex-`Φ` mixed-kernel envelope.

The Agda module `DASHI.Analysis.RiemannMixedKernelEnvelopeExact` posits a
ledger in which the mixed interference of the complex extension is dominated
by a summable envelope; the envelope itself is left to an analytic producer.

Here the envelope is *produced*, for an explicit real even taper: the Gaussian
`t ↦ exp(-t²/2)`.  We compute its complex bilinear extension in closed form,
read off the exact modulus of every centred-grid sample, prove that these
moduli are summable along the grid (for any nonzero spacing), and conclude
that the mixed kernel `Φ(z_j) · conj Φ(z_k)` is absolutely summable over
`ℤ × ℤ` with total mass the square of the one-dimensional envelope sum.
-/
import RiemannAnalytic.LatticeRetention

namespace RiemannAnalytic

open Complex MeasureTheory

/-- The Gaussian taper `t ↦ exp(-t²/2)`: real, even, and positive. -/
noncomputable def gaussTaper (t : ℝ) : ℝ := Real.exp (-(t ^ 2) / 2)

theorem gaussTaper_even (t : ℝ) : gaussTaper (-t) = gaussTaper t := by
  simp [gaussTaper]

/-- Closed form of the complex bilinear extension of the Gaussian taper:
`Φ(z) = (2π)^{1/2} e^{-z²/2}`. -/
theorem PhiExt_gaussTaper (z : ℂ) :
    PhiExt gaussTaper z = ((2 * Real.pi : ℝ) : ℂ) ^ (1 / 2 : ℂ)
      * Complex.exp (-z ^ 2 / 2) := by
  have hb : (-(1 / 2 : ℂ)).re < 0 := by norm_num
  have hint : ∀ t : ℝ,
      ((gaussTaper t : ℝ) : ℂ) * Complex.exp (-(Complex.I * z * (t : ℂ)))
        = Complex.exp (-(1 / 2 : ℂ) * (t : ℂ) ^ 2 + (-(Complex.I * z)) * (t : ℂ) + 0) := by
    intro t
    have : ((gaussTaper t : ℝ) : ℂ) = Complex.exp (-(1 / 2 : ℂ) * (t : ℂ) ^ 2) := by
      simp only [gaussTaper, Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [this, ← Complex.exp_add]
    congr 1
    ring
  have hquad := integral_cexp_quadratic hb (-(Complex.I * z)) 0
  unfold PhiExt
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hint), hquad]
  have hbase : (Real.pi : ℂ) / -(-(1 / 2 : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hbase]
  congr 1
  have : (-(Complex.I * z)) ^ 2 / (4 * -(1 / 2 : ℂ)) = z ^ 2 / 2 := by
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    field_simp
    ring_nf
    rw [hI]
    ring
  rw [this]
  ring_nf

/-- The exact modulus of the centred-grid samples of the Gaussian taper. -/
theorem norm_gridSample_gaussTaper (h α : ℝ) (k : ℤ) :
    ‖gridSample gaussTaper h α k‖
      = Real.sqrt (2 * Real.pi) * Real.exp ((α ^ 2 - ((k : ℝ) * h) ^ 2) / 2) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  unfold gridSample
  rw [PhiExt_gaussTaper, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpi,
    Complex.norm_exp]
  have h1 : ((1 : ℂ) / 2).re = (1 / 2 : ℝ) := by norm_num
  have h2 : (-(((k : ℝ) : ℂ) * (h : ℂ) - Complex.I * (α : ℂ)) ^ 2 / 2).re
      = (α ^ 2 - ((k : ℝ) * h) ^ 2) / 2 := by
    simp [pow_two]
  rw [h1, h2, ← Real.sqrt_eq_rpow]

/-- For a nonzero grid spacing the Gaussian envelope is summable along the
whole two-sided lattice. -/
theorem summable_gaussEnvelope (h α C : ℝ) (hh : h ≠ 0) :
    Summable fun k : ℤ => C * Real.exp ((α ^ 2 - ((k : ℝ) * h) ^ 2) / 2) := by
  have hc : -(h ^ 2 / 2) < 0 := by
    have : (0 : ℝ) < h ^ 2 := by positivity
    linarith
  have hbase : Summable fun n : ℕ => Real.exp (-(h ^ 2 / 2) * ((n : ℝ) ^ 2)) :=
    Real.summable_exp_nat_mul_of_ge hc (f := fun n : ℕ => (n : ℝ) ^ 2) (by
      intro i
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · simp [h0]
      · have h1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast h0
        nlinarith)
  have hnat : Summable fun n : ℕ => C * Real.exp ((α ^ 2 - (((n : ℤ) : ℝ) * h) ^ 2) / 2) := by
    refine ((hbase.mul_left (Real.exp (α ^ 2 / 2))).mul_left C).congr fun n => ?_
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring_nf
  refine Summable.of_nat_of_neg hnat ?_
  refine hnat.congr fun n => ?_
  push_cast
  ring_nf

theorem summable_norm_gridSample_gaussTaper (h α : ℝ) (hh : h ≠ 0) :
    Summable fun k : ℤ => ‖gridSample gaussTaper h α k‖ := by
  refine (summable_gaussEnvelope h α (Real.sqrt (2 * Real.pi)) hh).congr fun k => ?_
  rw [norm_gridSample_gaussTaper]

/-- The mixed kernel of the complex extension on the centred grid. -/
noncomputable def mixedKernel (φ : ℝ → ℝ) (h α : ℝ) (p : ℤ × ℤ) : ℂ :=
  gridSample φ h α p.1 * (starRingEnd ℂ) (gridSample φ h α p.2)

/-- **Summable complex-`Φ` mixed-kernel envelope.**  For the Gaussian taper and
any nonzero grid spacing the mixed kernel is absolutely summable over the full
two-sided lattice, and its absolute mass is the square of the one-dimensional
envelope sum. -/
theorem mixedKernel_gaussTaper_summable (h α : ℝ) (hh : h ≠ 0) :
    Summable (fun p : ℤ × ℤ => ‖mixedKernel gaussTaper h α p‖) ∧
      ∑' p : ℤ × ℤ, ‖mixedKernel gaussTaper h α p‖
        = (∑' k : ℤ, ‖gridSample gaussTaper h α k‖) ^ 2 := by
  have hsum := summable_norm_gridSample_gaussTaper h α hh
  have hnorm : ∀ p : ℤ × ℤ, ‖mixedKernel gaussTaper h α p‖
      = ‖gridSample gaussTaper h α p.1‖ * ‖gridSample gaussTaper h α p.2‖ := by
    intro p
    simp [mixedKernel]
  have hprod : Summable fun p : ℤ × ℤ =>
      ‖gridSample gaussTaper h α p.1‖ * ‖gridSample gaussTaper h α p.2‖ :=
    hsum.mul_of_nonneg hsum (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  refine ⟨hprod.congr fun p => (hnorm p).symm, ?_⟩
  have heq : ∑' p : ℤ × ℤ, ‖mixedKernel gaussTaper h α p‖
      = ∑' p : ℤ × ℤ, ‖gridSample gaussTaper h α p.1‖ * ‖gridSample gaussTaper h α p.2‖ :=
    tsum_congr hnorm
  rw [heq, ← tsum_mul_tsum_of_summable_norm (f := fun k : ℤ => ‖gridSample gaussTaper h α k‖)
      (g := fun k : ℤ => ‖gridSample gaussTaper h α k‖)
      (by simpa using hsum) (by simpa using hsum)]
  ring

end RiemannAnalytic
