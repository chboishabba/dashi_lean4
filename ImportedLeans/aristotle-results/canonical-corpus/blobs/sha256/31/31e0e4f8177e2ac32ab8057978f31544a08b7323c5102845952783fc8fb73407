/-
# A single curvature constant serves every zero of the critical strip

`ReflectionPairKernelDecay.abs_zeroConeValue_add_reflect_le` bounds the response
of a functional-equation pair of zeros by

    m_ρ · pairWeightCurvature g (heightOf ρ) / (Im ρ − t)² ,

where the curvature constant still depends on the horizontal height
`a = Re ρ − 1/2` of the zero.  For the aggregation over the infinite carrier one
needs a bound that does *not* move with the zero.

This module supplies it.  The second derivative of the reflection-pair weight
`u ↦ 4 g(u) cosh(a u)` is computed exactly,

    (4 g cosh(a·))'' = 4 (g'' cosh(a·) + 2a g' sinh(a·) + a² g cosh(a·)),

and, since every zero of the strip has `|a| ≤ 1/2` and the taper is supported in
a ball of radius `R`, all three hyperbolic factors are bounded by `cosh (R/2)`.
Hence

    pairWeightCurvature g a ≤ 4 cosh(R/2) · (‖g''‖₁ + ‖g'‖₁ + ‖g‖₁)

uniformly for `|a| ≤ 1/2`.

No `sorry`, no `axiom`, no Boolean receipt, no numerical evidence.
-/
import Zeta23Bridge.ReflectionPairKernelDecay

noncomputable section

open MeasureTheory
open scoped Real

namespace Zeta23Bridge
namespace ReflectionPairCurvatureBound

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.ReflectionPairKernelDecay

variable {g : ℝ → ℝ}


theorem hasDerivAt_cosh_mul (a u : ℝ) :
    HasDerivAt (fun u : ℝ => Real.cosh (a * u)) (a * Real.sinh (a * u)) u := by
  have := (Real.hasDerivAt_cosh (a * u)).comp u ((hasDerivAt_id u).const_mul a)
  simpa [Function.comp_def, mul_comm] using this

theorem hasDerivAt_sinh_mul (a u : ℝ) :
    HasDerivAt (fun u : ℝ => Real.sinh (a * u)) (a * Real.cosh (a * u)) u := by
  have := (Real.hasDerivAt_sinh (a * u)).comp u ((hasDerivAt_id u).const_mul a)
  simpa [Function.comp_def, mul_comm] using this

theorem hasDerivAt_pairWeight (hg : ContDiff ℝ 2 g) (a u : ℝ) :
    HasDerivAt (pairWeight g a)
      (4 * (deriv g u * Real.cosh (a * u) + a * g u * Real.sinh (a * u))) u := by
  have h1 : HasDerivAt g (deriv g u) u :=
    (hg.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have h3 := (h1.const_mul (4:ℝ)).mul (hasDerivAt_cosh_mul a u)
  have heq : (4:ℝ) * (deriv g u * Real.cosh (a * u) + a * g u * Real.sinh (a * u))
      = 4 * deriv g u * Real.cosh (a * u) + 4 * g u * (a * Real.sinh (a * u)) := by ring
  rw [heq]
  exact h3

theorem contDiff_deriv_g (hg : ContDiff ℝ 2 g) : ContDiff ℝ 1 (deriv g) :=
  ((contDiff_succ_iff_deriv (n := 1)).mp hg).2.2

theorem hasDerivAt_deriv_pairWeight (hg : ContDiff ℝ 2 g) (a u : ℝ) :
    HasDerivAt (fun u => 4 * (deriv g u * Real.cosh (a * u) + a * g u * Real.sinh (a * u)))
      (4 * (deriv (deriv g) u * Real.cosh (a * u) + 2 * a * deriv g u * Real.sinh (a * u)
        + a ^ 2 * g u * Real.cosh (a * u))) u := by
  have hg1 : HasDerivAt g (deriv g u) u :=
    (hg.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hg2 : HasDerivAt (deriv g) (deriv (deriv g) u) u :=
    ((contDiff_deriv_g hg).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hA := hg2.mul (hasDerivAt_cosh_mul a u)
  have hB := (hg1.const_mul a).mul (hasDerivAt_sinh_mul a u)
  have h3 := (hA.add hB).const_mul (4:ℝ)
  have heq : (4:ℝ) * (deriv (deriv g) u * Real.cosh (a * u)
        + 2 * a * deriv g u * Real.sinh (a * u) + a ^ 2 * g u * Real.cosh (a * u))
      = 4 * ((deriv (deriv g) u * Real.cosh (a * u) + deriv g u * (a * Real.sinh (a * u)))
        + (a * deriv g u * Real.sinh (a * u) + a * g u * (a * Real.cosh (a * u)))) := by ring
  rw [heq]
  exact h3

theorem deriv2_pairWeight (hg : ContDiff ℝ 2 g) (a : ℝ) :
    deriv (deriv (pairWeight g a)) = fun u =>
      4 * (deriv (deriv g) u * Real.cosh (a * u) + 2 * a * deriv g u * Real.sinh (a * u)
        + a ^ 2 * g u * Real.cosh (a * u)) := by
  have h1 : deriv (pairWeight g a)
      = fun u => 4 * (deriv g u * Real.cosh (a * u) + a * g u * Real.sinh (a * u)) := by
    funext u; exact (hasDerivAt_pairWeight hg a u).deriv
  rw [h1]
  funext u
  exact (hasDerivAt_deriv_pairWeight hg a u).deriv


/-- Off a ball containing the support, `g` and its first two derivatives vanish. -/
theorem vanish_outside (hgc : HasCompactSupport g) {R : ℝ} (u : ℝ)
    (hu : u ∉ Metric.closedBall (0:ℝ) R) (hsub : tsupport g ⊆ Metric.closedBall (0:ℝ) R) :
    g u = 0 ∧ deriv g u = 0 ∧ deriv (deriv g) u = 0 := by
  have h0 : u ∉ tsupport g := fun h => hu (hsub h)
  have hd1 : u ∉ tsupport (deriv g) := by
    intro h
    exact h0 (closure_minimal (support_deriv_subset) isClosed_closure h)
  have hd2 : u ∉ tsupport (deriv (deriv g)) := by
    intro h
    exact hd1 (closure_minimal (support_deriv_subset) isClosed_closure h)
  exact ⟨image_eq_zero_of_notMem_tsupport h0, image_eq_zero_of_notMem_tsupport hd1,
    image_eq_zero_of_notMem_tsupport hd2⟩

theorem exists_ball_tsupport (hgc : HasCompactSupport g) :
    ∃ R : ℝ, 0 ≤ R ∧ tsupport g ⊆ Metric.closedBall (0:ℝ) R := by
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall (0:ℝ)
  exact ⟨max R 0, le_max_right _ _,
    hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩


theorem abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  have h := Real.cosh_sq' x
  have hc : 0 < Real.cosh x := Real.cosh_pos x
  nlinarith [sq_abs (Real.sinh x), abs_nonneg (Real.sinh x)]

theorem abs_deriv2_pairWeight_le (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    {R : ℝ} (hR0 : 0 ≤ R) (hsub : tsupport g ⊆ Metric.closedBall (0:ℝ) R)
    {a : ℝ} (ha : |a| ≤ 1/2) (u : ℝ) :
    |deriv (deriv (pairWeight g a)) u|
      ≤ 4 * Real.cosh (R/2) * (|deriv (deriv g) u| + |deriv g u| + |g u|) := by
  rw [deriv2_pairWeight hg a]
  set K : ℝ := Real.cosh (R/2) with hK
  have hK1 : 1 ≤ K := by
    rw [hK]; exact Real.one_le_cosh _
  by_cases hu : u ∈ Metric.closedBall (0:ℝ) R
  · have hur : |u| ≤ R := by
      have := mem_closedBall_zero_iff.1 hu
      simpa [Real.norm_eq_abs] using this
    have hau : |a * u| ≤ R/2 := by
      rw [abs_mul]
      nlinarith [abs_nonneg a, abs_nonneg u]
    have hcosh : Real.cosh (a * u) ≤ K := by
      rw [hK]
      exact Real.cosh_le_cosh.2 (by rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ R/2)]; exact hau)
    have hch0 : 0 < Real.cosh (a * u) := Real.cosh_pos _
    have hsinh : |Real.sinh (a * u)| ≤ K := le_trans (abs_sinh_le_cosh _) hcosh
    set A := deriv (deriv g) u
    set B := deriv g u
    set C := g u
    have t1 : |A * Real.cosh (a*u)| ≤ |A| * K := by
      rw [abs_mul, abs_of_pos hch0]
      exact mul_le_mul_of_nonneg_left hcosh (abs_nonneg A)
    have t2 : |2 * a * B * Real.sinh (a*u)| ≤ |B| * K := by
      rw [abs_mul, abs_mul, abs_mul]
      have h2a : |(2:ℝ)| * |a| ≤ 1 := by rw [abs_two]; linarith
      calc |(2:ℝ)| * |a| * |B| * |Real.sinh (a*u)| ≤ 1 * |B| * K := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right h2a (abs_nonneg B)) hsinh
              (abs_nonneg _) (by positivity)
        _ = |B| * K := by ring
    have t3 : |a^2 * C * Real.cosh (a*u)| ≤ |C| * K := by
      rw [abs_mul, abs_mul]
      have ha2 : |a^2| ≤ 1 := by
        rw [abs_pow]
        nlinarith [abs_nonneg a]
      calc |a^2| * |C| * |Real.cosh (a*u)| ≤ 1 * |C| * K := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right ha2 (abs_nonneg C))
              (by rw [abs_of_pos hch0]; exact hcosh) (abs_nonneg _) (by positivity)
        _ = |C| * K := by ring
    have hsplit : |4 * (A * Real.cosh (a*u) + 2*a*B*Real.sinh (a*u) + a^2*C*Real.cosh (a*u))|
        ≤ 4 * (|A * Real.cosh (a*u)| + |2*a*B*Real.sinh (a*u)| + |a^2*C*Real.cosh (a*u)|) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
      have := abs_add_le (A * Real.cosh (a*u) + 2*a*B*Real.sinh (a*u)) (a^2*C*Real.cosh (a*u))
      have h2 := abs_add_le (A * Real.cosh (a*u)) (2*a*B*Real.sinh (a*u))
      nlinarith
    calc |4 * (A * Real.cosh (a*u) + 2*a*B*Real.sinh (a*u) + a^2*C*Real.cosh (a*u))|
        ≤ 4 * (|A * Real.cosh (a*u)| + |2*a*B*Real.sinh (a*u)| + |a^2*C*Real.cosh (a*u)|) := hsplit
      _ ≤ 4 * (|A| * K + |B| * K + |C| * K) := by linarith
      _ = 4 * K * (|A| + |B| + |C|) := by ring
  · obtain ⟨h1, h2, h3⟩ := vanish_outside hgc u hu hsub
    simp [h1, h2, h3]


theorem continuous_deriv2 (hg : ContDiff ℝ 2 g) : Continuous (deriv (deriv g)) :=
  (((contDiff_succ_iff_deriv (n := 0)).mp (contDiff_deriv_g hg)).2.2).continuous

theorem pairWeightCurvature_le (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    {R : ℝ} (hR0 : 0 ≤ R) (hsub : tsupport g ⊆ Metric.closedBall (0:ℝ) R)
    {a : ℝ} (ha : |a| ≤ 1/2) :
    pairWeightCurvature g a
      ≤ ∫ u : ℝ, 4 * Real.cosh (R/2) * (|deriv (deriv g) u| + |deriv g u| + |g u|) := by
  have hc0 : Continuous g := hg.continuous
  have hc1 : Continuous (deriv g) := (contDiff_deriv_g hg).continuous
  have hc2 : Continuous (deriv (deriv g)) := continuous_deriv2 hg
  have hMc : Continuous
      (fun u : ℝ => 4 * Real.cosh (R/2) * (|deriv (deriv g) u| + |deriv g u| + |g u|)) := by
    exact continuous_const.mul (((hc2.abs).add (hc1.abs)).add (hc0.abs))
  have hMs : HasCompactSupport
      (fun u : ℝ => 4 * Real.cosh (R/2) * (|deriv (deriv g) u| + |deriv g u| + |g u|)) :=
    HasCompactSupport.mul_left
      (((hgc.deriv.deriv.abs).add (hgc.deriv.abs)).add hgc.abs)
  have hMi : MeasureTheory.Integrable
      (fun u : ℝ => 4 * Real.cosh (R/2) * (|deriv (deriv g) u| + |deriv g u| + |g u|)) :=
    hMc.integrable_of_hasCompactSupport hMs
  have hfc : Continuous (fun u : ℝ => |deriv (deriv (pairWeight g a)) u|) := by
    rw [deriv2_pairWeight hg a]
    exact (((hc2.mul (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).add
      ((continuous_const.mul hc1).mul
        (Real.continuous_sinh.comp (continuous_const.mul continuous_id)))).add
      ((continuous_const.mul hc0).mul
        (Real.continuous_cosh.comp (continuous_const.mul continuous_id)))).const_mul (4:ℝ) |>.abs
  have hfi : MeasureTheory.Integrable (fun u : ℝ => |deriv (deriv (pairWeight g a)) u|) := by
    refine MeasureTheory.Integrable.mono' hMi hfc.aestronglyMeasurable ?_
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_deriv2_pairWeight_le hg hgc hR0 hsub ha u
  exact MeasureTheory.integral_mono hfi hMi (fun u => abs_deriv2_pairWeight_le hg hgc hR0 hsub ha u)

/-- **A single curvature constant works for every zero of the strip.** -/
theorem exists_uniform_pairWeightCurvature_bound (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    ∃ C : ℝ, ∀ a : ℝ, |a| ≤ 1/2 → pairWeightCurvature g a ≤ C := by
  obtain ⟨R, hR0, hsub⟩ := exists_ball_tsupport hgc
  exact ⟨_, fun a ha => pairWeightCurvature_le hg hgc hR0 hsub ha⟩


/-- Every zero of the critical strip has horizontal height at most `1/2` in
absolute value. -/
theorem abs_heightOf_le (ρ : Zeros) : |heightOf ρ| ≤ 1/2 := by
  obtain ⟨h0, h1⟩ := (Zeta23.zetaZeroConfig).strip (ρ : ℂ) ρ.2
  unfold heightOf
  rw [abs_le]
  constructor <;> linarith

/-- **The curvature constant can be chosen once and for all on the carrier.** -/
theorem exists_uniform_carrier_curvature_bound (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    ∃ C : ℝ, ∀ ρ : Zeros, pairWeightCurvature g (heightOf ρ) ≤ C := by
  obtain ⟨C, hC⟩ := exists_uniform_pairWeightCurvature_bound hg hgc
  exact ⟨C, fun ρ => hC _ (abs_heightOf_le ρ)⟩

end ReflectionPairCurvatureBound
end Zeta23Bridge
