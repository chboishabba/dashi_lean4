import Synthesis.RiemannProjectiveQuarticFourWindowUniformPoleLocalization
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform high-t equicontinuity of the normalized pole weights

For t>=200 and c in {1,2}, on the fixed interval [-6,6], write

  w_{t,c}(v) = cosh(8v/t) * (cos(16v) cos(cv)).

The hyperbolic factor is bounded by cosh(1), and its derivative has norm at
most cosh(1).  The circular product is 18-Lipschitz when |c|<=2.  Therefore

  |w_{t,c}(u)-w_{t,c}(v)| <= 19*cosh(1)*|u-v|.

All four bump centres 0,pi/3,pi/2,pi and every radius R<1 lie inside this fixed
interval.  This pays the equicontinuity input that was responsible for the
`t`-dependent localization radius in the older proof.
-/

noncomputable section
namespace Synthesis

open Set
open scoped Real

def quarticFourUniformPoleLipschitzConstant : ℝ := 19 * Real.cosh 1

theorem quarticFourUniformPoleLipschitzConstant_pos :
    0 < quarticFourUniformPoleLipschitzConstant := by
  unfold quarticFourUniformPoleLipschitzConstant
  positivity

private theorem abs_le_six_of_mem_Icc {x : ℝ}
    (hx : x ∈ Set.Icc (-6 : ℝ) 6) : |x| <= 6 := by
  rw [abs_le]
  exact hx

private theorem quarticPoleCosh_argument_abs_le_one
    {t x : ℝ} (ht : 200 <= t)
    (hx : x ∈ Set.Icc (-6 : ℝ) 6) :
    |8*x/t| <= 1 := by
  have ht0 : 0 < t := by linarith
  have hxabs := abs_le_six_of_mem_Icc hx
  rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) <= 8),
      abs_of_pos ht0]
  rw [div_le_one ht0]
  nlinarith

private theorem quarticPoleCosh_le_one
    {t x : ℝ} (ht : 200 <= t)
    (hx : x ∈ Set.Icc (-6 : ℝ) 6) :
    Real.cosh (8*x/t) <= Real.cosh 1 := by
  rw [Real.cosh_le_cosh]
  simpa using quarticPoleCosh_argument_abs_le_one ht hx

private theorem quarticPoleCosh_deriv_abs_le_oneCosh
    {t x : ℝ} (ht : 200 <= t)
    (hx : x ∈ Set.Icc (-6 : ℝ) 6) :
    |deriv (fun v : ℝ => Real.cosh (8*v/t)) x| <= Real.cosh 1 := by
  have ht0 : 0 < t := by linarith
  have harg := quarticPoleCosh_argument_abs_le_one ht hx
  have hderiv :
      deriv (fun v : ℝ => Real.cosh (8*v/t)) x
        = (8/t) * Real.sinh (8*x/t) := by
    have hlin : HasDerivAt (fun v : ℝ => 8*v/t) (8/t) x := by
      convert (hasDerivAt_id x).const_mul (8/t) using 1 <;> ring
    exact ((Real.hasDerivAt_cosh (8*x/t)).comp x hlin).deriv
  rw [hderiv, abs_mul]
  have h8 : |8/t| <= 1 := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) <= 8), abs_of_pos ht0,
        div_le_one ht0]
    linarith
  have hsinh : |Real.sinh (8*x/t)| <= Real.cosh 1 := by
    rw [Real.abs_sinh]
    have hs := Real.sinh_lt_cosh (x := |8*x/t|)
    have hc : Real.cosh |8*x/t| <= Real.cosh 1 := by
      rw [Real.cosh_le_cosh]
      simpa [abs_abs] using harg
    exact (le_of_lt hs).trans hc
  calc
    |8/t| * |Real.sinh (8*x/t)|
      <= 1 * Real.cosh 1 :=
        mul_le_mul h8 hsinh (abs_nonneg _) (by norm_num)
    _ = Real.cosh 1 := one_mul _

/-- The high-t hyperbolic factor is uniformly cosh(1)-Lipschitz on [-6,6]. -/
theorem quarticPoleCosh_sub_abs_le
    {t u v : ℝ} (ht : 200 <= t)
    (hu : u ∈ Set.Icc (-6 : ℝ) 6)
    (hv : v ∈ Set.Icc (-6 : ℝ) 6) :
    |Real.cosh (8*u/t) - Real.cosh (8*v/t)|
      <= Real.cosh 1 * |u-v| := by
  have hdiff : ∀ x ∈ Set.Icc (-6 : ℝ) 6,
      DifferentiableAt ℝ (fun y : ℝ => Real.cosh (8*y/t)) x := by
    intro x hx
    fun_prop
  have hbound : ∀ x ∈ Set.Icc (-6 : ℝ) 6,
      ‖deriv (fun y : ℝ => Real.cosh (8*y/t)) x‖ <= Real.cosh 1 := by
    intro x hx
    simpa [Real.norm_eq_abs] using quarticPoleCosh_deriv_abs_le_oneCosh ht hx
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    hdiff hbound (convex_Icc (-6 : ℝ) 6) hv hu
  simpa [Real.norm_eq_abs, abs_sub_comm] using h

private theorem quarticPoleCircularProduct_sub_abs_le
    {c u v : ℝ} (hc : |c| <= 2) :
    |Real.cos (16*u) * Real.cos (c*u)
      - Real.cos (16*v) * Real.cos (c*v)|
      <= 18 * |u-v| := by
  have h16 := Real.abs_cos_sub_cos_le (16*u) (16*v)
  have hc0 := Real.abs_cos_sub_cos_le (c*u) (c*v)
  have hcu : |Real.cos (c*u)| <= 1 := by
    rw [abs_le]
    exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hcv : |Real.cos (16*v)| <= 1 := by
    rw [abs_le]
    exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hsplit :
      Real.cos (16*u) * Real.cos (c*u)
        - Real.cos (16*v) * Real.cos (c*v)
      =
      (Real.cos (16*u)-Real.cos (16*v))*Real.cos (c*u)
        + Real.cos (16*v)*(Real.cos (c*u)-Real.cos (c*v)) := by ring
  rw [hsplit]
  calc
    |(Real.cos (16*u)-Real.cos (16*v))*Real.cos (c*u)
        + Real.cos (16*v)*(Real.cos (c*u)-Real.cos (c*v))|
      <= |Real.cos (16*u)-Real.cos (16*v)| * |Real.cos (c*u)|
        + |Real.cos (16*v)| * |Real.cos (c*u)-Real.cos (c*v)| := by
          rw [abs_mul, abs_mul]
          exact abs_add _ _
    _ <= |16*u-16*v| + |c*u-c*v| := by
      have h1 : |Real.cos (16*u)-Real.cos (16*v)| * |Real.cos (c*u)|
          <= |16*u-16*v| := by
        calc
          _ <= |Real.cos (16*u)-Real.cos (16*v)| * 1 :=
            mul_le_mul_of_nonneg_left hcu (abs_nonneg _)
          _ <= |16*u-16*v| := by simpa using h16
      have h2 : |Real.cos (16*v)| * |Real.cos (c*u)-Real.cos (c*v)|
          <= |c*u-c*v| := by
        calc
          _ <= 1 * |Real.cos (c*u)-Real.cos (c*v)| :=
            mul_le_mul_of_nonneg_right hcv (abs_nonneg _)
          _ <= |c*u-c*v| := by simpa using hc0
      linarith
    _ = 16*|u-v| + |c|*|u-v| := by
      rw [show 16*u-16*v = 16*(u-v) by ring,
          show c*u-c*v = c*(u-v) by ring,
          abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) <= 16)]
      ring
    _ <= 18*|u-v| := by
      have hd : 0 <= |u-v| := abs_nonneg _
      nlinarith

/-- Uniform equicontinuity of the actual t-dependent pole weight. -/
theorem quarticFourNormalizedPoleWeight_sub_abs_le_uniform
    {t c u v : ℝ}
    (ht : 200 <= t)
    (hc : |c| <= 2)
    (hu : u ∈ Set.Icc (-6 : ℝ) 6)
    (hv : v ∈ Set.Icc (-6 : ℝ) 6) :
    |quarticFourNormalizedPoleWeight t c u
      - quarticFourNormalizedPoleWeight t c v|
      <= quarticFourUniformPoleLipschitzConstant * |u-v| := by
  let H : ℝ -> ℝ := fun x => Real.cosh (8*x/t)
  let C : ℝ -> ℝ := fun x => Real.cos (16*x) * Real.cos (c*x)
  have hH := quarticPoleCosh_sub_abs_le ht hu hv
  have hC := quarticPoleCircularProduct_sub_abs_le hc (u:=u) (v:=v)
  have hHu : 0 <= H u := (Real.cosh_pos _).le
  have hHv : H v <= Real.cosh 1 := quarticPoleCosh_le_one ht hv
  have hCu : |C u| <= 1 := by
    dsimp [C]
    rw [abs_mul]
    have h1 : |Real.cos (16*u)| <= 1 := by
      rw [abs_le]; exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    have h2 : |Real.cos (c*u)| <= 1 := by
      rw [abs_le]; exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    nlinarith [abs_nonneg (Real.cos (16*u)), abs_nonneg (Real.cos (c*u))]
  have hsplit : H u*C u - H v*C v = (H u-H v)*C u + H v*(C u-C v) := by ring
  unfold quarticFourNormalizedPoleWeight
  change |H u*C u-H v*C v| <= _
  rw [hsplit]
  calc
    |(H u-H v)*C u + H v*(C u-C v)|
      <= |H u-H v|*|C u| + |H v|*|C u-C v| := by
        rw [abs_mul, abs_mul]
        exact abs_add _ _
    _ <= Real.cosh 1*|u-v| + Real.cosh 1*(18*|u-v|) := by
      have hHvAbs : |H v| <= Real.cosh 1 := by
        rw [abs_of_nonneg (Real.cosh_pos _).le]
        exact hHv
      exact add_le_add
        (calc
          |H u-H v|*|C u| <= |H u-H v|*1 :=
            mul_le_mul_of_nonneg_left hCu (abs_nonneg _)
          _ <= Real.cosh 1*|u-v| := by simpa using hH)
        (mul_le_mul hHvAbs hC (abs_nonneg _) (Real.cosh_pos _).le)
    _ = quarticFourUniformPoleLipschitzConstant*|u-v| := by
      unfold quarticFourUniformPoleLipschitzConstant
      ring

end Synthesis
