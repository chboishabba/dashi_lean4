import Synthesis.RiemannFourthOrderLocalSignCompiler
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Fourth derivative of a compact hyperbolic-cosine transform

For a continuous compactly-supported real profile P define

  H_P(a) = integral P(u) cosh(a u) du.

Unlike the circular transform, cosh is not uniformly bounded for all a.
Differentiation is nevertheless local: on a in [a0-1,a0+1],

  |a| <= |a0|+1,

and compact support makes

  |P(u)| cosh((|a0|+1)|u|) |u|^n

an integrable majorant.  Hence

  H'    = integral P sinh(au) u,
  H''   = integral P cosh(au) u^2,
  H'''  = integral P sinh(au) u^3,
  H'''' = integral P cosh(au) u^4.

The fourth derivative is continuous by the same local domination argument
(encoded below via differentiability of H''' and continuity of derivatives).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real

namespace Synthesis

def compactCoshTransform (P : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ u : ℝ, P u * Real.cosh (a*u)

def compactCoshD1 (P : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ u : ℝ, P u * Real.sinh (a*u) * u

def compactCoshD2 (P : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ u : ℝ, P u * Real.cosh (a*u) * u^2

def compactCoshD3 (P : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ u : ℝ, P u * Real.sinh (a*u) * u^3

def compactCoshD4 (P : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ u : ℝ, P u * Real.cosh (a*u) * u^4

private theorem abs_le_abs_add_one_of_mem_local
    {a0 x : ℝ} (hx : x ∈ Icc (a0-1) (a0+1)) :
    |x| ≤ |a0| + 1 := by
  have hdiff : |x-a0| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  calc
    |x| = |(x-a0)+a0| := by ring_nf
    _ ≤ |x-a0| + |a0| := abs_add _ _
    _ ≤ |a0| + 1 := by linarith

private theorem cosh_local_bound
    {a0 x u : ℝ} (hx : x ∈ Icc (a0-1) (a0+1)) :
    Real.cosh (x*u)
      ≤ Real.cosh ((|a0|+1)*|u|) := by
  rw [Real.cosh_le_cosh]
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (|a0|+1)*|u|)]
  exact mul_le_mul_of_nonneg_right
    (abs_le_abs_add_one_of_mem_local hx) (abs_nonneg u)

private theorem abs_sinh_local_bound
    {a0 x u : ℝ} (hx : x ∈ Icc (a0-1) (a0+1)) :
    |Real.sinh (x*u)|
      ≤ Real.cosh ((|a0|+1)*|u|) := by
  rw [Real.abs_sinh]
  have hs : Real.sinh |x*u| < Real.cosh |x*u| :=
    Real.sinh_lt_cosh
  have hc :
      Real.cosh |x*u|
        ≤ Real.cosh ((|a0|+1)*|u|) := by
    rw [Real.cosh_le_cosh]
    rw [abs_of_nonneg (abs_nonneg (x*u)),
      abs_of_nonneg (by positivity : 0 ≤ (|a0|+1)*|u|),
      abs_mul]
    exact mul_le_mul_of_nonneg_right
      (abs_le_abs_add_one_of_mem_local hx) (abs_nonneg u)
  exact hs.le.trans hc

private theorem compactCoshMajorant_integrable
    {P : ℝ → ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (a0 : ℝ) (n : ℕ) :
    Integrable
      (fun u : ℝ =>
        |P u| * Real.cosh ((|a0|+1)*|u|) * |u|^n) := by
  exact
    ((hP.abs.mul (by fun_prop)).mul (continuous_abs.pow n))
      .integrable_of_hasCompactSupport
        ((hPc.abs.mul_right).mul_right)

private theorem compactCoshD0_hasDerivAt
    {P : ℝ → ℝ}
    (hP : Continuous P) (hPc : HasCompactSupport P)
    (a0 : ℝ) :
    HasDerivAt (compactCoshTransform P) (compactCoshD1 P a0) a0 := by
  let F : ℝ → ℝ → ℝ := fun a u => P u * Real.cosh (a*u)
  let F' : ℝ → ℝ → ℝ := fun a u => P u * Real.sinh (a*u) * u
  let bound : ℝ → ℝ := fun u =>
    |P u| * Real.cosh ((|a0|+1)*|u|) * |u|
  let s : Set ℝ := Icc (a0-1) (a0+1)
  have ha0 : a0 ∈ interior s := by
    dsimp [s]
    rw [interior_Icc]
    constructor <;> linarith
  have hFmeas :
      ∀ᶠ a in 𝓝 a0, AEStronglyMeasurable (F a) volume := by
    filter_upwards with a
    exact (by dsimp [F]; fun_prop : Continuous (F a)).aestronglyMeasurable
  have hFint : Integrable (F a0) volume := by
    dsimp [F]
    exact (by fun_prop : Continuous (F a0))
      |>.integrable_of_hasCompactSupport hPc.mul_right
  have hF'meas : AEStronglyMeasurable (F' a0) volume := by
    exact (by dsimp [F']; fun_prop : Continuous (F' a0)).aestronglyMeasurable
  have hbound : Integrable bound volume := by
    exact compactCoshMajorant_integrable hP hPc a0 1
  have hderiv :
      ∀ᵐ u ∂volume, ∀ a ∈ s, HasDerivAt (F · u) (F' a u) a := by
    filter_upwards with u
    intro a ha
    dsimp [F, F']
    fun_prop
  have hdom :
      ∀ᵐ u ∂volume, ∀ a ∈ s, ‖F' a u‖ ≤ bound u := by
    filter_upwards with u
    intro a ha
    dsimp [F', bound]
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hs := abs_sinh_local_bound (a0 := a0) (u := u) ha
    nlinarith [abs_nonneg (P u), abs_nonneg u,
      Real.cosh_pos ((|a0|+1)*|u|)]
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (F := F) (x₀ := a0)
      (s := s) (bound := bound)
      ha0 hFmeas hFint hF'meas hdom hbound hderiv
  simpa [compactCoshTransform, compactCoshD1, F, F'] using h.2

private theorem compactCoshD1_hasDerivAt
    {P : ℝ → ℝ}
    (hP : Continuous P) (hPc : HasCompactSupport P)
    (a0 : ℝ) :
    HasDerivAt (compactCoshD1 P) (compactCoshD2 P a0) a0 := by
  let F : ℝ → ℝ → ℝ := fun a u => P u * Real.sinh (a*u) * u
  let F' : ℝ → ℝ → ℝ := fun a u => P u * Real.cosh (a*u) * u^2
  let bound : ℝ → ℝ := fun u =>
    |P u| * Real.cosh ((|a0|+1)*|u|) * |u|^2
  let s : Set ℝ := Icc (a0-1) (a0+1)
  have ha0 : a0 ∈ interior s := by
    dsimp [s]; rw [interior_Icc]; constructor <;> linarith
  have hFmeas : ∀ᶠ a in 𝓝 a0, AEStronglyMeasurable (F a) volume := by
    filter_upwards with a
    exact (by dsimp [F]; fun_prop : Continuous (F a)).aestronglyMeasurable
  have hFint : Integrable (F a0) volume := by
    dsimp [F]
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hPc.mul_right).mul_right)
  have hF'meas : AEStronglyMeasurable (F' a0) volume := by
    exact (by dsimp [F']; fun_prop : Continuous (F' a0)).aestronglyMeasurable
  have hbound : Integrable bound volume :=
    compactCoshMajorant_integrable hP hPc a0 2
  have hderiv :
      ∀ᵐ u ∂volume, ∀ a ∈ s, HasDerivAt (F · u) (F' a u) a := by
    filter_upwards with u
    intro a ha
    dsimp [F, F']; fun_prop
  have hdom :
      ∀ᵐ u ∂volume, ∀ a ∈ s, ‖F' a u‖ ≤ bound u := by
    filter_upwards with u
    intro a ha
    dsimp [F', bound]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
      abs_of_pos (Real.cosh_pos (a*u))]
    have hc := cosh_local_bound (a0 := a0) (u := u) ha
    nlinarith [abs_nonneg (P u), abs_nonneg u]
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (F := F) (x₀ := a0)
      (s := s) (bound := bound)
      ha0 hFmeas hFint hF'meas hdom hbound hderiv
  simpa [compactCoshD1, compactCoshD2, F, F'] using h.2

private theorem compactCoshD2_hasDerivAt
    {P : ℝ → ℝ}
    (hP : Continuous P) (hPc : HasCompactSupport P)
    (a0 : ℝ) :
    HasDerivAt (compactCoshD2 P) (compactCoshD3 P a0) a0 := by
  let F : ℝ → ℝ → ℝ := fun a u => P u * Real.cosh (a*u) * u^2
  let F' : ℝ → ℝ → ℝ := fun a u => P u * Real.sinh (a*u) * u^3
  let bound : ℝ → ℝ := fun u =>
    |P u| * Real.cosh ((|a0|+1)*|u|) * |u|^3
  let s : Set ℝ := Icc (a0-1) (a0+1)
  have ha0 : a0 ∈ interior s := by
    dsimp [s]; rw [interior_Icc]; constructor <;> linarith
  have hFmeas : ∀ᶠ a in 𝓝 a0, AEStronglyMeasurable (F a) volume := by
    filter_upwards with a
    exact (by dsimp [F]; fun_prop : Continuous (F a)).aestronglyMeasurable
  have hFint : Integrable (F a0) volume := by
    dsimp [F]
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hPc.mul_right).mul_right)
  have hF'meas : AEStronglyMeasurable (F' a0) volume := by
    exact (by dsimp [F']; fun_prop : Continuous (F' a0)).aestronglyMeasurable
  have hbound : Integrable bound volume :=
    compactCoshMajorant_integrable hP hPc a0 3
  have hderiv :
      ∀ᵐ u ∂volume, ∀ a ∈ s, HasDerivAt (F · u) (F' a u) a := by
    filter_upwards with u
    intro a ha
    dsimp [F, F']; fun_prop
  have hdom :
      ∀ᵐ u ∂volume, ∀ a ∈ s, ‖F' a u‖ ≤ bound u := by
    filter_upwards with u
    intro a ha
    dsimp [F', bound]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    have hs := abs_sinh_local_bound (a0 := a0) (u := u) ha
    nlinarith [abs_nonneg (P u), abs_nonneg u,
      Real.cosh_pos ((|a0|+1)*|u|)]
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (F := F) (x₀ := a0)
      (s := s) (bound := bound)
      ha0 hFmeas hFint hF'meas hdom hbound hderiv
  simpa [compactCoshD2, compactCoshD3, F, F'] using h.2

private theorem compactCoshD3_hasDerivAt
    {P : ℝ → ℝ}
    (hP : Continuous P) (hPc : HasCompactSupport P)
    (a0 : ℝ) :
    HasDerivAt (compactCoshD3 P) (compactCoshD4 P a0) a0 := by
  let F : ℝ → ℝ → ℝ := fun a u => P u * Real.sinh (a*u) * u^3
  let F' : ℝ → ℝ → ℝ := fun a u => P u * Real.cosh (a*u) * u^4
  let bound : ℝ → ℝ := fun u =>
    |P u| * Real.cosh ((|a0|+1)*|u|) * |u|^4
  let s : Set ℝ := Icc (a0-1) (a0+1)
  have ha0 : a0 ∈ interior s := by
    dsimp [s]; rw [interior_Icc]; constructor <;> linarith
  have hFmeas : ∀ᶠ a in 𝓝 a0, AEStronglyMeasurable (F a) volume := by
    filter_upwards with a
    exact (by dsimp [F]; fun_prop : Continuous (F a)).aestronglyMeasurable
  have hFint : Integrable (F a0) volume := by
    dsimp [F]
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hPc.mul_right).mul_right)
  have hF'meas : AEStronglyMeasurable (F' a0) volume := by
    exact (by dsimp [F']; fun_prop : Continuous (F' a0)).aestronglyMeasurable
  have hbound : Integrable bound volume :=
    compactCoshMajorant_integrable hP hPc a0 4
  have hderiv :
      ∀ᵐ u ∂volume, ∀ a ∈ s, HasDerivAt (F · u) (F' a u) a := by
    filter_upwards with u
    intro a ha
    dsimp [F, F']; fun_prop
  have hdom :
      ∀ᵐ u ∂volume, ∀ a ∈ s, ‖F' a u‖ ≤ bound u := by
    filter_upwards with u
    intro a ha
    dsimp [F', bound]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
      abs_of_pos (Real.cosh_pos (a*u))]
    have hc := cosh_local_bound (a0 := a0) (u := u) ha
    nlinarith [abs_nonneg (P u), abs_nonneg u]
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (F := F) (x₀ := a0)
      (s := s) (bound := bound)
      ha0 hFmeas hFint hF'meas hdom hbound hderiv
  simpa [compactCoshD3, compactCoshD4, F, F'] using h.2

theorem compactCoshTransform_hasDerivAt
    {P : ℝ → ℝ} (hP : Continuous P) (hPc : HasCompactSupport P) (a : ℝ) :
    HasDerivAt (compactCoshTransform P) (compactCoshD1 P a) a :=
  compactCoshD0_hasDerivAt hP hPc a

theorem compactCoshD1_deriv
    {P : ℝ → ℝ} (hP : Continuous P) (hPc : HasCompactSupport P) (a : ℝ) :
    HasDerivAt (compactCoshD1 P) (compactCoshD2 P a) a :=
  compactCoshD1_hasDerivAt hP hPc a

theorem compactCoshD2_deriv
    {P : ℝ → ℝ} (hP : Continuous P) (hPc : HasCompactSupport P) (a : ℝ) :
    HasDerivAt (compactCoshD2 P) (compactCoshD3 P a) a :=
  compactCoshD2_hasDerivAt hP hPc a

theorem compactCoshD3_deriv
    {P : ℝ → ℝ} (hP : Continuous P) (hPc : HasCompactSupport P) (a : ℝ) :
    HasDerivAt (compactCoshD3 P) (compactCoshD4 P a) a :=
  compactCoshD3_hasDerivAt hP hPc a

/-- The fourth derivative is continuous because it is itself differentiable
locally after one more identical dominated-differentiation step.  For the
fourth-order sign compiler it suffices to prove continuity directly by local
dominated convergence; here we use a local Lipschitz estimate encoded through
the fifth sinh moment. -/
theorem compactCoshD4_continuous
    {P : ℝ → ℝ}
    (hP : Continuous P) (hPc : HasCompactSupport P) :
    Continuous (compactCoshD4 P) := by
  apply continuous_of_forall_continuousAt
  intro a0
  -- On a compact parameter neighbourhood, dominated convergence is supplied
  -- by differentiability of D4 with the fifth-moment local majorant.
  let D5 : ℝ → ℝ := fun a =>
    ∫ u : ℝ, P u * Real.sinh (a*u) * u^5
  have hderiv : HasDerivAt (compactCoshD4 P) (D5 a0) a0 := by
    let F : ℝ → ℝ → ℝ := fun a u => P u * Real.cosh (a*u) * u^4
    let F' : ℝ → ℝ → ℝ := fun a u => P u * Real.sinh (a*u) * u^5
    let bound : ℝ → ℝ := fun u =>
      |P u| * Real.cosh ((|a0|+1)*|u|) * |u|^5
    let s : Set ℝ := Icc (a0-1) (a0+1)
    have ha0 : a0 ∈ interior s := by
      dsimp [s]; rw [interior_Icc]; constructor <;> linarith
    have hFmeas : ∀ᶠ a in 𝓝 a0, AEStronglyMeasurable (F a) volume := by
      filter_upwards with a
      exact (by dsimp [F]; fun_prop : Continuous (F a)).aestronglyMeasurable
    have hFint : Integrable (F a0) volume := by
      dsimp [F]
      exact Continuous.integrable_of_hasCompactSupport
        (by fun_prop) ((hPc.mul_right).mul_right)
    have hF'meas : AEStronglyMeasurable (F' a0) volume := by
      exact (by dsimp [F']; fun_prop : Continuous (F' a0)).aestronglyMeasurable
    have hbound : Integrable bound volume :=
      compactCoshMajorant_integrable hP hPc a0 5
    have hpoint :
        ∀ᵐ u ∂volume, ∀ a ∈ s, HasDerivAt (F · u) (F' a u) a := by
      filter_upwards with u
      intro a ha
      dsimp [F, F']; fun_prop
    have hdom :
        ∀ᵐ u ∂volume, ∀ a ∈ s, ‖F' a u‖ ≤ bound u := by
      filter_upwards with u
      intro a ha
      dsimp [F', bound]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
      have hs := abs_sinh_local_bound (a0 := a0) (u := u) ha
      nlinarith [abs_nonneg (P u), abs_nonneg u,
        Real.cosh_pos ((|a0|+1)*|u|)]
    have h :=
      hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (μ := volume) (F := F) (x₀ := a0)
        (s := s) (bound := bound)
        ha0 hFmeas hFint hF'meas hdom hbound hpoint
    simpa [compactCoshD4, D5, F, F'] using h.2
  exact hderiv.continuousAt

end Synthesis
