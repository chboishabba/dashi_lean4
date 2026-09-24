import Synthesis.RiemannFourthOrderLocalSignCompiler
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Fourth derivative of a compact cosine transform

For a continuous compactly-supported real profile P define

  C_P(q) = integral P(u) cos(q u) du.

All polynomial moments of P are integrable, so differentiation under the
integral sign is valid four times:

  C'   = integral -P sin(qu) u,
  C''  = integral -P cos(qu) u^2,
  C''' = integral  P sin(qu) u^3,
  C''''= integral  P cos(qu) u^4.

The fourth derivative is globally Lipschitz with constant
integral |P(u)| |u|^5, hence continuous.

This is the analytic engine for converting projective moment cancellation into
an actual punctured sign theorem.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real

namespace Synthesis

def compactCosineTransform (P : ℝ → ℝ) (q : ℝ) : ℝ :=
  ∫ u : ℝ, P u * Real.cos (q*u)

def compactCosineD1 (P : ℝ → ℝ) (q : ℝ) : ℝ :=
  ∫ u : ℝ, - P u * Real.sin (q*u) * u

def compactCosineD2 (P : ℝ → ℝ) (q : ℝ) : ℝ :=
  ∫ u : ℝ, - P u * Real.cos (q*u) * u^2

def compactCosineD3 (P : ℝ → ℝ) (q : ℝ) : ℝ :=
  ∫ u : ℝ, P u * Real.sin (q*u) * u^3

def compactCosineD4 (P : ℝ → ℝ) (q : ℝ) : ℝ :=
  ∫ u : ℝ, P u * Real.cos (q*u) * u^4

def compactProfileAbsMoment (P : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ u : ℝ, |P u| * |u|^n

theorem compactProfile_absMoment_integrable
    {P : ℝ → ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (n : ℕ) :
    Integrable (fun u : ℝ => |P u| * |u|^n) := by
  exact (hP.abs.mul (continuous_abs.pow n)).integrable_of_hasCompactSupport
    (hPc.abs.mul_right)

private theorem compactCosineD0_hasDerivAt
    {P : ℝ → ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (q : ℝ) :
    HasDerivAt (compactCosineTransform P) (compactCosineD1 P q) q := by
  let F : ℝ → ℝ → ℝ := fun x u => P u * Real.cos (x*u)
  let F' : ℝ → ℝ → ℝ := fun x u => -P u * Real.sin (x*u) * u
  let bound : ℝ → ℝ := fun u => |P u| * |u|
  have hFmeas :
      ∀ᶠ x in 𝓝 q, AEStronglyMeasurable (F x) volume := by
    filter_upwards with x
    exact (by dsimp [F]; fun_prop :
      Continuous (fun u : ℝ => P u * Real.cos (x*u))).aestronglyMeasurable
  have hFint : Integrable (F q) volume := by
    dsimp [F]
    exact (hP.mul (by fun_prop)).integrable_of_hasCompactSupport hPc.mul_right
  have hF'meas : AEStronglyMeasurable (F' q) volume := by
    exact (by dsimp [F']; fun_prop :
      Continuous (fun u : ℝ => -P u * Real.sin (q*u) * u)).aestronglyMeasurable
  have hbound : Integrable bound volume := by
    exact compactProfile_absMoment_integrable hP hPc 1
  have hderiv :
      ∀ᵐ u ∂volume, ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivAt (F · u) (F' x u) x := by
    filter_upwards with u
    intro x hx
    dsimp [F, F']
    fun_prop
  have hdom :
      ∀ᵐ u ∂volume, ∀ x ∈ (Set.univ : Set ℝ),
        ‖F' x u‖ ≤ bound u := by
    filter_upwards with u
    intro x hx
    dsimp [F', bound]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg]
    have hs := Real.abs_sin_le_one (x*u)
    nlinarith [abs_nonneg (P u), abs_nonneg u]
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (F := F) (x₀ := q)
      (s := (Set.univ : Set ℝ)) (bound := bound)
      (by simp) hFmeas hFint hF'meas hdom hbound hderiv
  simpa [compactCosineTransform, compactCosineD1, F, F'] using h.2

private theorem compactCosineD1_hasDerivAt
    {P : ℝ → ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (q : ℝ) :
    HasDerivAt (compactCosineD1 P) (compactCosineD2 P q) q := by
  let F : ℝ → ℝ → ℝ := fun x u => -P u * Real.sin (x*u) * u
  let F' : ℝ → ℝ → ℝ := fun x u => -P u * Real.cos (x*u) * u^2
  let bound : ℝ → ℝ := fun u => |P u| * |u|^2
  have hFmeas :
      ∀ᶠ x in 𝓝 q, AEStronglyMeasurable (F x) volume := by
    filter_upwards with x
    exact (by dsimp [F]; fun_prop : Continuous (F x)).aestronglyMeasurable
  have hFint : Integrable (F q) volume := by
    dsimp [F]
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hPc.neg.mul_right).mul_right)
  have hF'meas : AEStronglyMeasurable (F' q) volume := by
    exact (by dsimp [F']; fun_prop : Continuous (F' q)).aestronglyMeasurable
  have hbound : Integrable bound volume :=
    compactProfile_absMoment_integrable hP hPc 2
  have hderiv :
      ∀ᵐ u ∂volume, ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivAt (F · u) (F' x u) x := by
    filter_upwards with u
    intro x hx
    dsimp [F, F']
    fun_prop
  have hdom :
      ∀ᵐ u ∂volume, ∀ x ∈ (Set.univ : Set ℝ),
        ‖F' x u‖ ≤ bound u := by
    filter_upwards with u
    intro x hx
    dsimp [F', bound]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_pow]
    have hc := Real.abs_cos_le_one (x*u)
    nlinarith [abs_nonneg (P u), abs_nonneg u]
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (F := F) (x₀ := q)
      (s := (Set.univ : Set ℝ)) (bound := bound)
      (by simp) hFmeas hFint hF'meas hdom hbound hderiv
  simpa [compactCosineD1, compactCosineD2, F, F'] using h.2

private theorem compactCosineD2_hasDerivAt
    {P : ℝ → ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (q : ℝ) :
    HasDerivAt (compactCosineD2 P) (compactCosineD3 P q) q := by
  let F : ℝ → ℝ → ℝ := fun x u => -P u * Real.cos (x*u) * u^2
  let F' : ℝ → ℝ → ℝ := fun x u => P u * Real.sin (x*u) * u^3
  let bound : ℝ → ℝ := fun u => |P u| * |u|^3
  have hFmeas :
      ∀ᶠ x in 𝓝 q, AEStronglyMeasurable (F x) volume := by
    filter_upwards with x
    exact (by dsimp [F]; fun_prop : Continuous (F x)).aestronglyMeasurable
  have hFint : Integrable (F q) volume := by
    dsimp [F]
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hPc.neg.mul_right).mul_right)
  have hF'meas : AEStronglyMeasurable (F' q) volume := by
    exact (by dsimp [F']; fun_prop : Continuous (F' q)).aestronglyMeasurable
  have hbound : Integrable bound volume :=
    compactProfile_absMoment_integrable hP hPc 3
  have hderiv :
      ∀ᵐ u ∂volume, ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivAt (F · u) (F' x u) x := by
    filter_upwards with u
    intro x hx
    dsimp [F, F']
    fun_prop
  have hdom :
      ∀ᵐ u ∂volume, ∀ x ∈ (Set.univ : Set ℝ),
        ‖F' x u‖ ≤ bound u := by
    filter_upwards with u
    intro x hx
    dsimp [F', bound]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    have hs := Real.abs_sin_le_one (x*u)
    nlinarith [abs_nonneg (P u), abs_nonneg u]
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (F := F) (x₀ := q)
      (s := (Set.univ : Set ℝ)) (bound := bound)
      (by simp) hFmeas hFint hF'meas hdom hbound hderiv
  simpa [compactCosineD2, compactCosineD3, F, F'] using h.2

private theorem compactCosineD3_hasDerivAt
    {P : ℝ → ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (q : ℝ) :
    HasDerivAt (compactCosineD3 P) (compactCosineD4 P q) q := by
  let F : ℝ → ℝ → ℝ := fun x u => P u * Real.sin (x*u) * u^3
  let F' : ℝ → ℝ → ℝ := fun x u => P u * Real.cos (x*u) * u^4
  let bound : ℝ → ℝ := fun u => |P u| * |u|^4
  have hFmeas :
      ∀ᶠ x in 𝓝 q, AEStronglyMeasurable (F x) volume := by
    filter_upwards with x
    exact (by dsimp [F]; fun_prop : Continuous (F x)).aestronglyMeasurable
  have hFint : Integrable (F q) volume := by
    dsimp [F]
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hPc.mul_right).mul_right)
  have hF'meas : AEStronglyMeasurable (F' q) volume := by
    exact (by dsimp [F']; fun_prop : Continuous (F' q)).aestronglyMeasurable
  have hbound : Integrable bound volume :=
    compactProfile_absMoment_integrable hP hPc 4
  have hderiv :
      ∀ᵐ u ∂volume, ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivAt (F · u) (F' x u) x := by
    filter_upwards with u
    intro x hx
    dsimp [F, F']
    fun_prop
  have hdom :
      ∀ᵐ u ∂volume, ∀ x ∈ (Set.univ : Set ℝ),
        ‖F' x u‖ ≤ bound u := by
    filter_upwards with u
    intro x hx
    dsimp [F', bound]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    have hc := Real.abs_cos_le_one (x*u)
    nlinarith [abs_nonneg (P u), abs_nonneg u]
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (F := F) (x₀ := q)
      (s := (Set.univ : Set ℝ)) (bound := bound)
      (by simp) hFmeas hFint hF'meas hdom hbound hderiv
  simpa [compactCosineD3, compactCosineD4, F, F'] using h.2

theorem compactCosineTransform_hasDerivAt
    {P : ℝ → ℝ} (hP : Continuous P) (hPc : HasCompactSupport P) (q : ℝ) :
    HasDerivAt (compactCosineTransform P) (compactCosineD1 P q) q :=
  compactCosineD0_hasDerivAt hP hPc q

theorem compactCosineD1_deriv
    {P : ℝ → ℝ} (hP : Continuous P) (hPc : HasCompactSupport P) (q : ℝ) :
    HasDerivAt (compactCosineD1 P) (compactCosineD2 P q) q :=
  compactCosineD1_hasDerivAt hP hPc q

theorem compactCosineD2_deriv
    {P : ℝ → ℝ} (hP : Continuous P) (hPc : HasCompactSupport P) (q : ℝ) :
    HasDerivAt (compactCosineD2 P) (compactCosineD3 P q) q :=
  compactCosineD2_hasDerivAt hP hPc q

theorem compactCosineD3_deriv
    {P : ℝ → ℝ} (hP : Continuous P) (hPc : HasCompactSupport P) (q : ℝ) :
    HasDerivAt (compactCosineD3 P) (compactCosineD4 P q) q :=
  compactCosineD3_hasDerivAt hP hPc q

theorem compactCosineD4_lipschitz
    {P : ℝ → ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (p q : ℝ) :
    |compactCosineD4 P q - compactCosineD4 P p|
      ≤ compactProfileAbsMoment P 5 * |q-p| := by
  unfold compactCosineD4
  have hiq :
      Integrable (fun u : ℝ => P u * Real.cos (q*u) * u^4) := by
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hPc.mul_right).mul_right)
  have hip :
      Integrable (fun u : ℝ => P u * Real.cos (p*u) * u^4) := by
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hPc.mul_right).mul_right)
  rw [← integral_sub hiq hip]
  have hdom :
      Integrable
        (fun u : ℝ => |q-p| * (|P u| * |u|^5)) :=
    (compactProfile_absMoment_integrable hP hPc 5).const_mul |q-p|
  calc
    |∫ u : ℝ,
      (P u * Real.cos (q*u) * u^4
        - P u * Real.cos (p*u) * u^4)|
      ≤
    ∫ u : ℝ,
      |P u * Real.cos (q*u) * u^4
        - P u * Real.cos (p*u) * u^4| :=
      abs_integral_le_integral_abs
    _ ≤
    ∫ u : ℝ, |q-p| * (|P u| * |u|^5) := by
      apply integral_mono (hiq.sub hip).abs hdom
      intro u
      have hc := Real.abs_cos_sub_cos_le (q*u) (p*u)
      have hfactor : |q*u-p*u| = |q-p| * |u| := by
        rw [← sub_mul, abs_mul]
      calc
        |P u * Real.cos (q*u) * u^4
          - P u * Real.cos (p*u) * u^4|
          = |P u| * |Real.cos (q*u)-Real.cos (p*u)| * |u|^4 := by
              ring_nf
              rw [abs_mul, abs_mul, abs_pow]
        _ ≤ |P u| * |q*u-p*u| * |u|^4 := by gcongr
        _ = |q-p| * (|P u| * |u|^5) := by
              rw [hfactor]
              ring
    _ = |q-p| * compactProfileAbsMoment P 5 := by
      rw [integral_const_mul]
      rfl
    _ = compactProfileAbsMoment P 5 * |q-p| := by ring

theorem compactCosineD4_continuous
    {P : ℝ → ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P) :
    Continuous (compactCosineD4 P) := by
  let K : NNReal :=
    ⟨compactProfileAbsMoment P 5,
      by unfold compactProfileAbsMoment; positivity⟩
  have hLip : LipschitzWith K (compactCosineD4 P) := by
    intro p q
    have h := compactCosineD4_lipschitz hP hPc p q
    simpa [K, Real.dist_eq, abs_sub_comm] using h
  exact hLip.continuous

end Synthesis
