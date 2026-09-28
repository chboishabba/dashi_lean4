import Synthesis.RiemannCompactCosineFourthDerivative

/-!
# Fifth derivative of the compact cosine transform

The quartic RH outer-discrepancy route needs four integrations by parts
starting from C'_P.  The existing derivative tower stops at C''''_P, so this
file adds exactly one more derivative:

  C'''''_P(q) = - ∫ P(u) sin(q u) u^5 du.

No new analytic assumption is required beyond continuity and compact support.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real

namespace Synthesis

def compactCosineD5 (P : ℝ → ℝ) (q : ℝ) : ℝ :=
  ∫ u : ℝ, - P u * Real.sin (q*u) * u^5

private theorem compactCosineD4_hasDerivAt
    {P : ℝ → ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (q : ℝ) :
    HasDerivAt (compactCosineD4 P) (compactCosineD5 P q) q := by
  let F : ℝ → ℝ → ℝ := fun x u => P u * Real.cos (x*u) * u^4
  let F' : ℝ → ℝ → ℝ := fun x u => -P u * Real.sin (x*u) * u^5
  let bound : ℝ → ℝ := fun u => |P u| * |u|^5
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
    compactProfile_absMoment_integrable hP hPc 5
  have hderiv :
      ∀ᵐ u ∂volume, ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivAt (F · u) (F' x u) x := by
    filter_upwards with u
    intro x hx
    dsimp [F,F']
    fun_prop
  have hdom :
      ∀ᵐ u ∂volume, ∀ x ∈ (Set.univ : Set ℝ),
        ‖F' x u‖ ≤ bound u := by
    filter_upwards with u
    intro x hx
    dsimp [F',bound]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_pow]
    have hs := Real.abs_sin_le_one (x*u)
    nlinarith [abs_nonneg (P u), abs_nonneg u]
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (F := F) (x₀ := q)
      (s := (Set.univ : Set ℝ)) (bound := bound)
      (by simp) hFmeas hFint hF'meas hdom hbound hderiv
  simpa [compactCosineD4,compactCosineD5,F,F'] using h.2

theorem compactCosineD4_deriv
    {P : ℝ → ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (q : ℝ) :
    HasDerivAt (compactCosineD4 P) (compactCosineD5 P q) q :=
  compactCosineD4_hasDerivAt hP hPc q

theorem compactCosineD5_continuous
    {P : ℝ → ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P) :
    Continuous (compactCosineD5 P) := by
  apply continuous_iff_continuousAt.2
  intro q
  let G : ℝ → ℝ := fun u => P u * u^5
  have hG : Continuous G := by
    dsimp [G]
    fun_prop
  have hGc : HasCompactSupport G := hPc.mul_right
  have h :
      Continuous (fun q : ℝ => ∫ u : ℝ, G u * Real.sin (q*u)) := by
    apply continuous_iff_continuousAt.2
    intro x
    have hD :=
      compactCosineTransform_hasDerivAt hG hGc x
    exact hD.continuousAt
  simpa [compactCosineD5,G,compactCosineD1] using h.neg

theorem compactCosineD5_abs_le_absMomentFive
    {P : ℝ → ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (q : ℝ) :
    |compactCosineD5 P q| ≤ compactProfileAbsMoment P 5 := by
  have hi :
      Integrable (fun u : ℝ => -P u * Real.sin (q*u) * u^5) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hPc.neg.mul_right).mul_right)
  have hia :
      Integrable (fun u : ℝ => |P u| * |u|^5) :=
    compactProfile_absMoment_integrable hP hPc 5
  unfold compactCosineD5 compactProfileAbsMoment
  calc
    |∫ u : ℝ, -P u * Real.sin (q*u) * u^5|
      ≤ ∫ u : ℝ, |-P u * Real.sin (q*u) * u^5| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ u : ℝ, |P u| * |u|^5 := by
      apply integral_mono hi.abs hia
      intro u
      rw [abs_mul,abs_mul,abs_neg,abs_pow]
      have hs := Real.abs_sin_le_one (q*u)
      nlinarith [abs_nonneg (P u), abs_nonneg u]
    _ = ∫ u : ℝ, |P u| * |u|^5 := rfl

end Synthesis
