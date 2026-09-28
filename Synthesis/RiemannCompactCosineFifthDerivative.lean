import Synthesis.RiemannCompactCosineFourthDerivative
import Zeta23Bridge.OscillatoryKernelDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

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


open Zeta23Bridge.OscillatoryKernelDecay

def compactSineTransform (P : ℝ → ℝ) (q : ℝ) : ℝ :=
  ∫ u : ℝ, P u * Real.sin (q*u)

def compactSineSecondDerivativeMass
    (P : ℝ → ℝ) : ℝ :=
  ∫ u : ℝ, |deriv (deriv P) u|

theorem compactSineTransform_abs_le_profileMass
    {P : ℝ → ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (q : ℝ) :
    |compactSineTransform P q|
      <= compactProfileAbsMoment P 0 := by
  have hi :
      Integrable (fun u : ℝ => P u * Real.sin (q*u)) :=
    (hP.mul (by fun_prop)).integrable_of_hasCompactSupport hPc.mul_right
  have hia :
      Integrable (fun u : ℝ => |P u|) :=
    hP.abs.integrable_of_hasCompactSupport hPc.abs
  unfold compactSineTransform compactProfileAbsMoment
  calc
    |∫ u : ℝ, P u * Real.sin (q*u)|
      <= ∫ u : ℝ, |P u * Real.sin (q*u)| :=
        abs_integral_le_integral_abs
    _ <= ∫ u : ℝ, |P u| := by
      apply integral_mono hi.abs hia
      intro u
      rw [abs_mul]
      exact mul_le_of_le_one_right
        (abs_nonneg (P u)) (Real.abs_sin_le_one (q*u))
    _ = ∫ u : ℝ, |P u| * |u|^0 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by simp

theorem compactSineTransform_abs_le_invSq
    {P : ℝ → ℝ}
    (hP : ContDiff ℝ 2 P)
    (hPc : HasCompactSupport P)
    {q : ℝ}
    (hq : q ≠ 0) :
    |compactSineTransform P q|
      <= compactSineSecondDerivativeMass P / q^2 := by
  have hP1 : ContDiff ℝ 1 P := hP.of_le (by norm_num)
  have hPd1 : ContDiff ℝ 1 (deriv P) := ContDiff.deriv' hP
  have h1 := integral_mul_sin_eq hP1 hPc hq
  have h2 := integral_mul_cos_eq hPd1 hPc.deriv hq
  have hsecond :
      (∫ u : ℝ, P u * Real.sin (q*u))
        =
      -(1/q^2) *
        ∫ u : ℝ, deriv (deriv P) u * Real.sin (q*u) := by
    rw [h1,h2]
    field_simp [hq]
    ring
  have hd2c : Continuous (deriv (deriv P)) :=
    hPd1.continuous_deriv le_rfl
  have hd2s : HasCompactSupport (deriv (deriv P)) :=
    hPc.deriv.deriv
  have hi :
      Integrable
        (fun u : ℝ => deriv (deriv P) u * Real.sin (q*u)) :=
    Continuous.integrable_of_hasCompactSupport
      (hd2c.mul (by fun_prop)) hd2s.mul_right
  have hiabs :
      Integrable (fun u : ℝ => |deriv (deriv P) u|) :=
    hd2c.abs.integrable_of_hasCompactSupport hd2s.abs
  have hbound :
      |∫ u : ℝ, deriv (deriv P) u * Real.sin (q*u)|
        <= ∫ u : ℝ, |deriv (deriv P) u| := by
    calc
      |∫ u : ℝ, deriv (deriv P) u * Real.sin (q*u)|
        <=
      ∫ u : ℝ,
        |deriv (deriv P) u * Real.sin (q*u)| :=
          abs_integral_le_integral_abs
      _ <= ∫ u : ℝ, |deriv (deriv P) u| := by
        apply integral_mono hi.abs hiabs
        intro u
        rw [abs_mul]
        exact mul_le_of_le_one_right
          (abs_nonneg _) (Real.abs_sin_le_one _)
  unfold compactSineTransform
  rw [hsecond, abs_mul, abs_neg,
      abs_of_nonneg (by positivity : 0 <= 1/q^2)]
  unfold compactSineSecondDerivativeMass
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

theorem compactSineTransform_continuous
    {P : ℝ → ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P) :
    Continuous (compactSineTransform P) := by
  apply continuous_iff_continuousAt.2
  intro q
  let G : ℝ → ℝ := fun u => P u * u
  have hG : Continuous G := by
    dsimp [G]
    fun_prop
  have hGc : HasCompactSupport G := hPc.mul_right
  have hD :=
    compactCosineTransform_hasDerivAt hP hPc q
  unfold compactSineTransform
  have hEq :
      (∫ u : ℝ, P u * Real.sin (q*u))
        =
      - compactCosineD1 P q := by
    unfold compactCosineD1
    rw [← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by ring
  rw [hEq]
  exact (compactCosineD1_deriv hP hPc q).continuousAt.neg

theorem compactSineTransform_integrable
    {P : ℝ → ℝ}
    (hP : ContDiff ℝ 2 P)
    (hPc : HasCompactSupport P) :
    Integrable (compactSineTransform P) := by
  let M0 : ℝ := compactProfileAbsMoment P 0
  let M2 : ℝ := compactSineSecondDerivativeMass P
  let K : ℝ := 2 * (M0 + M2)
  have hPcont : Continuous P := hP.continuous
  have hM0 : 0 <= M0 := by
    dsimp [M0, compactProfileAbsMoment]
    positivity
  have hM2 : 0 <= M2 := by
    dsimp [M2, compactSineSecondDerivativeMass]
    positivity
  have hmajor :
      ∀ q : ℝ,
        |compactSineTransform P q|
          <= K * (1 + q^2)⁻¹ := by
    intro q
    have hmass :=
      compactSineTransform_abs_le_profileMass hPcont hPc q
    by_cases hq : |q| <= 1
    · have hq2 : q^2 <= 1 := by
        nlinarith [sq_nonneg q]
      have hden : 0 < 1 + q^2 := by positivity
      have hhalf :
          (1/2 : ℝ) <= (1 + q^2)⁻¹ := by
        rw [le_inv_iff₀ hden]
        nlinarith
      dsimp [K]
      have hscale :=
        mul_le_mul_of_nonneg_left hhalf
          (by positivity : 0 <= 2*(M0+M2))
      nlinarith
    · have hqgt : 1 < |q| := lt_of_not_ge hq
      have hq0 : q ≠ 0 := by
        intro hz
        rw [hz, abs_zero] at hqgt
        linarith
      have hdec :=
        compactSineTransform_abs_le_invSq hP hPc hq0
      have hq2 : 1 < q^2 := by
        nlinarith [sq_abs q]
      have hden : 0 < 1 + q^2 := by positivity
      have hinv :
          1 / q^2 <= 2 * (1 + q^2)⁻¹ := by
        rw [div_eq_mul_inv]
        have hq2pos : 0 < q^2 := by positivity
        rw [inv_le_iff₀ hq2pos]
        field_simp [ne_of_gt hden, ne_of_gt hq2pos]
        nlinarith
      dsimp [M2] at hdec
      dsimp [K]
      have hm :=
        mul_le_mul_of_nonneg_left hinv hM2
      calc
        |compactSineTransform P q|
          <= M2 / q^2 := hdec
        _ <= 2*M2*(1+q^2)⁻¹ := by
          simpa [div_eq_mul_inv, mul_assoc] using hm
        _ <= 2*(M0+M2)*(1+q^2)⁻¹ := by
          have hweight : 0 <= (1+q^2)⁻¹ := by positivity
          nlinarith
  have hmajInt :
      Integrable (fun q : ℝ => K * (1+q^2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul K
  have hS :
      Continuous (compactSineTransform P) :=
    compactSineTransform_continuous hPcont hPc
  exact hmajInt.mono'
    hS.aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs]
      have hkq : 0 <= K * (1+q^2)⁻¹ := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hkq]
      exact hmajor q)

theorem compactCosineD5_integrable
    {P : ℝ → ℝ}
    (hP : ContDiff ℝ 2 P)
    (hPc : HasCompactSupport P) :
    Integrable (compactCosineD5 P) := by
  let G : ℝ → ℝ := fun u => -P u * u^5
  have hG : ContDiff ℝ 2 G := by
    dsimp [G]
    exact hP.neg.mul (contDiff_id.pow 5)
  have hGc : HasCompactSupport G := hPc.neg.mul_right
  have hS := compactSineTransform_integrable hG hGc
  simpa [compactCosineD5, compactSineTransform, G] using hS

end Synthesis
