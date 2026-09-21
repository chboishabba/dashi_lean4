import Synthesis.RiemannNormalizedProjectiveBaseCurvature
import Synthesis.RiemannNormalizedProjectiveBaseTransformDerivativeRegularity
import Synthesis.RiemannNormalizedProjectiveRvMAbelResidualBound
import Synthesis.RiemannNormalizedProjectiveOffInfiniteSplit

/-!
# Local positive lobe of the canonical projective base transform

The signed second moment theorem gives Phi_t''(0)>0.  This file upgrades that
pointwise curvature to an actual punctured positive band.

This is analytically important for the Goal-1 frontier.  It proves that the
canonical q-only projective kernel itself cannot satisfy the hoped-for local
pointwise inequality Phi_t(q)<=0 after deleting q=0.  Any successful one-sided
N-mu theorem must therefore exploit the signed interaction with the counting
discrepancy (or change the target-dependent test family); it cannot come from a
fixed-sign kernel near the removed same-ordinate fibre.
-/

noncomputable section

open MeasureTheory Set
open scoped Real Topology

namespace Synthesis

def normalizedProjectiveProfileThirdAbsMoment (t : ℝ) : ℝ :=
  ∫ v : ℝ, |normalizedProjectivePhysicalProfile t v| * |v|^3

theorem normalizedProjectiveProfileThirdAbsMoment_nonneg (t : ℝ) :
    0 ≤ normalizedProjectiveProfileThirdAbsMoment t := by
  unfold normalizedProjectiveProfileThirdAbsMoment
  positivity

theorem normalizedProjectiveProfile_thirdAbsMoment_integrable (t : ℝ) :
    Integrable
      (fun v : ℝ =>
        |normalizedProjectivePhysicalProfile t v| * |v|^3) := by
  exact
    ((normalizedProjectivePhysicalProfile_continuous t).abs.mul
      (continuous_abs.pow 3)).integrable_of_hasCompactSupport
      ((normalizedProjectivePhysicalProfile_compact t).abs.mul_right)

theorem normalizedProjectiveBaseTransformSecondDeriv_lipschitz
    (t p q : ℝ) :
    |normalizedProjectiveBaseTransformSecondDeriv t q
      - normalizedProjectiveBaseTransformSecondDeriv t p|
      ≤ normalizedProjectiveProfileThirdAbsMoment t * |q-p| := by
  unfold normalizedProjectiveBaseTransformSecondDeriv
  have hiq :
      Integrable
        (fun v : ℝ =>
          - normalizedProjectivePhysicalProfile t v
            * Real.cos (q*v) * v^2) := by
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      (((normalizedProjectivePhysicalProfile_compact t).neg.mul_right).mul_right)
  have hip :
      Integrable
        (fun v : ℝ =>
          - normalizedProjectivePhysicalProfile t v
            * Real.cos (p*v) * v^2) := by
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      (((normalizedProjectivePhysicalProfile_compact t).neg.mul_right).mul_right)
  rw [← integral_sub hiq hip]
  have hdom :
      Integrable
        (fun v : ℝ =>
          |q-p| *
            (|normalizedProjectivePhysicalProfile t v| * |v|^3)) :=
    (normalizedProjectiveProfile_thirdAbsMoment_integrable t).const_mul |q-p|
  calc
    |∫ v : ℝ,
      (- normalizedProjectivePhysicalProfile t v * Real.cos (q*v) * v^2
        -
       (- normalizedProjectivePhysicalProfile t v * Real.cos (p*v) * v^2))|
      ≤
    ∫ v : ℝ,
      |(- normalizedProjectivePhysicalProfile t v * Real.cos (q*v) * v^2
        -
       (- normalizedProjectivePhysicalProfile t v * Real.cos (p*v) * v^2))| :=
      abs_integral_le_integral_abs
    _ ≤
    ∫ v : ℝ,
      |q-p| *
        (|normalizedProjectivePhysicalProfile t v| * |v|^3) := by
      apply integral_mono (hiq.sub hip).abs hdom
      intro v
      have hc := Real.abs_cos_sub_cos_le (q*v) (p*v)
      have hfactor : |q*v-p*v| = |q-p| * |v| := by
        rw [← sub_mul, abs_mul]
      calc
        |(- normalizedProjectivePhysicalProfile t v * Real.cos (q*v) * v^2
          -
         (- normalizedProjectivePhysicalProfile t v * Real.cos (p*v) * v^2))|
          =
        |normalizedProjectivePhysicalProfile t v|
          * |Real.cos (q*v)-Real.cos (p*v)| * |v|^2 := by
            ring_nf
            rw [abs_mul, abs_mul, abs_neg, abs_pow]
        _ ≤
        |normalizedProjectivePhysicalProfile t v| * |q*v-p*v| * |v|^2 := by
          gcongr
        _ =
        |q-p| *
          (|normalizedProjectivePhysicalProfile t v| * |v|^3) := by
            rw [hfactor]
            ring
    _ =
      |q-p| * normalizedProjectiveProfileThirdAbsMoment t := by
        rw [integral_const_mul]
        rfl
    _ =
      normalizedProjectiveProfileThirdAbsMoment t * |q-p| := by ring

theorem normalizedProjectiveBaseTransformSecondDeriv_continuous
    (t : ℝ) :
    Continuous (normalizedProjectiveBaseTransformSecondDeriv t) := by
  let K : NNReal :=
    ⟨normalizedProjectiveProfileThirdAbsMoment t,
      normalizedProjectiveProfileThirdAbsMoment_nonneg t⟩
  have hLip :
      LipschitzWith K (normalizedProjectiveBaseTransformSecondDeriv t) := by
    intro p q
    have h :=
      normalizedProjectiveBaseTransformSecondDeriv_lipschitz t p q
    simpa [K, Real.dist_eq, abs_sub_comm] using h
  exact hLip.continuous

theorem normalizedProjectiveBaseTransformDeriv_zero (t : ℝ) :
    normalizedProjectiveBaseTransformDeriv t 0 = 0 := by
  unfold normalizedProjectiveBaseTransformDeriv
  simp

/--
For every high canonical parameter t there is a genuine right-hand punctured
band on which the q-only projective base transform is strictly positive.
-/
theorem exists_normalizedProjectiveBaseTransform_pos_right
    {t : ℝ} (ht : 18 ≤ t) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ q : ℝ, 0 < q → q < eps →
        0 < normalizedProjectiveBaseTransform t q := by
  have hcurv :
      0 < normalizedProjectiveBaseTransformSecondDeriv t 0 :=
    normalizedProjectiveBaseTransformSecondDeriv_zero_pos ht
  have hopen :
      IsOpen {q : ℝ | 0 < normalizedProjectiveBaseTransformSecondDeriv t q} :=
    isOpen_lt continuous_const
      (normalizedProjectiveBaseTransformSecondDeriv_continuous t)
  have hmem :
      (0 : ℝ) ∈ {q : ℝ |
        0 < normalizedProjectiveBaseTransformSecondDeriv t q} := hcurv
  obtain ⟨eps, heps, hball⟩ :=
    (Metric.isOpen_iff.1 hopen) 0 hmem

  have hsecond :
      ∀ x : ℝ, |x| < eps →
        0 < normalizedProjectiveBaseTransformSecondDeriv t x := by
    intro x hx
    apply hball
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx

  have hDerivMono :
      StrictMonoOn (normalizedProjectiveBaseTransformDeriv t)
        (Set.Icc 0 eps) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 eps)
    · exact
        (normalizedProjectiveBaseTransformDeriv_continuous t).continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      rw [(normalizedProjectiveBaseTransformDeriv_hasDerivAt t x).deriv]
      apply hsecond x
      rw [abs_of_pos hx.1]
      exact hx.2

  have hBaseMono :
      StrictMonoOn (normalizedProjectiveBaseTransform t)
        (Set.Icc 0 eps) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 eps)
    · exact
        (continuous_of_forall_continuousAt fun x =>
          (normalizedProjectiveBaseTransform_hasDerivAt t x).continuousAt).continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      rw [(normalizedProjectiveBaseTransform_hasDerivAt t x).deriv]
      have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) eps := by
        exact ⟨le_rfl, heps.le⟩
      have hxmem : x ∈ Set.Icc (0 : ℝ) eps := ⟨hx.1.le, hx.2.le⟩
      have hinc := hDerivMono h0mem hxmem hx.1
      rw [normalizedProjectiveBaseTransformDeriv_zero] at hinc
      exact hinc

  refine ⟨eps, heps, ?_⟩
  intro q hq0 hqeps
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) eps := ⟨le_rfl, heps.le⟩
  have hqmem : q ∈ Set.Icc (0 : ℝ) eps := ⟨hq0.le, hqeps.le⟩
  have hinc := hBaseMono h0mem hqmem hq0
  rw [normalizedProjectiveBaseTransform_zero (by linarith : 0 < t)] at hinc
  exact hinc

/-- Evenness turns the right-hand positive lobe into a two-sided punctured band. -/
theorem exists_normalizedProjectiveBaseTransform_pos_punctured
    {t : ℝ} (ht : 18 ≤ t) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ q : ℝ, 0 < |q| → |q| < eps →
        0 < normalizedProjectiveBaseTransform t q := by
  obtain ⟨eps, heps, hright⟩ :=
    exists_normalizedProjectiveBaseTransform_pos_right ht
  refine ⟨eps, heps, ?_⟩
  intro q hq0 hqeps
  by_cases hq : 0 ≤ q
  · have habs : |q| = q := abs_of_nonneg hq
    rw [habs] at hq0 hqeps
    exact hright q hq0 hqeps
  · have hqneg : q < 0 := lt_of_not_ge hq
    have habs : |q| = -q := abs_of_neg hqneg
    have hp := hright (-q) (by linarith) (by simpa [habs] using hqeps)
    rw [normalizedProjectiveBaseTransform_neg] at hp
    exact hp

/--
The same local positive lobe appears on the actual atomic zero carrier:
every zero with sufficiently small but nonzero normalized ordinate gap contributes
a strictly positive q-only base source term.
-/
theorem exists_normalizedProjectiveBaseSourceTerm_pos_punctured
    {t : ℝ} (ht : 18 ≤ t) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ sigma : Zeta23.Zeros,
        0 < |normalizedGap t sigma| →
        |normalizedGap t sigma| < eps →
        0 < normalizedProjectiveBaseSourceTerm t sigma := by
  obtain ⟨eps, heps, hphi⟩ :=
    exists_normalizedProjectiveBaseTransform_pos_punctured ht
  refine ⟨eps, heps, ?_⟩
  intro sigma hq0 hqeps
  unfold normalizedProjectiveBaseSourceTerm
  have hm :
      0 < ((Zeta23.zetaZeroConfig).mult (sigma : ℂ) : ℝ) := by
    positivity
  exact mul_pos hm (hphi (normalizedGap t sigma) hq0 hqeps)

end Synthesis
