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

/--
No punctured neighbourhood of q=0 can carry a pointwise nonpositive canonical
base kernel.  Thus the desired one-sided restricted N-mu estimate, if true,
must use the signed measure interaction rather than a local fixed-sign kernel.
-/
theorem not_exists_normalizedProjectiveBaseTransform_nonpos_punctured
    {t : ℝ} (ht : 18 ≤ t) :
    ¬ ∃ eps : ℝ, 0 < eps ∧
      ∀ q : ℝ, 0 < |q| → |q| < eps →
        normalizedProjectiveBaseTransform t q ≤ 0 := by
  intro hbad
  obtain ⟨epsBad, hBadPos, hbadSign⟩ := hbad
  obtain ⟨epsGood, hGoodPos, hgoodSign⟩ :=
    exists_normalizedProjectiveBaseTransform_pos_punctured ht
  let q : ℝ := min epsBad epsGood / 2
  have hqpos : 0 < q := by
    dsimp [q]
    have hmin : 0 < min epsBad epsGood := lt_min hBadPos hGoodPos
    linarith
  have hqBad : |q| < epsBad := by
    rw [abs_of_pos hqpos]
    dsimp [q]
    have hle := min_le_left epsBad epsGood
    nlinarith
  have hqGood : |q| < epsGood := by
    rw [abs_of_pos hqpos]
    dsimp [q]
    have hle := min_le_right epsBad epsGood
    nlinarith
  have hpos := hgoodSign q (by simpa [abs_of_pos hqpos] using hqpos) hqGood
  have hnonpos := hbadSign q (by simpa [abs_of_pos hqpos] using hqpos) hqBad
  linarith


/--
Positive curvature gives a punctured neighbourhood on which the derivative has
the sign of q.  This is the Abel-facing local form of the positive-lobe theorem.
-/
theorem exists_normalizedProjectiveBaseTransformDeriv_sign_punctured
    {t : ℝ} (ht : 18 ≤ t) :
    ∃ eps : ℝ, 0 < eps ∧
      (∀ q : ℝ, 0 < q → q < eps →
        0 < normalizedProjectiveBaseTransformDeriv t q) ∧
      (∀ q : ℝ, -eps < q → q < 0 →
        normalizedProjectiveBaseTransformDeriv t q < 0) := by
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
  have hmono :
      StrictMonoOn (normalizedProjectiveBaseTransformDeriv t)
        (Set.Icc (-eps) eps) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (-eps) eps)
    · exact
        (normalizedProjectiveBaseTransformDeriv_continuous t).continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      rw [(normalizedProjectiveBaseTransformDeriv_hasDerivAt t x).deriv]
      apply hsecond x
      exact abs_lt.2 hx
  refine ⟨eps, heps, ?_, ?_⟩
  · intro q hq0 hqeps
    have h0mem : (0 : ℝ) ∈ Set.Icc (-eps) eps := by
      constructor <;> linarith
    have hqmem : q ∈ Set.Icc (-eps) eps := by
      constructor <;> linarith
    have h := hmono h0mem hqmem hq0
    rw [normalizedProjectiveBaseTransformDeriv_zero] at h
    exact h
  · intro q hqlo hq0
    have hqmem : q ∈ Set.Icc (-eps) eps := by
      constructor <;> linarith
    have h0mem : (0 : ℝ) ∈ Set.Icc (-eps) eps := by
      constructor <;> linarith
    have h := hmono hqmem h0mem hq0
    rw [normalizedProjectiveBaseTransformDeriv_zero] at h
    exact h

/--
Equivalent sign-product form: sufficiently near q=0, q * Phi_t'(q) is
strictly positive away from q=0.
-/
theorem exists_normalizedProjectiveBaseTransformDeriv_radial_pos
    {t : ℝ} (ht : 18 ≤ t) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ q : ℝ, 0 < |q| → |q| < eps →
        0 < q * normalizedProjectiveBaseTransformDeriv t q := by
  obtain ⟨eps, heps, hpos, hneg⟩ :=
    exists_normalizedProjectiveBaseTransformDeriv_sign_punctured ht
  refine ⟨eps, heps, ?_⟩
  intro q hq0 hqeps
  by_cases hq : 0 < q
  · exact mul_pos hq (hpos q hq (by simpa [abs_of_pos hq] using hqeps))
  · have hqn : q < 0 := by
      have hqne : q ≠ 0 := by
        intro hz
        simpa [hz] using hq0
      exact lt_of_le_of_ne (le_of_not_gt hq) (Ne.symm hqne)
    have hleft : -eps < q := by
      rw [abs_of_neg hqn] at hqeps
      linarith
    exact mul_pos_of_neg_of_neg hqn (hneg q hleft hqn)

end Synthesis
