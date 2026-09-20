import Synthesis.RiemannNormalizedProjectiveHorizontalSignedNearFar
import Synthesis.RiemannNormalizedProjectiveRvMMissingTailBound
import Synthesis.RiemannNormalizedProjectiveOffTsumAttachment
import Zeta23Bridge.ProjectedZeroTailSummability
import Zeta23Bridge.ReflectionPairCurvatureBound
import Zeta23Bridge.NearFarCarrierSplit

/-!
# Absolute summability of the actual far horizontal source family

For the far ordinate tail we avoid a new alpha-uniform bound on Q_proj itself.

Use the exact identity

  horizontalSource = normalizedProjectiveAtom - m * Phi_proj(q).

For |Im rho - t| >= 1 the normalized atom is t times the literal projective
reflection-pair response, while the q-only base transform has q^-2 decay.
Both are therefore dominated by the existing summable literal quadratic
zero-tail weight.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.ReflectionPairKernelDecay
open Zeta23Bridge.ReflectionPairCurvatureBound
open Zeta23Bridge.ProjectedZeroTailSummability
open Zeta23Bridge.NearFarCarrierSplit

theorem normalizedProjectiveOffZeroAtom_eq_t_mul_pairTerm
    {t : ℝ} (ht : 18 ≤ t) (rho : Zeros) :
    normalizedProjectiveOffZeroAtom t rho
      =
    t * pairTerm
      (projTaper
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t))
      t rho := by
  have ht0 : t ≠ 0 := by linarith
  have hpair :
      literalPairProjectiveDefect
          (quantitativeCanonicalTaper t)
          t (quantitativeSampleRadius t) rho
        =
      pairTerm
        (projTaper
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t))
        t rho := by
    rw [literalPairProjectiveDefect_eq_projectiveZero_add_reflect
      (quantitativeCanonicalTaper_contDiff ht)
      (quantitativeCanonicalTaper_compact ht)
      quantitativeCanonicalTaper_even
      t (quantitativeSampleRadius t) rho]
    rfl
  have hnorm :=
    literalPairProjectiveDefect_eq_one_div_t_mul_normalizedAtom ht rho
  rw [hpair] at hnorm
  have hscaled := congrArg (fun x : ℝ => t * x) hnorm
  have hcancel : t * (1 / t) = 1 := by
    field_simp [ht0]
  rw [mul_assoc, hcancel, one_mul] at hscaled
  exact hscaled.symm

def normalizedProjectiveHorizontalFarTerm
    (t : ℝ) (rho : Zeros) : ℝ :=
  if 1 ≤ |(rho : ℂ).im - t|
  then normalizedProjectiveHorizontalSourceTerm t rho
  else 0

theorem normalizedProjectiveHorizontalFarTerm_abs
    (t : ℝ) (rho : Zeros) :
    |normalizedProjectiveHorizontalFarTerm t rho|
      =
    if 1 ≤ |(rho : ℂ).im - t|
    then |normalizedProjectiveHorizontalSourceTerm t rho|
    else 0 := by
  unfold normalizedProjectiveHorizontalFarTerm
  split <;> simp_all

theorem weighted_normalizedProjectiveBase_abs_le_delta_invSq
    {t : ℝ} (ht : 18 ≤ t)
    (rho : Zeros)
    (hdelta : ((rho : ℂ).im - t) ≠ 0) :
    |((zetaZeroConfig).mult (rho : ℂ) : ℝ)
        * normalizedProjectiveBaseTransform t (normalizedGap t rho)|
      ≤
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * (normalizedProjectiveBaseCurvature t * t^2
          / ((rho : ℂ).im - t)^2) := by
  have ht0 : t ≠ 0 := by linarith
  have hq : normalizedGap t rho ≠ 0 := by
    unfold normalizedGap
    exact div_ne_zero hdelta ht0
  have hdecay :=
    normalizedProjectiveBaseTransform_abs_le_invSq
      (t := t) (q := normalizedGap t rho) hq
  have hm :
      0 ≤ ((zetaZeroConfig).mult (rho : ℂ) : ℝ) := by positivity
  rw [abs_mul, abs_of_nonneg hm]
  refine mul_le_mul_of_nonneg_left ?_ hm
  unfold normalizedGap at hdecay ⊢
  calc
    |normalizedProjectiveBaseTransform t (((rho : ℂ).im - t) / t)|
      ≤ normalizedProjectiveBaseCurvature t
          / (((rho : ℂ).im - t) / t)^2 := hdecay
    _ = normalizedProjectiveBaseCurvature t * t^2
          / ((rho : ℂ).im - t)^2 := by
          field_simp [hdelta, ht0]
          ring

theorem normalizedProjectiveHorizontalFarTerm_abs_le_tailTerm
    {t Cpair : ℝ} (ht : 18 ≤ t)
    (hCpair : ∀ rho : Zeros,
      pairWeightCurvature
        (projTaper
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t))
        (heightOf rho)
        ≤ Cpair)
    (hCpair0 : 0 ≤ Cpair)
    (rho : Zeros) :
    |normalizedProjectiveHorizontalFarTerm t rho|
      ≤
    (t * Cpair + t^2 * normalizedProjectiveBaseCurvature t)
      * tailTerm t rho := by
  have htpos : 0 < t := by linarith
  rw [normalizedProjectiveHorizontalFarTerm_abs]
  by_cases hfar : 1 ≤ |(rho : ℂ).im - t|
  · rw [if_pos hfar]
    have hdelta : ((rho : ℂ).im - t) ≠ 0 := by
      intro hz
      rw [hz, abs_zero] at hfar
      linarith
    have hatomEq :=
      normalizedProjectiveOffZeroAtom_eq_t_mul_pairTerm ht rho
    have hpair :=
      abs_zeroConeValue_add_reflect_le
        (projTaper_contDiff (quantitativeCanonicalTaper_contDiff ht)
          (quantitativeSampleRadius t))
        (projTaper_hasCompactSupport (quantitativeCanonicalTaper_compact ht)
          (quantitativeSampleRadius t))
        (projTaper_even quantitativeCanonicalTaper_even
          (quantitativeSampleRadius t))
        t rho hdelta
    have hatom :
        |normalizedProjectiveOffZeroAtom t rho|
          ≤
        t * ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
          * (Cpair / ((rho : ℂ).im - t)^2) := by
      rw [hatomEq, abs_mul, abs_of_pos htpos]
      have hcurv := hCpair rho
      have hm :
          0 ≤ ((zetaZeroConfig).mult (rho : ℂ) : ℝ) := by positivity
      have hd2 : 0 < ((rho : ℂ).im - t)^2 := sq_pos_of_ne_zero hdelta
      have hscaledCurv :
          ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
            * (pairWeightCurvature
                (projTaper
                  (quantitativeCanonicalTaper t)
                  (quantitativeSampleRadius t))
                (heightOf rho)
              / ((rho : ℂ).im - t)^2)
            ≤
          ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
            * (Cpair / ((rho : ℂ).im - t)^2) := by
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hcurv hd2.le) hm
      exact mul_le_mul_of_nonneg_left
        (hpair.trans hscaledCurv) htpos.le
    have hbase :=
      weighted_normalizedProjectiveBase_abs_le_delta_invSq ht rho hdelta
    have hsplit :
        normalizedProjectiveHorizontalSourceTerm t rho
          =
        normalizedProjectiveOffZeroAtom t rho
          -
        ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
          * normalizedProjectiveBaseTransform t (normalizedGap t rho) := by
      have h :=
        normalizedProjectiveOffZeroAtom_eq_base_add_sourceHorizontal
          (by linarith : t ≠ 0) rho
      linarith
    rw [hsplit]
    have htri := abs_sub
      (normalizedProjectiveOffZeroAtom t rho)
      (((zetaZeroConfig).mult (rho : ℂ) : ℝ)
        * normalizedProjectiveBaseTransform t (normalizedGap t rho))
    unfold tailTerm
    rw [if_pos hfar]
    calc
      |normalizedProjectiveOffZeroAtom t rho
        - ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
          * normalizedProjectiveBaseTransform t (normalizedGap t rho)|
        ≤ |normalizedProjectiveOffZeroAtom t rho|
          + |((zetaZeroConfig).mult (rho : ℂ) : ℝ)
            * normalizedProjectiveBaseTransform t (normalizedGap t rho)| := htri
      _ ≤
        t * ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
            * (Cpair / ((rho : ℂ).im - t)^2)
          +
        ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
            * (normalizedProjectiveBaseCurvature t * t^2
              / ((rho : ℂ).im - t)^2) := add_le_add hatom hbase
      _ =
        (t * Cpair + t^2 * normalizedProjectiveBaseCurvature t)
          * (((zetaZeroConfig).mult (rho : ℂ) : ℝ)
            / ((rho : ℂ).im - t)^2) := by ring
  · rw [if_neg hfar]
    unfold tailTerm
    rw [if_neg hfar]
    simp

theorem exists_canonicalProjectiveHorizontalFarSummableBound
    {t : ℝ} (ht : 18 ≤ t) :
    ∃ K : ℝ, 0 ≤ K
      ∧ Summable (fun rho : Zeros =>
          |normalizedProjectiveHorizontalFarTerm t rho|)
      ∧ (∀ rho : Zeros,
          |normalizedProjectiveHorizontalFarTerm t rho|
            ≤ K * tailTerm t rho)
      ∧ (∑' rho : Zeros,
          |normalizedProjectiveHorizontalFarTerm t rho|)
          ≤ K * ∑' rho : Zeros, tailTerm t rho := by
  obtain ⟨C0, hC0⟩ :=
    exists_uniform_carrier_curvature_bound
      (projTaper_contDiff (quantitativeCanonicalTaper_contDiff ht)
        (quantitativeSampleRadius t))
      (projTaper_hasCompactSupport (quantitativeCanonicalTaper_compact ht)
        (quantitativeSampleRadius t))
  let Cpair : ℝ := max C0 0
  let K : ℝ :=
    t * Cpair + t^2 * normalizedProjectiveBaseCurvature t
  have hCp0 : 0 ≤ Cpair := le_max_right _ _
  have hK0 : 0 ≤ K := by
    dsimp [K]
    have hb := normalizedProjectiveBaseCurvature_nonneg t
    have ht0 : 0 ≤ t := by linarith
    positivity
  have hdom : ∀ rho : Zeros,
      |normalizedProjectiveHorizontalFarTerm t rho|
        ≤ K * tailTerm t rho := by
    intro rho
    exact normalizedProjectiveHorizontalFarTerm_abs_le_tailTerm
      ht
      (Cpair := Cpair)
      (fun z => (hC0 z).trans (le_max_left _ _))
      hCp0 rho
  have hsumMajor :
      Summable (fun rho : Zeros => K * tailTerm t rho) :=
    (summable_tailTerm t).mul_left K
  have habs :
      Summable (fun rho : Zeros =>
        |normalizedProjectiveHorizontalFarTerm t rho|) :=
    Summable.of_nonneg_of_le
      (fun rho => abs_nonneg _)
      hdom hsumMajor
  refine ⟨K, hK0, habs, hdom, ?_⟩
  exact habs.tsum_le_tsum hdom hsumMajor

end Synthesis
