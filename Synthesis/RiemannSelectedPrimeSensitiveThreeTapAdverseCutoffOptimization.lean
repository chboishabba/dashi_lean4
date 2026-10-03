import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdverseAsymptoticBudget

/-!
# Cutoff optimization for the canonical one-scale scalar

The finite adverse core grows as the physical cutoff R captures more zeros,
while the residual adverse tail decreases.  This file records that tradeoff
exactly and then specializes the explicit finite budget to the simple
RvM-compatible corridor R=t/2.

At R=t/2 the scale-table budget is exactly

  256/t * M0 * Cmu*log(3t/2+3)
  + 256/t^2 * Ehalf * M0
  + 4096/t^2 * Ehalf * M1,

where

  Ehalf = C*(log(t/2+3)+log(3t/2+4)),
  M0 = cosh(1) * normalizedAbsMass,
  M1 = cosh(1) * normalizedFirstAbsMoment.

Thus the leading finite-core term is the smooth-mu O((log t)/t) term,
conditional only on controlling the normalized masses.  The theorem at the end
shows that negativity of this coarser half-height scale scalar is sufficient
for the actual paid resonance PASS.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators Interval
open Zeta23Bridge.OffOrdinateCutoffCarrier

/-- Literal near-off windows are monotone in their positive radius. -/
theorem nearOffFinset_mono_radius
    {t R1 R2 : ℝ}
    (hR : R1 <= R2) :
    nearOffFinset t R1 ⊆ nearOffFinset t R2 := by
  intro sigma hsigma
  have hmem := (mem_nearOffFinset_iff t R1 sigma).1 hsigma
  apply (mem_nearOffFinset_iff t R2 sigma).2
  exact lt_of_lt_of_le hmem hR

/-- The captured adverse mass is monotone increasing in the cutoff. -/
theorem QuarticFourSignedPolePair.threeTapPairAdverseNearAt_mono
    {t eps R1 R2 : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hR : R1 <= R2) :
    W.threeTapPairAdverseNearAt eps R1
      <= W.threeTapPairAdverseNearAt eps R2 := by
  classical
  unfold QuarticFourSignedPolePair.threeTapPairAdverseNearAt
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (nearOffFinset_mono_radius hR)
    (fun sigma h2 h1 =>
      W.threeTapPairAdversePart_nonneg (eps:=eps) (sigma : Zeros))

/-- Consequently the actual residual adverse tail is antitone in R. -/
theorem QuarticFourSignedPolePair.threeTapPairAdverseFarAfter_antitone
    {t eps R1 R2 : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hR : R1 <= R2) :
    W.threeTapPairAdverseFarAfter eps R2
      <= W.threeTapPairAdverseFarAfter eps R1 := by
  unfold QuarticFourSignedPolePair.threeTapPairAdverseFarAfter
  have hnear := W.threeTapPairAdverseNearAt_mono (eps:=eps) hR
  linarith

/-- The literal near+far adverse total is cutoff-independent. -/
theorem QuarticFourSignedPolePair.threeTapPairAdverseCutoff_conservation
    {t eps R1 R2 : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapPairAdverseNearAt eps R1
        + W.threeTapPairAdverseFarAfter eps R1
      =
    W.threeTapPairAdverseNearAt eps R2
        + W.threeTapPairAdverseFarAfter eps R2 := by
  rw [← W.threeTap_pair_adverse_tsum_eq_near_add_far (eps:=eps) (R:=R1),
      ← W.threeTap_pair_adverse_tsum_eq_near_add_far (eps:=eps) (R:=R2)]

/-- RvM logarithmic discrepancy factor at the half-height cutoff. -/
def threeTapHalfHeightRvMFactor (t C : ℝ) : ℝ :=
  C * (Real.log (t/2 + 3) + Real.log (3*t/2 + 4))

/-- Smooth-mu logarithmic factor at the half-height cutoff. -/
def threeTapHalfHeightMuFactor (t Cmu : ℝ) : ℝ :=
  Cmu * Real.log (3*t/2 + 3)

/-- Canonical M0 coefficient after the uniform cosh bound. -/
def QuarticFourSignedPolePair.threeTapCanonicalM0
    {t : ℝ} (W : QuarticFourSignedPolePair t) (eps : ℝ) : ℝ :=
  Real.cosh 1 * W.threeTapNormalizedProjectiveAbsMass eps

/-- Canonical M1 coefficient after the uniform cosh bound. -/
def QuarticFourSignedPolePair.threeTapCanonicalM1
    {t : ℝ} (W : QuarticFourSignedPolePair t) (eps : ℝ) : ℝ :=
  Real.cosh 1 * W.threeTapNormalizedProjectiveAbsMoment eps 1

/-- Closed-form half-height scale budget displaying the three asymptotic
powers separately. -/
def QuarticFourSignedPolePair.threeTapAdverseHalfHeightClosedBudget
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps C Cmu : ℝ) : ℝ :=
  (256/t) * W.threeTapCanonicalM0 eps * threeTapHalfHeightMuFactor t Cmu
    +
  (256/t^2) * threeTapHalfHeightRvMFactor t C * W.threeTapCanonicalM0 eps
    +
  (4096/t^2) * threeTapHalfHeightRvMFactor t C * W.threeTapCanonicalM1 eps

/-- Exact algebraic specialization of the generic scale budget at R=t/2. -/
theorem QuarticFourSignedPolePair.threeTapAdverseHalfHeightScaleBudget_eq_closed
    {t eps C Cmu : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapAdverseHalfHeightScaleBudget eps C Cmu
      = W.threeTapAdverseHalfHeightClosedBudget eps C Cmu := by
  unfold QuarticFourSignedPolePair.threeTapAdverseHalfHeightScaleBudget
    QuarticFourSignedPolePair.threeTapAdverseNearScaleBudget
    QuarticFourSignedPolePair.threeTapAdverseHalfHeightClosedBudget
    QuarticFourSignedPolePair.threeTapCanonicalM0
    QuarticFourSignedPolePair.threeTapCanonicalM1
    threeTapHalfHeightRvMFactor threeTapHalfHeightMuFactor
  field_simp [ne_of_gt ht]
  ring

/-- Coarser half-height scalar whose finite part has completely explicit
source-visible t powers. -/
def QuarticFourSignedPolePair.ThreeTapAdverseHalfHeightScaleScalar
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps C Cmu : ℝ) : ℝ :=
  (1/2 : ℝ) *
    (W.threeTapAdverseHalfHeightClosedBudget eps C Cmu
      + W.threeTapPairAdverseFarAfter eps (t/2))
    -
  (W.threeTapAdaptiveLocalExact eps
    - W.threeTapResonanceCompensation eps)

/-- The actual canonical final scalar at R=t/2 is no larger than the
closed-form scale scalar. -/
theorem QuarticFourSignedPolePair.threeTapAdverseCanonicalFinalScalar_half_le_scale
    {t eps C Cmu : ℝ}
    (ht : 200 <= t)
    (hC : 0 <= C)
    (hCmu : 0 <= Cmu)
    (W : QuarticFourSignedPolePair t) :
    W.ThreeTapAdverseCanonicalFinalScalar eps (t/2) C Cmu
      <= W.ThreeTapAdverseHalfHeightScaleScalar eps C Cmu := by
  have hnear := W.threeTapAdverseNearExplicitBudget_le_scaleBudget
    (eps:=eps) (R:=t/2) (C:=C) (Cmu:=Cmu)
    ht (by linarith) hC hCmu (by linarith)
  have hscaleEq := W.threeTapAdverseHalfHeightScaleBudget_eq_closed
    (eps:=eps) (C:=C) (Cmu:=Cmu) (by linarith : 0 < t)
  unfold QuarticFourSignedPolePair.ThreeTapAdverseCanonicalFinalScalar
    QuarticFourSignedPolePair.ThreeTapAdverseHalfHeightScaleScalar
  rw [← hscaleEq]
  linarith

/-- The half-height scale scalar is an honest sufficient PASS criterion using
only the existing unconditional RvM/mu constants. -/
theorem QuarticFourSignedPolePair.exists_threeTapHalfHeightScalePass_constants :
    ∃ C Cmu : ℝ, 0 <= C ∧ 0 <= Cmu ∧
      ∀ {t eps : ℝ},
        200 <= t ->
        ∀ W : QuarticFourSignedPolePair t,
        W.ThreeTapAdverseHalfHeightScaleScalar eps C Cmu < 0 ->
        W.threeTapResonancePaidCost eps < 0 := by
  obtain ⟨C,Cmu,hC,hCmu,hcut⟩ :=
    QuarticFourSignedPolePair.exists_threeTapAdverseCanonicalFinalCut_constants
  refine ⟨C,Cmu,hC,hCmu,?_⟩
  intro t eps ht W hscale
  have hactual :
      W.ThreeTapAdverseCanonicalFinalScalar eps (t/2) C Cmu < 0 :=
    lt_of_le_of_lt
      (W.threeTapAdverseCanonicalFinalScalar_half_le_scale ht hC hCmu)
      hscale
  apply hcut ht W (W.threeTapHalfHeightCutoff_compatible ht)
  exact (W.threeTapAdverseCanonicalFinalScalar_neg_iff).1 hactual

/-- Direct resonance near-line PASS from the closed half-height scale scalar. -/
theorem QuarticFourSignedPolePair.exists_threeTapHalfHeightScalePass_terminal_constants :
    ∃ C Cmu : ℝ, 0 <= C ∧ 0 <= Cmu ∧
      ∀ {t eps mult : ℝ},
        200 <= t ->
        ∀ W : QuarticFourSignedPolePair t,
        Real.cos (t * Real.log 2) = 0 ->
        W.ThreeTapAdverseHalfHeightScaleScalar eps C Cmu < 0 ->
        ∃ delta : ℝ, 0 < delta ∧
          ∀ a : ℝ, 0 < a -> a < delta ->
            0 < W.threeTapAdaptiveTerminalProfile eps mult a := by
  obtain ⟨C,Cmu,hC,hCmu,hpass⟩ :=
    QuarticFourSignedPolePair.exists_threeTapHalfHeightScalePass_constants
  refine ⟨C,Cmu,hC,hCmu,?_⟩
  intro t eps mult ht W hphase hscale
  apply W.exists_threeTapResonantTerminalProfile_pos_right_of_paidCost_neg ht hphase
  exact hpass ht W hscale

end Synthesis
