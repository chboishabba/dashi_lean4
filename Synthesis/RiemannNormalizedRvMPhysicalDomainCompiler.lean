import Synthesis.RiemannNormalizedBaseTransformDecay
import Synthesis.RiemannNormalizedRvMSmoothMainDecomposition

/-!
# Normalized RvM physical-domain compiler

For gamma=t(1+q), dgamma=t dq.  Hence the smooth RvM q-density is

  t * (1/(2*pi)) * log(t(1+q)/(2*pi)).

The literal normalized Off aggregate carries an external 1/t, so this Jacobian
cancels exactly.  The smooth-main contribution is therefore naturally measured
at order one before Fourier cancellation, and the surviving constant-mode tail
is order log(t)/t only after the literal outer normalization is restored.

This file also records the honest domain decomposition.  The RvM density is
physical only for gamma>0, i.e. q>-1.  Whole-line zero-mode cancellation does
not imply exact cancellation on q>-1.  Instead

  integral_(q>-1) Phi
    = - integral_(q<=-1) Phi

whenever the whole-line integral vanishes.  Thus the missing negative half-line
is the exact residual constant-mode term, and the pointwise q^-2 estimate from
RiemannNormalizedBaseTransformDecay is the correct way to control it.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Real

namespace Synthesis

def normalizedRvMSmoothQDensity (t q : ℝ) : ℝ :=
  t * normalizedRvMSmoothDensity t q

def normalizedRvMPhysicalIndicator (phi : ℝ → ℝ) : ℝ → ℝ :=
  Set.Ioi (-1 : ℝ).indicator phi

def normalizedRvMMissingTailIndicator (phi : ℝ → ℝ) : ℝ → ℝ :=
  Set.Iic (-1 : ℝ).indicator phi

theorem normalizedRvMSmoothQDensity_eq
    (t q : ℝ) :
    normalizedRvMSmoothQDensity t q
      = t * normalizedRvMSmoothDensity t q := by
  rfl

theorem outerJacobian_cancel_smoothQDensity
    {t x : ℝ} (ht : t ≠ 0) :
    (1 / t) * (t * x) = x := by
  field_simp [ht]

theorem physical_plus_missing_indicator
    (phi : ℝ → ℝ) :
    (fun q =>
      normalizedRvMPhysicalIndicator phi q
        + normalizedRvMMissingTailIndicator phi q)
      =
    phi := by
  funext q
  by_cases h : q <= -1
  · have hIic : q ∈ Set.Iic (-1 : ℝ) := h
    have hnotIoi : q ∉ Set.Ioi (-1 : ℝ) := by
      simp only [Set.mem_Ioi]
      linarith
    simp [normalizedRvMPhysicalIndicator,
      normalizedRvMMissingTailIndicator, hIic, hnotIoi]
  · have hIoi : q ∈ Set.Ioi (-1 : ℝ) := by
      simp only [Set.mem_Ioi]
      linarith
    have hnotIic : q ∉ Set.Iic (-1 : ℝ) := by
      simpa [Set.mem_Iic] using h
    simp [normalizedRvMPhysicalIndicator,
      normalizedRvMMissingTailIndicator, hIoi, hnotIic]

/--
Generic exact domain-restriction identity.  No RvM estimate enters: this is
only the partition R = (-1,infinity) union (-infinity,-1].
-/
theorem integral_physical_add_missing_eq_total
    {phi : ℝ → ℝ}
    (hphys : Integrable (normalizedRvMPhysicalIndicator phi))
    (htail : Integrable (normalizedRvMMissingTailIndicator phi)) :
    (∫ q : ℝ, normalizedRvMPhysicalIndicator phi q)
      +
    (∫ q : ℝ, normalizedRvMMissingTailIndicator phi q)
      =
    ∫ q : ℝ, phi q := by
  rw [← integral_add hphys htail]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun q => by
    have hfun := congrFun (physical_plus_missing_indicator phi) q
    exact hfun

/--
If the whole-line transform has zero total mass, the physical q>-1 integral is
exactly minus the missing q<=-1 tail.
-/
theorem integral_physical_eq_neg_missing_of_total_zero
    {phi : ℝ → ℝ}
    (hphys : Integrable (normalizedRvMPhysicalIndicator phi))
    (htail : Integrable (normalizedRvMMissingTailIndicator phi))
    (hzero : (∫ q : ℝ, phi q) = 0) :
    (∫ q : ℝ, normalizedRvMPhysicalIndicator phi q)
      =
    - (∫ q : ℝ, normalizedRvMMissingTailIndicator phi q) := by
  have hsplit :=
    integral_physical_add_missing_eq_total hphys htail
  rw [hzero] at hsplit
  linarith

theorem abs_integral_physical_eq_abs_missing_of_total_zero
    {phi : ℝ → ℝ}
    (hphys : Integrable (normalizedRvMPhysicalIndicator phi))
    (htail : Integrable (normalizedRvMMissingTailIndicator phi))
    (hzero : (∫ q : ℝ, phi q) = 0) :
    |∫ q : ℝ, normalizedRvMPhysicalIndicator phi q|
      =
    |∫ q : ℝ, normalizedRvMMissingTailIndicator phi q| := by
  rw [integral_physical_eq_neg_missing_of_total_zero hphys htail hzero,
      abs_neg]

/--
Constant-mode budget after honest domain restriction.  Any quantitative bound
on the missing q<=-1 tail immediately controls the q>-1 constant mode.
-/
theorem constantMode_physical_abs_le_of_missingTail
    {t C : ℝ}
    (hC : 0 <= C)
    (hphys :
      Integrable
        (normalizedRvMPhysicalIndicator
          (normalizedCenteredBaseTransform t)))
    (htail :
      Integrable
        (normalizedRvMMissingTailIndicator
          (normalizedCenteredBaseTransform t)))
    (hzero :
      (∫ q : ℝ, normalizedCenteredBaseTransform t q) = 0)
    (htailBound :
      |∫ q : ℝ,
        normalizedRvMMissingTailIndicator
          (normalizedCenteredBaseTransform t) q| <= C) :
    |normalizedRvMConstantMode t
      * (∫ q : ℝ,
          normalizedRvMPhysicalIndicator
            (normalizedCenteredBaseTransform t) q)|
      <=
    |normalizedRvMConstantMode t| * C := by
  rw [abs_mul]
  have hEq :=
    abs_integral_physical_eq_abs_missing_of_total_zero
      hphys htail hzero
  rw [hEq]
  exact mul_le_mul_of_nonneg_left htailBound (abs_nonneg _)

end Synthesis
