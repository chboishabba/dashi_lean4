import Synthesis.RiemannReflectionPairClusterSignal
import Zeta23Bridge.LiteralWeilProjectiveSeparationGate
import Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient

/-!
# Reflection-doubled projective gate

An off-line zero rho has a distinct functional-equation partner at the same
ordinate and opposite height.  The two-radius height defect is even in height,
so the two defects are equal.  Since every same-ordinate defect is nonnegative
under GateData, the literal cluster satisfies

  2 * zeroHeightDefect rho <= clusterHeightDefect.

This strengthens the projective contradiction gate by an exact factor two.

Combining with the existing quadratic expansion gives the coefficient gate

  E + 2 r^2 R_rho < 2 L_rho

instead of the previous one-copy condition

  E + r^2 R_rho < L_rho.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
open Zeta23Bridge.LiteralWeilTwoRadiusSeparationGate
open Zeta23Bridge.LiteralWeilProjectiveSeparationGate
open Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient

theorem gateData_two_targetDefect_le_cluster
    {g : ℝ → ℝ} {t r Lambda : ℝ}
    (hd : GateData g t r Lambda)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0) :
    2 * zeroHeightDefect g r rho
      <= clusterHeightDefect g t r := by
  classical
  rw [clusterHeightDefect_eq_tsum
    hd.smooth hd.compactSupport hd.isEven t r]

  let z0 : SameOrd t := ⟨rho, him⟩
  let z1 : SameOrd t :=
    ⟨reflectZero rho, by
      rw [Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair.im_reflectZero]
      exact him⟩

  have hne : z1 ≠ z0 := by
    intro h
    have hv : (z1 : Zeros) = (z0 : Zeros) :=
      congrArg Subtype.val h
    dsimp [z0, z1] at hv
    exact (reflectZero_ne_of_height_ne_zero hoff) hv

  have hsum :=
    Summable.sum_le_tsum
      (f := fun z : SameOrd t => zeroHeightDefect g r (z : Zeros))
      {z0, z1}
      (fun z _ =>
        zeroHeightDefect_nonneg
          hd.smooth.continuous hd.compactSupport hd.nonneg
          hd.radiusPos hd.radial (z : Zeros))
      (summable_zeroHeightDefect
        hd.smooth hd.compactSupport hd.isEven t r)

  have href :
      zeroHeightDefect g r (z1 : Zeros)
        = zeroHeightDefect g r rho := by
    dsimp [z1]
    unfold zeroHeightDefect
    rw [reflectZero_mult]
    rw [Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair.heightOf_reflectZero]
    rw [heightDefect_neg_height]

  have hfinite :
      ∑ z ∈ ({z0, z1} : Finset (SameOrd t)),
        zeroHeightDefect g r (z : Zeros)
        =
      2 * zeroHeightDefect g r rho := by
    rw [Finset.sum_insert]
    · rw [Finset.sum_singleton]
      dsimp [z0]
      rw [href]
      ring
    · simpa [Finset.mem_singleton] using hne

  rw [hfinite] at hsum
  exact hsum

theorem false_of_projectiveEnvelope_lt_reflectionPairDefect
    {g : ℝ → ℝ} {t r Lambda CG : ℝ}
    (hd : GateData g t r Lambda)
    (henv :
      |clusterHeightDefect g t r|
        <= r ^ 2 * projectiveEnvelope g Lambda t CG)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0)
    (hsep :
      r ^ 2 * projectiveEnvelope g Lambda t CG
        < 2 * zeroHeightDefect g r rho) :
    False := by
  have hlo :=
    gateData_two_targetDefect_le_cluster hd him hoff
  have habs := le_abs_self (clusterHeightDefect g t r)
  linarith

theorem reflectionPair_gate_of_coefficientComparison
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (rho : Zeros)
    (r E : ℝ)
    (hr0 : 0 < r)
    (hr1 : r <= 1)
    (hcmp :
      E + 2 * r ^ 2 * zeroRemainderCoeff g rho
        < 2 * zeroLeadingCoeff g rho) :
    r ^ 2 * E
      < 2 * zeroHeightDefect g r rho := by
  have hbase :=
    abs_zeroHeightDefect_sub_leading_le
      hg hgc rho r hr0.le hr1
  have hlow :
      r ^ 2 * zeroLeadingCoeff g rho
          - r ^ 4 * zeroRemainderCoeff g rho
        <= zeroHeightDefect g r rho := by
    have habs := abs_le.1 hbase
    linarith [habs.1]
  have hr2 : 0 < r ^ 2 := by positivity
  nlinarith [hcmp, hlow, hr2]

theorem false_of_reflectionPair_coefficientGate
    {g : ℝ → ℝ} {t r Lambda CG : ℝ}
    (hd : GateData g t r Lambda)
    (hr1 : r <= 1)
    (henv :
      |clusterHeightDefect g t r|
        <= r ^ 2 * projectiveEnvelope g Lambda t CG)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0)
    (hcmp :
      projectiveEnvelope g Lambda t CG
          + 2 * r ^ 2 * zeroRemainderCoeff g rho
        < 2 * zeroLeadingCoeff g rho) :
    False := by
  have hsep :=
    reflectionPair_gate_of_coefficientComparison
      hd.smooth.continuous hd.compactSupport rho r
      (projectiveEnvelope g Lambda t CG)
      hd.radiusPos hr1 hcmp
  exact false_of_projectiveEnvelope_lt_reflectionPairDefect
    hd henv him hoff hsep

end Synthesis
