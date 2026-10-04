import Synthesis.RiemannSelectedPrimeSensitiveThreeTapPairOrdinateCut
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdverseRvMAbel

/-!
# Same-object finite adverse core -> ordinate envelope

This closes the pointwise-to-finite-sum seam on the exact `nearOffFinset`
carrier.  Under a uniform horizontal strip bound, each adverse transformed pair
is bounded by the physical ordinate test at that zero's ordinate.  Summing over
the literal finite off-ordinate window therefore gives a finite majorant which
depends only on ordinates and multiplicities.

The theorem deliberately stops before identifying this strict symmetric finset
with the half-open Zeta23 `(A,B]` window used by `zetaWindowWeightedPair`;
that endpoint convention is kept visible for the RvM attachment.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators
open Zeta23Bridge.OffOrdinateCutoffCarrier

/-- Finite ordinate-only majorant on the exact transformed near-off carrier. -/
def QuarticFourSignedPolePair.threeTapPairAdverseNearEnvelopeAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps A R : ℝ) : ℝ :=
  ∑ sigma ∈ nearOffFinset t R,
    ((zetaZeroConfig).mult (sigma : Zeros) : ℝ)
      * W.threeTapAdversePhysicalOrdinateTest eps A
          (((sigma : Zeros) : ℂ).im)

theorem QuarticFourSignedPolePair.threeTapPairAdverseNearEnvelopeAt_nonneg
    {t eps A R : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    0 <= W.threeTapPairAdverseNearEnvelopeAt eps A R := by
  classical
  unfold QuarticFourSignedPolePair.threeTapPairAdverseNearEnvelopeAt
  exact Finset.sum_nonneg fun sigma hsigma =>
    mul_nonneg (by positivity)
      (W.threeTapAdversePhysicalOrdinateTest_nonneg ht)

/-- At a zero ordinate the physical test is exactly the r^-2 alpha-envelope
appearing in the pointwise pair majorant. -/
theorem QuarticFourSignedPolePair.mult_mul_adversePhysicalTest_eq_pairEnvelope
    {t eps A : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * W.threeTapAdversePhysicalOrdinateTest eps A ((rho : ℂ).im)
      =
    (((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2)
      * W.threeTapKernelAdverseAlphaEnvelope eps A
          (quarticSignedPoleNormalizedOrdinateOffset t rho) := by
  unfold QuarticFourSignedPolePair.threeTapAdversePhysicalOrdinateTest
    quarticSignedPoleNormalizedOrdinateOffset
  ring

/-- Finite transformed adverse core is bounded by the ordinate-only envelope on
exactly the same `nearOffFinset`. -/
theorem QuarticFourSignedPolePair.threeTapPairAdverseNearAt_le_envelope
    {t eps A R : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hA : 0 <= A)
    (hstrip : W.ThreeTapAlphaStripBound A) :
    W.threeTapPairAdverseNearAt eps R
      <= W.threeTapPairAdverseNearEnvelopeAt eps A R := by
  classical
  unfold QuarticFourSignedPolePair.threeTapPairAdverseNearAt
    QuarticFourSignedPolePair.threeTapPairAdverseNearEnvelopeAt
  apply Finset.sum_le_sum
  intro sigma hsigma
  have hpoint :=
    W.threeTapPairAdversePart_le_ordinateEnvelope_of_strip
      ht hA hstrip sigma
  rw [W.mult_mul_adversePhysicalTest_eq_pairEnvelope
      (by linarith : 0 < t) (sigma : Zeros)]
  exact hpoint

/-- Producer-facing finite-core theorem.  Any upper bound for the ordinate-only
finite envelope immediately bounds the actual transformed adverse near mass. -/
theorem QuarticFourSignedPolePair.threeTapPairAdverseNearAt_le_of_envelope_bound
    {t eps A R Bnear : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hA : 0 <= A)
    (hstrip : W.ThreeTapAlphaStripBound A)
    (henv : W.threeTapPairAdverseNearEnvelopeAt eps A R <= Bnear) :
    W.threeTapPairAdverseNearAt eps R <= Bnear := by
  exact (W.threeTapPairAdverseNearAt_le_envelope ht hA hstrip).trans henv

end Synthesis
