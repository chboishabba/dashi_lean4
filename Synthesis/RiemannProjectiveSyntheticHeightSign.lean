import Synthesis.RiemannCanonicalGateData
import Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
import Zeta23Bridge.LiteralWeilProjectiveTaper
import Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector

/-!
# Synthetic-height sign of the literal projective reflection-pair kernel

The current normalized signed route had a theorem saying the divided-square
horizontal coefficient is negative at q=0 when the horizontal height is realized
by an actual same-ordinate zero.

That is weaker than the underlying two-radius geometry.

For an arbitrary real height a, the projective reflection-pair kernel at zero
ordinate gap is exactly

  integral reflectionPairWeight (projTaper g r) a 0
    = -4 * heightDefect g r a 0.

This is a direct same-object identity: projTaper is precisely the two-radius
bracket consumed by the determinant.

Therefore, on canonical GateData, every nonzero synthetic height has strictly
negative projective reflection-pair response at q=0.  No zero with that height
needs to exist at the target ordinate.

This is the correct sign theorem to transport to the normalized
Q_proj(t,alpha,0) surface.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector
open Zeta23Bridge.LiteralWeilTwoRadiusSeparationGate

/--
Exact synthetic-height projective identity:

  <reflection pair, projTaper> = -4 * heightDefect.

The sign reversal is the orientation of twoRadiusBracket:
it is A_0(r) cos(2ru) - A_0(2r) cos(ru), whereas heightDefect
is A_a(r) A_0(2r) - A_a(2r) A_0(r).
-/
theorem reflectionPairWeight_projTaper_zero_eq_neg_four_heightDefect
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (r a : ℝ) :
    (∫ u : ℝ,
      reflectionPairWeight (projTaper g r) a 0 u)
      =
    -4 * heightDefect g r a 0 := by
  let F : ℝ → ℝ := fun u =>
    4 * g u * Real.cosh (a * u)

  have hFcont : Continuous F := by
    dsimp [F]
    fun_prop

  have hFcpt : HasCompactSupport F := by
    dsimp [F]
    exact (hgc.mul_left).mul_right

  have hproj :=
    cosineChannelProjective hFcont hFcpt g r

  have h2 :
      (∫ u : ℝ, F u * Real.cos (2 * r * u))
        =
      4 * evenResp g a (2 * r) := by
    unfold F evenResp
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by ring

  have h1 :
      (∫ u : ℝ, F u * Real.cos (r * u))
        =
      4 * evenResp g a r := by
    unfold F evenResp
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by ring

  have hrhs :
      (∫ u : ℝ, F u * twoRadiusBracket g r u)
        =
      ∫ u : ℝ,
        reflectionPairWeight (projTaper g r) a 0 u := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by
      unfold F reflectionPairWeight projTaper
      simp only [zero_mul, Real.cos_zero, mul_one]
      ring

  rw [h2, h1, hrhs] at hproj
  unfold heightDefect
  linarith

/--
Canonical synthetic sign theorem: every nonzero horizontal height gives a
strictly negative literal projective reflection-pair response at zero ordinate
gap.
-/
theorem canonical_reflectionPairWeight_projTaper_zero_neg
    {t a : ℝ}
    (ht : 18 ≤ t)
    (ha : a ≠ 0) :
    (∫ u : ℝ,
      reflectionPairWeight
        (projTaper
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t))
        a 0 u)
      < 0 := by
  let hd := quantitativeCanonicalGateData ht
  obtain ⟨u0, v0, hu0, hv0, huv⟩ := hd.twoPoint
  have hD :
      0 <
      heightDefect
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t)
        a 0 := by
    exact twoRadiusEvenProfileDetectsHeight
      hd.smooth.continuous
      hd.compactSupport
      hd.nonneg
      hd.radiusPos
      hd.radial
      hu0 hv0 huv ha
  rw [reflectionPairWeight_projTaper_zero_eq_neg_four_heightDefect
    hd.smooth.continuous hd.compactSupport]
  linarith

end Synthesis
