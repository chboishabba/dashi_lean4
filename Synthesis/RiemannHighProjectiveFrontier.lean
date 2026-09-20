import Synthesis.RiemannSelectedRadiusClusterReduction
import Synthesis.RiemannCanonicalCompletedResidualMinCut
import Zeta23Bridge.LiteralWeilProjectiveSeparationGate

/-!
# Prize-facing high projective frontier

The one-radius selected complement is now solved exactly, but it is height-blind.
The RH-sensitive high consumer is the two-radius projective height defect.

The imported Zeta23 bridge already proves, for an off-line zero, the sandwich

  0 < D_rho(r) <= D_cluster(t,r) <= r^2 E_proj(g,Lambda,t),

provided the taper support lies below the first prime frequency.

For the positive high region t >= 18, that support premise is no longer an
independent hypothesis: the selected-radius owner proves

  9*pi <= 4*t*log 2

throughout the whole region.

Consequently the only remaining analytic inequality on this route is the strict
coefficient separation

  r^2 E_proj(g,Lambda,t) < D_rho(r).

This file removes the height/support plumbing and exposes that single leaf.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilProjectiveSeparationGate

theorem high_primeInvisible_projective_height
    {t : ℝ} (ht : 18 <= t) :
    9 * Real.pi <= 4 * |t| * Real.log 2 := by
  have ht0 : 0 <= t := by linarith
  rw [abs_of_nonneg ht0]
  exact quantitativeCanonical_primeInvisible_height ht

theorem targetZeroDefect_le_projectiveEnvelope_high
    {rhoStar : Zeros} {t : ℝ}
    (him : (rhoStar : ℂ).im = t)
    (hoffline : heightOf rhoStar ≠ 0)
    (ht : 18 <= t) :
    ∃ (g : ℝ → ℝ) (r Lambda CG : ℝ),
      ContDiff ℝ 2 g
      ∧ HasCompactSupport g
      ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r
      ∧ 0 <= Lambda
      ∧ (∀ u, g u ≠ 0 → |u| <= Lambda)
      ∧ 0 <= CG
      ∧ evenConeFunctional (primeVec (sampleFam g t r)) = 0
      ∧ evenConeFunctional (primeVec (sampleFam g t (2 * r))) = 0
      ∧ primeProjectiveDefect g t r = 0
      ∧ clusterHeightDefect g t r
          =
        offOrdProjectiveDefect g t r
          + gammaProjectiveDefect g t r
          + poleProjectiveDefect g t r
      ∧ 0 < zeroHeightDefect g r rhoStar
      ∧ zeroHeightDefect g r rhoStar <= clusterHeightDefect g t r
      ∧ clusterHeightDefect g t r
          <= r ^ 2 * projectiveEnvelope g Lambda t CG := by
  have htne : t ≠ 0 := by linarith
  exact targetZeroDefect_le_projectiveEnvelope
    him hoffline htne (high_primeInvisible_projective_height ht)

theorem high_zero_on_criticalLine_of_projective_gate
    {rhoStar : Zeros} {t : ℝ}
    (him : (rhoStar : ℂ).im = t)
    (ht : 18 <= t)
    (hgate :
      ∀ (g : ℝ → ℝ) (r Lambda CG : ℝ),
        GateData g t r Lambda →
        |clusterHeightDefect g t r|
          <= r ^ 2 * projectiveEnvelope g Lambda t CG →
        heightOf rhoStar ≠ 0 →
        r ^ 2 * projectiveEnvelope g Lambda t CG
          < zeroHeightDefect g r rhoStar) :
    heightOf rhoStar = 0 := by
  have htne : t ≠ 0 := by linarith
  exact no_offLineZero_of_projectiveEnvelope_lt_targetDefect
    him htne (high_primeInvisible_projective_height ht) hgate

theorem high_zero_realPart_eq_half_of_projective_gate
    {rhoStar : Zeros} {t : ℝ}
    (him : (rhoStar : ℂ).im = t)
    (ht : 18 <= t)
    (hgate :
      ∀ (g : ℝ → ℝ) (r Lambda CG : ℝ),
        GateData g t r Lambda →
        |clusterHeightDefect g t r|
          <= r ^ 2 * projectiveEnvelope g Lambda t CG →
        heightOf rhoStar ≠ 0 →
        r ^ 2 * projectiveEnvelope g Lambda t CG
          < zeroHeightDefect g r rhoStar) :
    (rhoStar : ℂ).re = 1 / 2 := by
  have h :=
    high_zero_on_criticalLine_of_projective_gate him ht hgate
  unfold heightOf at h
  linarith

end Synthesis


/-!
## 2026-09 completed-density frontier

The later projective tranche sharpens the old envelope-facing surface above.

Paid at source level:
* Gamma = the theorem-bearing mu pairing on the exact projective test;
* pole = the theorem-bearing Pi_X pairing on that same test;
* full zero carrier = completed smooth density (prime invisible);
* full reflection-pair zero carrier = normalized projective atom tsum;
* SameOrd q-only base vanishes exactly;
* SameOrd normalized atoms are -2 t times the positive height defect;
* the divided-square horizontal consumer is one physical cosine profile;
* strict q=0 sign, q-Lipschitz control, and q^-2 far decay are source-written;
* actual zeta zeros lie in the normalized strip |alpha| <= 1/(2t).

Crucial firewall:
  canonicalOffCompletedResidual t = clusterHeightDefect(g_t,t,r_t).

Hence under an actual off-line target,
  0 < 2 D_rho <= canonicalOffCompletedResidual t.

So the remaining high theorem is genuinely a strict signed estimate on the
off-ordinate completed residual obtained independently of the full-carrier
explicit-formula replacement.  A fixed positive absolute budget cannot close
uniformly as a_rho -> 0.
-/

structure CompletedProjectiveHighFrontierStatus where
  gammaMuSameObjectPaid : Bool
  polePiXSameObjectPaid : Bool
  completedSmoothCollapsePaid : Bool
  fullCarrierCancellationPaid : Bool
  fullNormalizedCarrierPaid : Bool
  sameOrdBaseZeroPaid : Bool
  sameOrdHeightDefectSignPaid : Bool
  horizontalSingleProfilePaid : Bool
  horizontalNearSignPaid : Bool
  horizontalFarDecayPaid : Bool
  actualAlphaStripPaid : Bool
  independentSignedCompletedResidualEstimatePaid : Bool
  uniformHighContradictionPaid : Bool

def completedProjectiveHighFrontierStatus :
    CompletedProjectiveHighFrontierStatus :=
  { gammaMuSameObjectPaid := true
    polePiXSameObjectPaid := true
    completedSmoothCollapsePaid := true
    fullCarrierCancellationPaid := true
    fullNormalizedCarrierPaid := true
    sameOrdBaseZeroPaid := true
    sameOrdHeightDefectSignPaid := true
    horizontalSingleProfilePaid := true
    horizontalNearSignPaid := true
    horizontalFarDecayPaid := true
    actualAlphaStripPaid := true
    independentSignedCompletedResidualEstimatePaid := false
    uniformHighContradictionPaid := false }

theorem independentSignedCompletedResidualEstimateStillOpen :
    completedProjectiveHighFrontierStatus
      .independentSignedCompletedResidualEstimatePaid = false := rfl

theorem uniformHighContradictionStillOpen_completed :
    completedProjectiveHighFrontierStatus.uniformHighContradictionPaid = false := rfl
