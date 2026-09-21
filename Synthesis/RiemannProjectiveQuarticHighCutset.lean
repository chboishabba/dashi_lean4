import Synthesis.RiemannProjectiveQuarticTargetPairResidual
import Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition

/-!
# Prize-facing high cutset for the quartic-escape detector

For t>=100 the physical signed quartic profile is C², compactly supported,
even, and supported strictly inside (-log 2,log 2).  Hence the literal prime
channel vanishes exactly and the projective explicit formula gives

  D_cluster^Q
    = D_off^{Q,proj} + D_Gamma^{Q,proj} + D_pole^{Q,proj}.

If additionally 8/t<eps_Q, the same-ordinate quartic cluster satisfies

  2 D_rho^Q <= D_cluster^Q

for every hypothetical off-line target rho at ordinate t.

Therefore any independent strict external upper estimate below 2D_rho^Q is
already contradictory.  This is the quartic analogue of the canonical signed
reflection-pair cutset, but it does not use GateData.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile

theorem quartic_cluster_eq_threeProjectiveChannels
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 100 ≤ t) :
    clusterHeightDefect
        (quarticPhysicalDetector W.R W.lam t)
        t (t/16)
      =
    offOrdProjectiveDefect
        (quarticPhysicalDetector W.R W.lam t)
        t (t/16)
      +
    gammaProjectiveDefect
        (quarticPhysicalDetector W.R W.lam t)
        t (t/16)
      +
    poleProjectiveDefect
        (quarticPhysicalDetector W.R W.lam t)
        t (t/16) := by
  have htpos : 0 < t := by linarith
  have hsmooth :=
    quarticPhysicalDetector_contDiff
      (t := t) (lam := W.lam) W.Rpos
  have hcompact :=
    quarticPhysicalDetector_compact
      (t := t) (lam := W.lam) W.Rpos htpos
  have heven :=
    quarticPhysicalDetector_even W.R W.lam t
  have hshort :
      ∀ u,
        quarticPhysicalDetector W.R W.lam t u ≠ 0 ->
          |u| < Real.log 2 := by
    exact physicalQuarticProfile_short_of_hundred
      W.Rpos W.RltOne ht
  exact clusterHeightDefect_eq_threeProjectiveChannels
    hsmooth hcompact heven hshort t (t/16)

/--
The single strict inequality that would close the high quartic route.
-/
theorem false_of_quartic_external_strict
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 100 ≤ t)
    (hhigh : 8/t < W.eps)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0)
    (hstrict :
      offOrdProjectiveDefect
          (quarticPhysicalDetector W.R W.lam t)
          t (t/16)
        +
      gammaProjectiveDefect
          (quarticPhysicalDetector W.R W.lam t)
          t (t/16)
        +
      poleProjectiveDefect
          (quarticPhysicalDetector W.R W.lam t)
          t (t/16)
        <
      2 *
        zeroHeightDefect
          (quarticPhysicalDetector W.R W.lam t)
          (t/16) rho) :
    False := by
  have htpos : 0 < t := by linarith
  have hlo :=
    quartic_cluster_ge_two_target
      W htpos hhigh him hoff
  rw [quartic_cluster_eq_threeProjectiveChannels W ht] at hlo
  linarith

end Synthesis
