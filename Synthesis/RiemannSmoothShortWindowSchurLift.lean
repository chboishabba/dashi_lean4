import Synthesis.RiemannHighOneZeroSchurCutset
import Synthesis.RiemannShortWindowSchurCompiler
import Zeta23Bridge.WindowSchurSharedCertificate

/-!
# Smooth short-window Schur lift

The imported narrow-window construction already proves the response-separation
statement needed to remove one selected zero direction.  Its concrete tent
tapers are packaged at the Continuous/compact-support level, whereas the literal
explicit-formula balance used by the high cutset requires ContDiff R 2 tapers.

This module keeps that representation debt explicit.  Given one short normalized
window certificate plus a C^2 lift on the *same windowPair functions*, the
existing endpoint comparison compiles directly to:

  * prime-invisible short support;
  * an actual small-radius interval;
  * exact survival of the target after nuisance-zero projection.

No far-tail estimate is introduced here.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.MultiTaperSchurCore
open Zeta23Bridge.LiteralWeilTwoTaperCoefficientGate
open Zeta23Bridge.LiteralWeilWindowSchurAdmission
open Zeta23Bridge.WindowSchurSharedCertificate
open Zeta23Bridge.NormalizedNarrowWindowCertificate

structure SmoothShortWindowSchurCertificate
    (sigma rho : Zeros) where
  windows : ShortNormalizedWindowTriple
  lam : ℝ
  envelope :
    ResponseEnvelope windows.triple (heightOf sigma) (heightOf rho)

  sigmaHeight_pos : 0 < heightOf sigma
  sigmaHeight_lt_target : heightOf sigma < heightOf rho

  endpointGate :
    Zeta23Bridge.CoshWindowSeparation.coshDiff
        (heightOf rho) windows.triple.be0 windows.triple.be1
      *
      Zeta23Bridge.CoshWindowSeparation.coshDiff
        (heightOf sigma) windows.triple.al0 windows.triple.al2
      <
    Zeta23Bridge.CoshWindowSeparation.coshDiff
        (heightOf rho) windows.triple.al0 windows.triple.al2
      *
      Zeta23Bridge.CoshWindowSeparation.coshDiff
        (heightOf sigma) windows.triple.be0 windows.triple.be1

  endpointStrict :
    envelopeBudget envelope lam
      <
    crossMargin windows.triple lam (heightOf sigma) (heightOf rho)

  sigmaMult_pos :
    0 < ((zetaZeroConfig).mult sigma : ℝ)
  targetMult_pos :
    0 < ((zetaZeroConfig).mult rho : ℝ)

  smoothPair :
    ∀ j, ContDiff ℝ 2
      (windowPair windows.triple.p windows.triple.q0 windows.triple.q1 lam j)

  evenPair :
    ∀ j u,
      windowPair windows.triple.p windows.triple.q0 windows.triple.q1 lam j (-u)
        =
      windowPair windows.triple.p windows.triple.q0 windows.triple.q1 lam j u

namespace SmoothShortWindowSchurCertificate

variable {sigma rho : Zeros}
variable (C : SmoothShortWindowSchurCertificate sigma rho)

def g : Fin 2 → ℝ → ℝ :=
  windowPair C.windows.triple.p C.windows.triple.q0 C.windows.triple.q1 C.lam

theorem continuousPair : ∀ j, Continuous (C.g j) :=
  fun j => (C.smoothPair j).continuous

theorem compactPair : ∀ j, HasCompactSupport (C.g j) := by
  exact windowPair_compactSupport
    C.windows.triple.pNorm.compactSupport
    C.windows.triple.q0Norm.compactSupport
    C.windows.triple.q1Norm.compactSupport
    C.lam

theorem shortPair :
    ∀ j u, C.g j u ≠ 0 → |u| < Real.log 2 := by
  exact C.windows.windowPair_short C.lam

theorem exists_radius_targetProjected_ne_zero :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 ≤ 1 ∧
      ∀ r : ℝ, 0 < r → r ≤ r0 →
        targetProjected C.g r rho sigma ≠ 0 := by
  obtain ⟨r0, hr0, hr01, hsurvive⟩ :=
    exists_radius_transverseComp_ne_zero_of_endpointComparison
      C.envelope C.lam
      C.sigmaHeight_pos C.sigmaHeight_lt_target
      C.endpointGate C.endpointStrict
      C.sigmaMult_pos C.targetMult_pos
  refine ⟨r0, hr0, hr01, ?_⟩
  intro r hr hrle
  exact hsurvive r hr hrle

/--
The stronger admission receipt keeps the positive Gram wedge.  It therefore
supplies both facts needed by the exact cutset: the nuisance response is nonzero
and the target survives its orthogonal removal.
-/
theorem exists_radius_nuisance_ne_zero_and_target_survives :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 ≤ 1 ∧
      ∀ r : ℝ, 0 < r → r ≤ r0 →
        zeroRespVec C.g r sigma ≠ 0
          ∧ targetProjected C.g r rho sigma ≠ 0 := by
  have hdom :
      |Zeta23Bridge.LiteralWeilLeadingCoefficientCovariance.detRest
          C.windows.triple.p C.windows.triple.q0 C.windows.triple.q1
          C.lam (heightOf sigma) (heightOf rho)|
        <
      crossMargin C.windows.triple C.lam (heightOf sigma) (heightOf rho) :=
    hdom_of_endpointComparison C.envelope C.lam C.endpointStrict

  have hL : leadingCrossDet C.g sigma rho ≠ 0 := by
    change leadingCrossDet
      (windowPair C.windows.triple.p C.windows.triple.q0
        C.windows.triple.q1 C.lam) sigma rho ≠ 0
    exact
      (leadingCrossDet_windowPair_ne_zero
        C.windows.triple.pWindow
        C.windows.triple.q0Window
        C.windows.triple.q1Window
        C.windows.triple.lowPositive
        C.windows.triple.lowOrdered
        C.windows.triple.lowMiddleSeparated
        C.windows.triple.middleOrdered
        C.windows.triple.middleTopSeparated
        C.sigmaHeight_pos
        C.sigmaHeight_lt_target
        C.endpointGate
        hdom
        C.sigmaMult_pos
        C.targetMult_pos).2

  obtain ⟨r0, hr0, hr01, hwedge⟩ :=
    exists_radius_wedgeSq_pos
      C.continuousPair C.compactPair hL

  refine ⟨r0, hr0, hr01, ?_⟩
  intro r hr hrle
  have hw :
      0 < wedgeSq
        (zeroRespVec C.g r sigma)
        (zeroRespVec C.g r rho) :=
    hwedge r hr hrle
  have hn : zeroRespVec C.g r sigma ≠ 0 := by
    intro hz
    rw [hz] at hw
    simp [wedgeSq, normSqP, dotP] at hw
  have ht :
      targetProjected C.g r rho sigma ≠ 0 := by
    unfold targetProjected
    exact transverseComp_ne_zero_of_wedgeSq_pos hw
  exact ⟨hn, ht⟩

end SmoothShortWindowSchurCertificate

end Synthesis
