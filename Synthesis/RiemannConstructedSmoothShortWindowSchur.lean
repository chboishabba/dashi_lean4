import Synthesis.RiemannSmoothNarrowWindowDomination
import Synthesis.RiemannSmoothShortWindowSchurLift

/-!
# Constructed smooth short-window Schur certificate

This module instantiates the smooth narrow-window existence theorem at three
fixed centres below log 2 and packages the result directly into the
SmoothShortWindowSchurCertificate consumed by the corrected high cutset.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilWindowSchurAdmission
open Zeta23Bridge.LiteralWeilWindowSchurInstance
open Zeta23Bridge.WindowSchurSharedCertificate
open Zeta23Bridge.NormalizedNarrowWindowCertificate

def schurCenter0 : ℝ := Real.log 2 / 8
def schurCenter1 : ℝ := Real.log 2 / 4
def schurCenter2 : ℝ := 3 * Real.log 2 / 8

theorem schurCenter0_pos : 0 < schurCenter0 := by
  unfold schurCenter0
  have h := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  positivity

theorem schurCenter01 : schurCenter0 < schurCenter1 := by
  unfold schurCenter0 schurCenter1
  have h := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  nlinarith

theorem schurCenter12 : schurCenter1 < schurCenter2 := by
  unfold schurCenter1 schurCenter2
  have h := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  nlinarith

theorem schurCenter2_short : schurCenter2 < Real.log 2 := by
  unfold schurCenter2
  have h := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  nlinarith

theorem zeroMultiplicity_pos (rho : Zeros) :
    0 < ((zetaZeroConfig).mult rho : ℝ) := by
  have hnat : 1 ≤ (zetaZeroConfig).mult rho :=
    (zetaZeroConfig).one_le_mult (rho : ℂ) rho.2
  exact_mod_cast hnat

theorem exists_constructedSmoothShortWindowSchurCertificate
    {sigma rho : Zeros}
    (hsigma : 0 < heightOf sigma)
    (hord : heightOf sigma < heightOf rho) :
    Nonempty (SmoothShortWindowSchurCertificate sigma rho) := by
  obtain ⟨w, hgate, hstrict, htop⟩ :=
    exists_smoothNormalizedTriple_endpointComparison
      (lam := (1 : ℝ))
      (a := heightOf sigma)
      (b := heightOf rho)
      (c0 := schurCenter0)
      (c1 := schurCenter1)
      (c2 := schurCenter2)
      one_ne_zero
      hsigma hord
      schurCenter0_pos schurCenter01 schurCenter12 schurCenter2_short

  let shortW : ShortNormalizedWindowTriple :=
    { triple := w.toNormalizedNarrowWindowTriple
      pUpperShort := by
        exact lt_trans w.lowMiddleSeparated
          (lt_trans (le_lt_of_le_of_lt w.middleOrdered w.middleTopSeparated)
            (lt_of_le_of_lt (le_of_lt w.middleTopSeparated) htop))
      q0UpperShort := by
        exact lt_trans w.middleTopSeparated
          (lt_of_le_of_lt (by linarith : w.be2 ≤ w.be2) htop)
      q1UpperShort := htop }

  let env :=
    exactEnvelope w.toNormalizedNarrowWindowTriple
      (heightOf sigma) (heightOf rho)

  have hsmooth :
      ∀ j, ContDiff ℝ 2
        (windowPair w.p w.q0 w.q1 (1 : ℝ) j) := by
    intro j
    fin_cases j
    · rw [windowPair_zero]
      exact w.pSmooth.add (w.q0Smooth.const_smul 1)
    · rw [windowPair_one]
      exact w.pSmooth.add (w.q1Smooth.const_smul 1)

  have heven :
      ∀ j u,
        windowPair w.p w.q0 w.q1 (1 : ℝ) j (-u)
          =
        windowPair w.p w.q0 w.q1 (1 : ℝ) j u := by
    intro j u
    fin_cases j
    · rw [windowPair_zero, windowPair_zero, w.pEven, w.q0Even]
    · rw [windowPair_one, windowPair_one, w.pEven, w.q1Even]

  refine ⟨{
    windows := shortW
    lam := 1
    envelope := env
    sigmaHeight_pos := hsigma
    sigmaHeight_lt_target := hord
    endpointGate := hgate
    endpointStrict := ?_
    sigmaMult_pos := zeroMultiplicity_pos sigma
    targetMult_pos := zeroMultiplicity_pos rho
    smoothPair := hsmooth
    evenPair := heven
  }⟩
  simpa [env, shortW] using hstrict

end Synthesis
