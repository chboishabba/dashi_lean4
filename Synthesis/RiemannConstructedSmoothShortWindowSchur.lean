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
        linarith [w.lowMiddleSeparated, w.middleOrdered,
          w.middleTopSeparated, htop]
      q0UpperShort := by
        linarith [w.middleTopSeparated, htop]
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
    lam_pos := one_pos
    envelope := env
    sigmaHeight_pos := hsigma
    sigmaHeight_lt_target := hord
    endpointGate := hgate
    endpointStrict := ?_
    sigmaMult_pos := zeroMultiplicity_pos sigma
    targetMult_pos := zeroMultiplicity_pos rho
    smoothPair := hsmooth
    evenPair := heven
    nonnegPair := by
      intro j u
      fin_cases j
      · rw [windowPair_zero]
        have hp := w.pNorm.nonneg u
        have hq := w.q0Norm.nonneg u
        linarith
      · rw [windowPair_one]
        have hp := w.pNorm.nonneg u
        have hq := w.q1Norm.nonneg u
        linarith
    twoPointPositive := by
      intro j
      fin_cases j
      · refine ⟨schurCenter0, schurCenter1, ?_, ?_, ?_⟩
        · rw [windowPair_zero]
          have hp : 0 < w.p schurCenter0 := by
            dsimp [w, w0, p]
            exact smoothWindow_pos_at_center hepos
          have hq : 0 ≤ w.q0 schurCenter0 := w.q0Norm.nonneg _
          linarith
        · rw [windowPair_zero]
          have hp : 0 ≤ w.p schurCenter1 := w.pNorm.nonneg _
          have hq : 0 < w.q0 schurCenter1 := by
            dsimp [w, w0, q0]
            exact smoothWindow_pos_at_center hepos
          linarith
        · rw [abs_of_pos schurCenter0_pos, abs_of_pos (lt_trans schurCenter0_pos schurCenter01)]
          exact ne_of_lt schurCenter01
      · refine ⟨schurCenter0, schurCenter2, ?_, ?_, ?_⟩
        · rw [windowPair_one]
          have hp : 0 < w.p schurCenter0 := by
            dsimp [w, w0, p]
            exact smoothWindow_pos_at_center hepos
          have hq : 0 ≤ w.q1 schurCenter0 := w.q1Norm.nonneg _
          linarith
        · rw [windowPair_one]
          have hp : 0 ≤ w.p schurCenter2 := w.pNorm.nonneg _
          have hq : 0 < w.q1 schurCenter2 := by
            dsimp [w, w0, q1]
            exact smoothWindow_pos_at_center hepos
          linarith
        · rw [abs_of_pos schurCenter0_pos,
            abs_of_pos (lt_trans (lt_trans schurCenter0_pos schurCenter01) schurCenter12)]
          exact ne_of_lt (lt_trans schurCenter01 schurCenter12)
  }⟩
  simpa [env, shortW] using hstrict

end Synthesis
