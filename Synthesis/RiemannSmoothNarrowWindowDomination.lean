import Synthesis.RiemannSmoothNormalizedWindow
import Zeta23Bridge.LiteralWeilNarrowWindowDomination
import Zeta23Bridge.WindowSchurSharedCertificate

/-!
# Smooth narrow-window domination

The imported narrow-window theorem proves the endpoint domination geometry for
arbitrary ordered centres. Its final witness used normalized tents. This module
replays only that last construction with the C^2 even normalized modulus-window
bumps from RiemannSmoothNormalizedWindow.

Thus the same domination defect gives an actual normalized narrow-window triple
whose three base tapers are C^2 and even.
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilWindowRatioSeparation
open Zeta23Bridge.LiteralWeilNormalizedWindowBounds
open Zeta23Bridge.LiteralWeilNarrowWindowDomination
open Zeta23Bridge.LiteralWeilDetRestBoundMonotonicity
open Zeta23Bridge.LiteralWeilLeadingCoefficientCovariance
open Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient
open Zeta23Bridge.CoshWindowSeparation
open Zeta23Bridge.NormalizedNarrowWindowCertificate
open Zeta23Bridge.WindowSchurSharedCertificate

structure SmoothNormalizedNarrowWindowTriple extends NormalizedNarrowWindowTriple where
  pSmooth : ContDiff ℝ 2 p
  q0Smooth : ContDiff ℝ 2 q0
  q1Smooth : ContDiff ℝ 2 q1
  pEven : ∀ u, p (-u) = p u
  q0Even : ∀ u, q0 (-u) = q0 u
  q1Even : ∀ u, q1 (-u) = q1 u

theorem exists_smoothNormalizedTriple_endpointComparison
    {lam a b c0 c1 c2 : ℝ}
    (hlam : lam ≠ 0)
    (ha : 0 < a) (hab : a < b)
    (hc0 : 0 < c0) (h01 : c0 < c1) (h12 : c1 < c2) :
    ∃ w : SmoothNormalizedNarrowWindowTriple,
      coshDiff b w.be0 w.be1 * coshDiff a w.al0 w.al2
        < coshDiff b w.al0 w.al2 * coshDiff a w.be0 w.be1
      ∧
      envelopeBudget
        (Zeta23Bridge.LiteralWeilWindowSchurInstance.exactEnvelope w.toNormalizedNarrowWindowTriple a b)
        lam
        <
      crossMargin w.toNormalizedNarrowWindowTriple lam a b := by
  obtain ⟨e0, he0pos, hall⟩ :=
    exists_narrow_radius hlam ha hab hc0 h01 h12
  obtain ⟨hec0, hord1, hord2, hgate, hdefect⟩ :=
    hall e0 he0pos le_rfl
  let e : ℝ := e0
  have hepos : 0 < e := by simpa [e] using he0pos
  have hp0 : 0 < c0 - e := by simpa [e] using hec0
  have hp1 : 0 < c1 - e := by
    dsimp [e]
    linarith
  have hp2 : 0 < c2 - e := by
    dsimp [e]
    linarith

  let p : ℝ → ℝ := smoothWindow c0 e
  let q0 : ℝ → ℝ := smoothWindow c1 e
  let q1 : ℝ → ℝ := smoothWindow c2 e

  have hpN : NormalizedWindowTaper p (c0 - e) (c0 + e) := by
    dsimp [p]
    exact smoothWindow_normalizedWindow hp0 hepos
  have hq0N : NormalizedWindowTaper q0 (c1 - e) (c1 + e) := by
    dsimp [q0]
    exact smoothWindow_normalizedWindow hp1 hepos
  have hq1N : NormalizedWindowTaper q1 (c2 - e) (c2 + e) := by
    dsimp [q1]
    exact smoothWindow_normalizedWindow hp2 hepos

  have hgate' :
      coshDiff b (c0 + e) (c1 + e) * coshDiff a (c0 - e) (c2 - e)
        <
      coshDiff b (c0 - e) (c2 - e) * coshDiff a (c0 + e) (c1 + e) := by
    unfold gateDefect at hgate
    linarith

  let w0 : NormalizedNarrowWindowTriple :=
    { p := p
      q0 := q0
      q1 := q1
      al0 := c0 - e
      be0 := c0 + e
      al1 := c1 - e
      be1 := c1 + e
      al2 := c2 - e
      be2 := c2 + e
      pNorm := hpN
      q0Norm := hq0N
      q1Norm := hq1N
      lowPositive := hp0
      lowOrdered := by linarith
      lowMiddleSeparated := by simpa [e] using hord1
      middleOrdered := by linarith
      middleTopSeparated := by simpa [e] using hord2 }

  have hb : 0 < b := ha.trans hab

  have hpw1 : WindowTaper p (c0 - e) (c1 + e) :=
    hpN.window.mono le_rfl (by linarith)
  have hq0w : WindowTaper q0 (c0 - e) (c1 + e) :=
    hq0N.window.mono (by linarith) le_rfl
  have hpw2 : WindowTaper p (c0 - e) (c2 + e) :=
    hpN.window.mono le_rfl (by linarith)
  have hq1w : WindowTaper q1 (c0 - e) (c2 + e) :=
    hq1N.window.mono (by linarith) le_rfl

  have capPa := targetLeadingCoeff_le_unitMass hpN.window hpN.unitMass ha hp0
  have capPb := targetLeadingCoeff_le_unitMass hpN.window hpN.unitMass hb hp0
  have capQ0a := targetLeadingCoeff_le_unitMass hq0N.window hq0N.unitMass ha hp1
  have capQ0b := targetLeadingCoeff_le_unitMass hq0N.window hq0N.unitMass hb hp1
  have capQ1a := targetLeadingCoeff_le_unitMass hq1N.window hq1N.unitMass ha hp2
  have capQ1b := targetLeadingCoeff_le_unitMass hq1N.window hq1N.unitMass hb hp2
  have capC0a := covForm_le_unitMass hpw1 hq0w hpN.unitMass hq0N.unitMass ha hp0
  have capC0b := covForm_le_unitMass hpw1 hq0w hpN.unitMass hq0N.unitMass hb hp0
  have capC1a := covForm_le_unitMass hpw2 hq1w hpN.unitMass hq1N.unitMass ha hp0
  have capC1b := covForm_le_unitMass hpw2 hq1w hpN.unitMass hq1N.unitMass hb hp0

  have floor0 :
      responseFloor a (c0 + e) (c1 - e) ≤ covForm p q0 a :=
    covForm_ge_unitMass hpN.window hq0N.window hpN.unitMass hq0N.unitMass
      ha hp0 (by linarith) (by linarith)
  have floor1 :
      responseFloor a (c0 + e) (c2 - e) ≤ covForm p q1 a :=
    covForm_ge_unitMass hpN.window hq1N.window hpN.unitMass hq1N.unitMass
      ha hp0 (by linarith) (by linarith)

  have hF0pos : 0 < responseFloor a (c0 + e) (c1 - e) :=
    responseFloor_pos ha (by linarith) (by linarith)
  have hF1pos : 0 < responseFloor a (c0 + e) (c2 - e) :=
    responseFloor_pos ha (by linarith) (by linarith)

  have hDtop : 0 < coshDiff a (c0 - e) (c2 - e) :=
    coshDiff_pos ha hp0 (by linarith)
  have hDbot : 0 < coshDiff a (c0 + e) (c1 + e) :=
    coshDiff_pos ha (by linarith) (by linarith)
  have hden : 0 < denomProduct a c0 c1 c2 e := by
    unfold denomProduct
    exact mul_pos hDtop hDbot

  have hgapeq :
      coshDiff b (c0 - e) (c2 - e) / coshDiff a (c0 - e) (c2 - e)
        - coshDiff b (c0 + e) (c1 + e) / coshDiff a (c0 + e) (c1 + e)
      =
      gateDefect a b c0 c1 c2 e / denomProduct a c0 c1 c2 e := by
    unfold gateDefect denomProduct
    field_simp

  have hgapnn :
      0 ≤
      coshDiff b (c0 - e) (c2 - e) / coshDiff a (c0 - e) (c2 - e)
        - coshDiff b (c0 + e) (c1 + e) / coshDiff a (c0 + e) (c1 + e) := by
    rw [hgapeq]
    exact (div_pos hgate hden).le

  have hdet :=
    Zeta23Bridge.LiteralWeilNarrowWindowDomination.covForm_det_ge
      hpN.window hq0N.window hq1N.window
      ha hab hp0 (by linarith) (by linarith) (by linarith) (by linarith)

  have hfloorprod :
      responseFloor a (c0 + e) (c1 - e)
          * responseFloor a (c0 + e) (c2 - e)
          *
          (coshDiff b (c0 - e) (c2 - e) / coshDiff a (c0 - e) (c2 - e)
            - coshDiff b (c0 + e) (c1 + e) / coshDiff a (c0 + e) (c1 + e))
        ≤
      covForm p q0 a * covForm p q1 a
          *
          (coshDiff b (c0 - e) (c2 - e) / coshDiff a (c0 - e) (c2 - e)
            - coshDiff b (c0 + e) (c1 + e) / coshDiff a (c0 + e) (c1 + e)) := by
    have h1 : 0 ≤ covForm p q0 a := le_trans hF0pos.le floor0
    refine mul_le_mul_of_nonneg_right ?_ hgapnn
    exact mul_le_mul floor0 floor1 hF1pos.le h1

  have hbudget :
      endpointBudget lam a b c0 c1 c2 e
        <
      marginFloor lam a c0 c1 c2 e
        * (gateDefect a b c0 c1 c2 e / denomProduct a c0 c1 c2 e) := by
    rw [← mul_div_assoc, lt_div_iff₀ hden]
    unfold dominationDefect at hdefect
    linarith

  have hmarginle :
      marginFloor lam a c0 c1 c2 e
        * (gateDefect a b c0 c1 c2 e / denomProduct a c0 c1 c2 e)
      ≤
      4 * lam ^ 2 *
        (covForm p q0 a * covForm p q1 b
          - covForm p q1 a * covForm p q0 b) := by
    have hlam2 : (0 : ℝ) < 4 * lam ^ 2 := by positivity
    have hchain :
        responseFloor a (c0 + e) (c1 - e)
            * responseFloor a (c0 + e) (c2 - e)
            * (gateDefect a b c0 c1 c2 e / denomProduct a c0 c1 c2 e)
          ≤
        covForm p q0 a * covForm p q1 b
          - covForm p q1 a * covForm p q0 b := by
      rw [← hgapeq]
      exact hfloorprod.trans hdet
    unfold marginFloor
    nlinarith [hchain, hlam2]

  have hmono :=
    detRestBound_mono
      (lam := lam)
      hpN.window.cont hpN.window.cpt
      hq0N.window.cont hq0N.window.cpt
      hq1N.window.cont hq1N.window.cpt
      hpN.window.nonneg hq0N.window.nonneg hq1N.window.nonneg
      capPa capPb capQ0a capQ0b capQ1a capQ1b
      capC0a capC0b capC1a capC1b

  have hstrict :
      Zeta23Bridge.LiteralWeilLeadingCoefficientCovariance.detRestBound
          p q0 q1 lam a b
        <
      4 * lam ^ 2 *
        (covForm p q0 a * covForm p q1 b
          - covForm p q1 a * covForm p q0 b) := by
    calc
      Zeta23Bridge.LiteralWeilLeadingCoefficientCovariance.detRestBound
          p q0 q1 lam a b
        ≤ endpointBudget lam a b c0 c1 c2 e := hmono
      _ < marginFloor lam a c0 c1 c2 e
          * (gateDefect a b c0 c1 c2 e / denomProduct a c0 c1 c2 e) := hbudget
      _ ≤ _ := hmarginle

  let w : SmoothNormalizedNarrowWindowTriple :=
    { w0 with
      pSmooth := by dsimp [w0, p]; exact smoothWindow_contDiff hepos
      q0Smooth := by dsimp [w0, q0]; exact smoothWindow_contDiff hepos
      q1Smooth := by dsimp [w0, q1]; exact smoothWindow_contDiff hepos
      pEven := by intro u; dsimp [w0, p]; exact smoothWindow_even c0 e u
      q0Even := by intro u; dsimp [w0, q0]; exact smoothWindow_even c1 e u
      q1Even := by intro u; dsimp [w0, q1]; exact smoothWindow_even c2 e u }

  refine ⟨w, hgate', ?_⟩
  rw [Zeta23Bridge.LiteralWeilWindowSchurInstance.envelopeBudget_exactEnvelope]
  exact hstrict

end Synthesis
