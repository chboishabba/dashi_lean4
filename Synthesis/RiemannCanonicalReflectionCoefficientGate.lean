import Synthesis.RiemannArbitraryRadiusTargetRemainder
import Synthesis.RiemannCanonicalGateData
import Synthesis.RiemannCanonicalLeadingSignalFloor
import Synthesis.RiemannSmoothWindowLeadingSignal
import Synthesis.RiemannReflectionDoubledProjectiveGate
import Zeta23Bridge.LiteralWeilProjectiveSeparationGate

/-!
# Fully instantiated canonical reflection coefficient gate

Fix the actual high-side taper and radius:

  g_t = quantitativeCanonicalTaper t,
  r_t = quantitativeSampleRadius t = t/16,
  Lambda_t = 9*pi/(4*t).

The taper is now a literal GateData inhabitant.  For an off-line zero rho at
ordinate t, choose the positive-height member rho+ of its functional-equation
orbit.  The reflection pair doubles the signal, and the canonical two-window
geometry supplies an explicit lower bound for its leading coefficient.

The only remaining sufficient inequality is therefore the finite coefficient
comparison

  E_proj(g_t,Lambda_t,t,CG)
    + 2 r_t^2 R4(g_t,rho+)
    + 2 r_t^4 R6(g_t,rho+)
  <
    4 mult(rho+) canonicalCrossSignalFloor(t,height(rho+)).

No small-radius assumption remains.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
open Zeta23Bridge.LiteralWeilProjectiveSeparationGate
open Zeta23Bridge.LiteralWeilTwoRadiusSeparationGate
open Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient

def canonicalProjectiveLambda (t : ℝ) : ℝ :=
  9 * Real.pi / (4 * t)

def canonicalProjectiveEnvelope (t CG : ℝ) : ℝ :=
  projectiveEnvelope
    (quantitativeCanonicalTaper t)
    (canonicalProjectiveLambda t)
    t CG

def canonicalReflectionRemainder4 (t : ℝ) (rho : Zeros) : ℝ :=
  zeroRemainder4
    (quantitativeCanonicalTaper t)
    (positiveHeightRepresentative rho)

def canonicalReflectionRemainder6 (t : ℝ) (rho : Zeros) : ℝ :=
  zeroRemainder6
    (quantitativeCanonicalTaper t)
    (positiveHeightRepresentative rho)

def canonicalReflectionSignalFloor (t : ℝ) (rho : Zeros) : ℝ :=
  4 * ((zetaZeroConfig).mult (positiveHeightRepresentative rho) : ℝ)
    * canonicalCrossSignalFloor
      t (heightOf (positiveHeightRepresentative rho))

theorem canonicalReflectionSignalFloor_pos
    {t : ℝ} {rho : Zeros}
    (ht : 18 <= t)
    (hoff : heightOf rho ≠ 0) :
    0 < canonicalReflectionSignalFloor t rho := by
  have ha :
      0 < heightOf (positiveHeightRepresentative rho) :=
    positiveHeightRepresentative_height_pos hoff
  have hf := canonicalCrossSignalFloor_pos ht ha
  have hm :
      0 < ((zetaZeroConfig).mult
        (positiveHeightRepresentative rho) : ℝ) :=
    zeroMultiplicity_pos (positiveHeightRepresentative rho)
  unfold canonicalReflectionSignalFloor
  positivity

theorem canonicalReflectionSignalFloor_le_doubledLeading
    {t : ℝ} {rho : Zeros}
    (ht : 18 <= t)
    (hoff : heightOf rho ≠ 0) :
    canonicalReflectionSignalFloor t rho
      <=
    2 * zeroLeadingCoeff
      (quantitativeCanonicalTaper t)
      (positiveHeightRepresentative rho) := by
  let rhoP := positiveHeightRepresentative rho
  have ha : 0 < heightOf rhoP := by
    dsimp [rhoP]
    exact positiveHeightRepresentative_height_pos hoff
  have hfloor :=
    canonicalCrossSignalFloor_le_targetLeadingCoeff ht ha
  have hm : 0 <= ((zetaZeroConfig).mult rhoP : ℝ) := by
    positivity
  unfold canonicalReflectionSignalFloor zeroLeadingCoeff
  dsimp [rhoP]
  have hscaled :=
    mul_le_mul_of_nonneg_left hfloor
      (by positivity :
        (0 : ℝ) <= 4 * ((zetaZeroConfig).mult rhoP : ℝ))
  nlinarith

theorem false_of_canonicalReflectionCoefficientGate
    {t CG : ℝ} {rho : Zeros}
    (ht : 18 <= t)
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0)
    (hCG0 : 0 <= CG)
    (henv :
      |clusterHeightDefect
          (quantitativeCanonicalTaper t)
          t (quantitativeSampleRadius t)|
        <=
      (quantitativeSampleRadius t) ^ 2
        * canonicalProjectiveEnvelope t CG)
    (hcoeff :
      canonicalProjectiveEnvelope t CG
        + 2 * (quantitativeSampleRadius t) ^ 2
          * canonicalReflectionRemainder4 t rho
        + 2 * (quantitativeSampleRadius t) ^ 4
          * canonicalReflectionRemainder6 t rho
      <
      canonicalReflectionSignalFloor t rho) :
    False := by
  let rhoP := positiveHeightRepresentative rho
  have hPim : ((rhoP : Zeros) : ℂ).im = t := by
    dsimp [rhoP]
    rw [positiveHeightRepresentative_im]
    exact him
  have hPheight : 0 < heightOf rhoP := by
    dsimp [rhoP]
    exact positiveHeightRepresentative_height_pos hoff
  have hPoff : heightOf rhoP ≠ 0 := ne_of_gt hPheight

  have hfloor :=
    canonicalReflectionSignalFloor_le_doubledLeading ht hoff

  have hcmp :
      canonicalProjectiveEnvelope t CG
        + 2 * (quantitativeSampleRadius t) ^ 2
          * zeroRemainder4
            (quantitativeCanonicalTaper t) rhoP
        + 2 * (quantitativeSampleRadius t) ^ 4
          * zeroRemainder6
            (quantitativeCanonicalTaper t) rhoP
      <
      2 * zeroLeadingCoeff
        (quantitativeCanonicalTaper t) rhoP := by
    unfold canonicalReflectionRemainder4
      canonicalReflectionRemainder6 at hcoeff
    dsimp [rhoP] at hcoeff
    exact lt_of_lt_of_le hcoeff hfloor

  have hsep :
      (quantitativeSampleRadius t) ^ 2
          * canonicalProjectiveEnvelope t CG
        <
      2 * zeroHeightDefect
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t) rhoP := by
    exact
      reflectionPair_gate_of_arbitraryRadius_coefficientComparison
        (quantitativeCanonicalTaper_contDiff ht).continuous
        (quantitativeCanonicalTaper_compact ht)
        rhoP
        (quantitativeSampleRadius t)
        (canonicalProjectiveEnvelope t CG)
        (by
          unfold quantitativeSampleRadius
          positivity)
        hcmp

  have hd :
      GateData
        (quantitativeCanonicalTaper t)
        t
        (quantitativeSampleRadius t)
        (canonicalProjectiveLambda t) := by
    unfold canonicalProjectiveLambda
    exact quantitativeCanonicalGateData ht

  exact false_of_projectiveEnvelope_lt_reflectionPairDefect
    hd
    (by
      unfold canonicalProjectiveEnvelope at henv
      exact henv)
    hPim hPoff
    (by
      unfold canonicalProjectiveEnvelope at hsep
      exact hsep)

/--
The projective envelope theorem supplies CG automatically.  Thus, for every
off-line zero in the high region, one concrete finite coefficient inequality is
sufficient for contradiction.
-/
theorem exists_canonicalReflectionCoefficientGate
    {t : ℝ} {rho : Zeros}
    (ht : 18 <= t)
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0) :
    ∃ CG : ℝ, 0 <= CG ∧
      (canonicalProjectiveEnvelope t CG
          + 2 * (quantitativeSampleRadius t) ^ 2
            * canonicalReflectionRemainder4 t rho
          + 2 * (quantitativeSampleRadius t) ^ 4
            * canonicalReflectionRemainder6 t rho
        <
        canonicalReflectionSignalFloor t rho
        ->
        False) := by
  obtain ⟨CG, hCG0, henvAll⟩ := exists_projectiveEnvelope
  have hd :
      GateData
        (quantitativeCanonicalTaper t)
        t
        (quantitativeSampleRadius t)
        (canonicalProjectiveLambda t) := by
    unfold canonicalProjectiveLambda
    exact quantitativeCanonicalGateData ht
  have henv := henvAll hd
  refine ⟨CG, hCG0, ?_⟩
  intro hcoeff
  exact false_of_canonicalReflectionCoefficientGate
    ht him hoff hCG0
    (by
      unfold canonicalProjectiveEnvelope
      exact henv)
    hcoeff

end Synthesis
