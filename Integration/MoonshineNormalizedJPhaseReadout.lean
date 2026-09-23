import Integration.MoonshineEisensteinAgdaTarget
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Concrete continuous phase readout for normalized modular j

The Agda normalized renderer still leaves its atan2/phase carrier abstract.
On the Lean/Mathlib target we can close the continuous phase part canonically:

  jPhase(τ) = Arg(jTarget τ) : Real.Angle.

Using Real.Angle instead of a raw real-valued branch of arg is deliberate.
Mathlib proves conjugation acts by exact additive negation on this quotient,
with no special-case ambiguity at ±π.

This module does NOT choose:
* a colour map;
* a tone map;
* C3/C6/C9/C27 sector quantizers.

Those remain presentation/finite-observer choices.  What is closed here is the
continuous normalized-j phase and its reflection law.
-/

namespace Integration.MoonshineNormalizedJPhaseReadout

open Complex Real
open UpperHalfPlane hiding I
open scoped Real MatrixGroups

noncomputable section

namespace Target
open Integration.MoonshineEisensteinAgdaTarget
end Target

/-- The concrete normalized modular-j value already owned by route B. -/
abbrev jValue (τ : ℍ) : ℂ :=
  Target.jTarget τ

/-- Canonical continuous phase carrier: argument modulo one full turn. -/
def jPhase (τ : ℍ) : Real.Angle :=
  (Complex.arg (jValue τ) : Real.Angle)

/-- Cartesian readout fields needed by the Agda renderer. -/
def jRealPart (τ : ℍ) : ℝ := (jValue τ).re

def jImagPart (τ : ℍ) : ℝ := (jValue τ).im

/-- Canonical magnitude/tone scalar before any colour calibration. -/
def jMagnitude (τ : ℍ) : ℝ := ‖jValue τ‖

/-- Weight-zero reflection conjugates the exact complex j value. -/
theorem jValue_reflects (τ : ℍ) :
    jValue (ModularGroup.S • Target.negConj τ) =
      conj (jValue τ) :=
  Target.jTarget_inv_conj τ

/-- The continuous phase reflection is exact negation in Real.Angle. -/
theorem jPhase_reflects (τ : ℍ) :
    jPhase (ModularGroup.S • Target.negConj τ) =
      - jPhase τ := by
  rw [jPhase, jPhase, jValue_reflects]
  exact Complex.arg_conj_coe_angle (jValue τ)

/-- Real part is reflection-even. -/
theorem jRealPart_reflects (τ : ℍ) :
    jRealPart (ModularGroup.S • Target.negConj τ) =
      jRealPart τ := by
  rw [jRealPart, jRealPart, jValue_reflects]
  simp

/-- Imaginary part is reflection-odd. -/
theorem jImagPart_reflects (τ : ℍ) :
    jImagPart (ModularGroup.S • Target.negConj τ) =
      - jImagPart τ := by
  rw [jImagPart, jImagPart, jValue_reflects]
  simp

/-- Magnitude/tone scalar is reflection-even. -/
theorem jMagnitude_reflects (τ : ℍ) :
    jMagnitude (ModularGroup.S • Target.negConj τ) =
      jMagnitude τ := by
  rw [jMagnitude, jMagnitude, jValue_reflects]
  simp

/-- On the reciprocal-conjugate fixed locus, the phase is self-negative. -/
theorem jPhase_unitCircle_selfNeg
    (τ : ℍ)
    (hunit : Complex.normSq (τ : ℂ) = 1) :
    jPhase τ = - jPhase τ := by
  have hfix := Target.S_negConj_fixed_of_normSq_one τ hunit
  calc
    jPhase τ =
        jPhase (ModularGroup.S • Target.negConj τ) := by
      exact congrArg jPhase hfix.symm
    _ = - jPhase τ := jPhase_reflects τ

/-- Equivalent exact-j reality statement already proved in the target lane. -/
theorem jImagPart_unitCircle_zero
    (τ : ℍ)
    (hunit : Complex.normSq (τ : ℂ) = 1) :
    jImagPart τ = 0 :=
  Target.jTarget_unitCircle_im_zero τ hunit

/-- Concrete continuous readout package.

Finite observers remain separate because a sector quantizer is additional
presentation data, not forced by Complex.arg itself.
-/
structure ContinuousJReadout where
  value : ℍ → ℂ
  realPart : ℍ → ℝ
  imagPart : ℍ → ℝ
  phase : ℍ → Real.Angle
  magnitude : ℍ → ℝ

  valueIsJ : ∀ τ, value τ = jValue τ
  phaseIsArg : ∀ τ, phase τ = jPhase τ

  valueReflects :
    ∀ τ,
      value (ModularGroup.S • Target.negConj τ) =
        conj (value τ)

  phaseReflects :
    ∀ τ,
      phase (ModularGroup.S • Target.negConj τ) =
        - phase τ

def canonicalContinuousJReadout : ContinuousJReadout where
  value := jValue
  realPart := jRealPart
  imagPart := jImagPart
  phase := jPhase
  magnitude := jMagnitude

  valueIsJ := fun _ => rfl
  phaseIsArg := fun _ => rfl
  valueReflects := jValue_reflects
  phaseReflects := jPhase_reflects

structure ContinuousJReadoutBoundary where
  normalizedStandardJValueConcrete : Bool
  realPartConcrete : Bool
  imagPartConcrete : Bool
  continuousPhaseUsesComplexArg : Bool
  phaseCarrierIsFullTurnQuotient : Bool
  phaseReflectionOwned : Bool
  magnitudeReadoutConcrete : Bool
  fixedLocusPhaseSelfNegationOwned : Bool

  colourCalibrationChosen : Bool
  toneCalibrationChosen : Bool
  finiteC3QuantizerChosen : Bool
  finiteC6QuantizerChosen : Bool
  finiteC9QuantizerChosen : Bool
  finiteC27QuantizerChosen : Bool

def continuousJReadoutBoundary : ContinuousJReadoutBoundary where
  normalizedStandardJValueConcrete := true
  realPartConcrete := true
  imagPartConcrete := true
  continuousPhaseUsesComplexArg := true
  phaseCarrierIsFullTurnQuotient := true
  phaseReflectionOwned := true
  magnitudeReadoutConcrete := true
  fixedLocusPhaseSelfNegationOwned := true

  colourCalibrationChosen := false
  toneCalibrationChosen := false
  finiteC3QuantizerChosen := false
  finiteC6QuantizerChosen := false
  finiteC9QuantizerChosen := false
  finiteC27QuantizerChosen := false

end

end Integration.MoonshineNormalizedJPhaseReadout
