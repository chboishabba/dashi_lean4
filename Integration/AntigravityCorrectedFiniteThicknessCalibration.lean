import Integration.AntigravityCorrectedSourceGeometryWeld
import Integration.AntigravitySourceNativeAnisotropicYMProfile

namespace Integration.AntigravityCorrectedFiniteThicknessCalibration

open Integration.AntigravityCorrectedSourceGeometryWeld
open Integration.AntigravitySourceNativeAnisotropicYMProfile
open Integration.AntigravityFiniteThicknessTOVTransition

/-!
AG-CAL / corrected source-unit + length calibration.

Calibration is allowed only after a source-native anisotropic stress profile has
been supplied.  Matching the Kottler amplitude alone is not treated as a
source-to-geometry theorem.
-/

def correctedFiniteThicknessRequiredStressLengthSquaredLower
    (source : AgdaLorentzianActiveSourceReceipt) : Rat :=
  correctedRequiredStressLengthSquaredLowerFor
    finiteThicknessKottlerTarget source

def correctedFiniteThicknessRequiredStressLengthSquaredUpper
    (source : AgdaLorentzianActiveSourceReceipt) : Rat :=
  correctedRequiredStressLengthSquaredUpperFor
    finiteThicknessKottlerTarget source

theorem corrected_finite_thickness_required_scale_interval_ordered
    (source : AgdaLorentzianActiveSourceReceipt) :
    correctedFiniteThicknessRequiredStressLengthSquaredLower source
      ≤ correctedFiniteThicknessRequiredStressLengthSquaredUpper source := by
  exact corrected_required_scale_interval_ordered
    finiteThicknessKottlerTarget source
    (le_of_lt finite_thickness_kottler_target_positive)

structure CorrectedFiniteThicknessSourceCalibrationWitness
    (source : AgdaLorentzianActiveSourceReceipt)
    (profile : SourceNativeAnisotropicYMProfile)
    (profileGeometry : SourceNativeYMFiniteThicknessTarget profile)
    (calibration :
      CorrectedPhysicalStressLengthSquaredCalibration
        source finiteThicknessKottlerTarget) : Prop where
  sourceActiveNegative :
    source.activeConnectedNumerator < 0
  sourceMagnitudePositive :
    0 < source.sourceMagnitude
  scaleInsideRequiredInterval :
    correctedFiniteThicknessRequiredStressLengthSquaredLower source
      ≤ calibration.stressLengthSquared
      ∧
    calibration.stressLengthSquared
      ≤ correctedFiniteThicknessRequiredStressLengthSquaredUpper source
  sourceNativeStressProfile :
    SourceNativeYMFiniteThicknessTarget profile

theorem compile_corrected_finite_thickness_source_calibration
    (source : AgdaLorentzianActiveSourceReceipt)
    (profile : SourceNativeAnisotropicYMProfile)
    (profileGeometry : SourceNativeYMFiniteThicknessTarget profile)
    (calibration :
      CorrectedPhysicalStressLengthSquaredCalibration
        source finiteThicknessKottlerTarget) :
    CorrectedFiniteThicknessSourceCalibrationWitness
      source profile profileGeometry calibration := by
  exact {
    sourceActiveNegative := source.activeConnectedNumerator_negative
    sourceMagnitudePositive := source.sourceMagnitude_positive
    scaleInsideRequiredInterval :=
      corrected_calibration_lies_in_required_interval
        source finiteThicknessKottlerTarget
        finite_thickness_kottler_target_positive
        calibration
    sourceNativeStressProfile := profileGeometry
  }

def traceOnlyKottlerCalibrationCountsAsSourceGeometryClosure : Bool := false
def correctedActiveStressCalibrationCompiled : Bool := true
def sourceNativeStressOverlapRequiredBeforeCalibrationPromotion : Bool := true
def acceptedMeasuredKappaAuthorityStillRequired : Bool := true
def microscopicStressLengthFactorizationStillOptional : Bool := true

end Integration.AntigravityCorrectedFiniteThicknessCalibration
