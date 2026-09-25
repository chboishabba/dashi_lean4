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


/-!
Calibration-sign firewall.

Positive Einstein coupling, positive source-unit conversion, and positive
length-squared scaling preserve the sign of the active source.  Calibration
therefore cannot repair a positive-active-stress source by normalization.
-/

theorem positive_calibration_cannot_flip_active_source_sign
    {activeSource coupling stressLengthSquared : Rat}
    (hActive : 0 ≤ activeSource)
    (hCoupling : 0 < coupling)
    (hScale : 0 < stressLengthSquared) :
    0 ≤ coupling * activeSource * stressLengthSquared := by
  have hc : 0 ≤ coupling := le_of_lt hCoupling
  have hs : 0 ≤ stressLengthSquared := le_of_lt hScale
  positivity

theorem positive_calibration_preserves_strict_negative_active_source
    {activeSource coupling stressLengthSquared : Rat}
    (hActive : activeSource < 0)
    (hCoupling : 0 < coupling)
    (hScale : 0 < stressLengthSquared) :
    coupling * activeSource * stressLengthSquared < 0 := by
  have hca : coupling * activeSource < 0 :=
    mul_neg_of_pos_of_neg hCoupling hActive
  exact mul_neg_of_neg_of_pos hca hScale

def calibrationCanRepairActiveStressSignMismatch : Bool := false
def calibrationSignPreservationCompiled : Bool := true

end Integration.AntigravityCorrectedFiniteThicknessCalibration
