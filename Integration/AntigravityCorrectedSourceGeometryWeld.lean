import Integration.AntigravitySourceGeometryWeld

namespace Integration.AntigravityCorrectedSourceGeometryWeld

open Integration.GRQFTPostMergeLocalization
open Integration.AntigravitySourceGeometryWeld

/-!
Corrected cross-prover antigravity ABI.

The historical AgdaTraceSourceReceipt packages Z * trace as an "active"
numerator.  That name is retained only for compatibility.  The physical
Lorentzian active/focusing contraction requires the same-object timelike
component:

  active density numerator = Theta + 2 T00
  connected active numerator = Z * (Theta + 2 T00).
-/

structure AgdaLorentzianActiveSourceReceipt where
  partitionFunction : Rat
  lorentzianTraceNumerator : Rat
  timelikeEnergyNumerator : Rat

  partitionPositive : 0 < partitionFunction

  activeDensityNumeratorNegative :
    lorentzianTraceNumerator + 2 * timelikeEnergyNumerator < 0

  selectedTraceSameObject : Prop
  selectedT00SameObject : Prop
  selectedPartitionFunctionSameObject : Prop
  euclideanToLorentzianContinuationSameObject : Prop

def AgdaLorentzianActiveSourceReceipt.activeDensityNumerator
    (s : AgdaLorentzianActiveSourceReceipt) : Rat :=
  s.lorentzianTraceNumerator + 2 * s.timelikeEnergyNumerator

def AgdaLorentzianActiveSourceReceipt.activeConnectedNumerator
    (s : AgdaLorentzianActiveSourceReceipt) : Rat :=
  s.partitionFunction * s.activeDensityNumerator

theorem AgdaLorentzianActiveSourceReceipt.activeConnectedNumerator_negative
    (s : AgdaLorentzianActiveSourceReceipt) :
    s.activeConnectedNumerator < 0 := by
  exact mul_neg_of_pos_of_neg
    s.partitionPositive
    s.activeDensityNumeratorNegative

def AgdaLorentzianActiveSourceReceipt.sourceMagnitude
    (s : AgdaLorentzianActiveSourceReceipt) : Rat :=
  -s.activeConnectedNumerator

theorem AgdaLorentzianActiveSourceReceipt.sourceMagnitude_positive
    (s : AgdaLorentzianActiveSourceReceipt) :
    0 < s.sourceMagnitude := by
  unfold AgdaLorentzianActiveSourceReceipt.sourceMagnitude
  linarith [s.activeConnectedNumerator_negative]

theorem trace_threshold_is_exact
    (s : AgdaLorentzianActiveSourceReceipt) :
    s.activeDensityNumerator < 0 := by
  exact s.activeDensityNumeratorNegative

def historicalTraceReceiptAloneIsPhysicalActiveSource : Bool := false
def correctedLorentzianReceiptRequiredForGeometry : Bool := true

/-!
Least-privilege corrected physical calibration.

The gravitational consumer observes only

  kappa * (stress-energy/source-unit * length^2) * sourceMagnitude.

It does not need a separate stress scale and length scale.
-/

structure CorrectedPhysicalStressLengthSquaredCalibration
    (source : AgdaLorentzianActiveSourceReceipt)
    (targetAmplitude : Rat) where
  stressLengthSquared : Rat
  stressLengthSquaredPositive : 0 < stressLengthSquared

  targetInsideCODATAKappaEnclosure :
    codataCandidateKappaLower
        * source.sourceMagnitude * stressLengthSquared
      ≤ targetAmplitude
      ∧
    targetAmplitude
      ≤ codataCandidateKappaUpper
        * source.sourceMagnitude * stressLengthSquared

def correctedRequiredStressLengthSquaredLowerFor
    (targetAmplitude : Rat)
    (source : AgdaLorentzianActiveSourceReceipt) : Rat :=
  targetAmplitude
    / (codataCandidateKappaUpper * source.sourceMagnitude)

def correctedRequiredStressLengthSquaredUpperFor
    (targetAmplitude : Rat)
    (source : AgdaLorentzianActiveSourceReceipt) : Rat :=
  targetAmplitude
    / (codataCandidateKappaLower * source.sourceMagnitude)

theorem corrected_required_scale_interval_ordered
    (targetAmplitude : Rat)
    (source : AgdaLorentzianActiveSourceReceipt)
    (hTarget : 0 ≤ targetAmplitude) :
    correctedRequiredStressLengthSquaredLowerFor targetAmplitude source
      ≤ correctedRequiredStressLengthSquaredUpperFor targetAmplitude source := by
  unfold correctedRequiredStressLengthSquaredLowerFor
    correctedRequiredStressLengthSquaredUpperFor
  have hs : 0 < source.sourceMagnitude := source.sourceMagnitude_positive
  have hlo : 0 < codataCandidateKappaLower :=
    codata_candidate_kappa_lower_positive
  have hhi : 0 < codataCandidateKappaUpper := by
    exact lt_of_lt_of_le hlo codata_candidate_kappa_interval_ordered
  apply div_le_div_of_nonneg_left
  · exact hTarget
  · exact mul_pos hlo hs
  · exact mul_le_mul_of_nonneg_right
      codata_candidate_kappa_interval_ordered (le_of_lt hs)

theorem corrected_calibration_lies_in_required_interval
    (source : AgdaLorentzianActiveSourceReceipt)
    (targetAmplitude : Rat)
    (hTarget : 0 < targetAmplitude)
    (calibration :
      CorrectedPhysicalStressLengthSquaredCalibration source targetAmplitude) :
    correctedRequiredStressLengthSquaredLowerFor targetAmplitude source
      ≤ calibration.stressLengthSquared
      ∧
    calibration.stressLengthSquared
      ≤ correctedRequiredStressLengthSquaredUpperFor targetAmplitude source := by
  rcases calibration.targetInsideCODATAKappaEnclosure with ⟨hlo, hhi⟩
  have hs : 0 < source.sourceMagnitude := source.sourceMagnitude_positive
  have hklo : 0 < codataCandidateKappaLower :=
    codata_candidate_kappa_lower_positive
  have hkhi : 0 < codataCandidateKappaUpper := by
    exact lt_of_lt_of_le hklo codata_candidate_kappa_interval_ordered
  constructor
  · unfold correctedRequiredStressLengthSquaredLowerFor
    apply (div_le_iff₀ (mul_pos hkhi hs)).2
    nlinarith
  · unfold correctedRequiredStressLengthSquaredUpperFor
    apply (le_div_iff₀ (mul_pos hklo hs)).2
    nlinarith

def correctedCalibrationUsesActiveStressNotTraceAlone : Bool := true
def separateStressAndLengthStillNotIdentifiable : Bool := true

end Integration.AntigravityCorrectedSourceGeometryWeld
