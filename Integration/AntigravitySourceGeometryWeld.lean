import Integration.GRQFTPostMergeLocalization

namespace Integration.AntigravitySourceGeometryWeld

open Integration.GRQFTPostMergeLocalization

/-!
Cross-prover antigravity ABI.

The Agda side reduces the source theorem to a positive literal partition function
and a strictly negative renormalized trace numerator.  This Lean module does not
claim that those physical facts have been proved.  It gives their exact consumer
surface and proves the downstream sign/calibration/global-geometry consequences.

This keeps the remaining source physics separate from the already-constructed
TOV/Israel/Kottler geometry.
-/

structure AgdaTraceSourceReceipt where
  partitionFunction : Rat
  quantumTraceNumerator : Rat
  partitionPositive : 0 < partitionFunction
  quantumTraceNegative : quantumTraceNumerator < 0

def AgdaTraceSourceReceipt.activeConnectedNumerator
    (s : AgdaTraceSourceReceipt) : Rat :=
  s.partitionFunction * s.quantumTraceNumerator

theorem AgdaTraceSourceReceipt.activeConnectedNumerator_negative
    (s : AgdaTraceSourceReceipt) :
    s.activeConnectedNumerator < 0 := by
  exact mul_neg_of_pos_of_neg s.partitionPositive s.quantumTraceNegative

def AgdaTraceSourceReceipt.sourceMagnitude
    (s : AgdaTraceSourceReceipt) : Rat :=
  -s.activeConnectedNumerator

theorem AgdaTraceSourceReceipt.sourceMagnitude_positive
    (s : AgdaTraceSourceReceipt) :
    0 < s.sourceMagnitude := by
  unfold sourceMagnitude
  linarith [s.activeConnectedNumerator_negative]

/-!
The source magnitude and the geometric vacuum amplitude have dimensions and
normalizations that are not definitionally identical.  The calibration scale is
therefore explicit.  This is the AG-5 seam: it is an input to be sourced, not a
unit conversion silently invented by the formalization.
-/

structure SourceToKottlerCalibration
    (source : AgdaTraceSourceReceipt) where
  normalizationScale : Rat
  normalizationScalePositive : 0 < normalizationScale
  calibratedExteriorAmplitude :
    source.sourceMagnitude / normalizationScale
      = nambuBubbleExteriorAmplitude

theorem calibrated_exterior_amplitude_positive
    (source : AgdaTraceSourceReceipt)
    (calibration : SourceToKottlerCalibration source) :
    0 < source.sourceMagnitude / calibration.normalizationScale := by
  rw [calibration.calibratedExteriorAmplitude]
  norm_num [nambuBubbleExteriorAmplitude]

theorem canonical_nambu_bubble_acceleration_positive :
    0 < nambuBubbleAcceleration := by
  norm_num [nambuBubbleAcceleration]

/-!
AG-6/AG-8 conditional end-to-end witness.

The geometry is not inferred merely from a negative source.  We require:
  * the source trace receipt;
  * an explicit source-to-vacuum-amplitude calibration;
  * the normalized CMP119 tensor transport already used by the bubble model.

Given those inputs, Lean packages a globally consistent thin-wall candidate
with the existing TOV/junction/Kottler construction and proves the exterior
acceleration is positive.  Source-native derivation of the potential/wall and
finite-thickness/SI calibration remain deliberately outside this theorem.
-/

structure EndToEndConditionalAntigravityWitness
    {Stress : Type u}
    (E : CMP119RationalStressComponentEvaluator Stress)
    (stress : Stress)
    (normalized : NormalizedCrossSectorStressInstance E stress)
    (source : AgdaTraceSourceReceipt)
    (calibration : SourceToKottlerCalibration source) : Prop where
  activeSourceNegative :
    source.activeConnectedNumerator < 0
  sourceMagnitudePositive :
    0 < source.sourceMagnitude
  calibratedExteriorAmplitudePositive :
    0 < source.sourceMagnitude / calibration.normalizationScale
  bubble :
    NambuGotoRepulsiveBubbleCandidate E stress normalized
  exteriorAccelerationPositive :
    0 < nambuBubbleAcceleration
  negativeNewtonGNotRequired :
    nambuBubbleNegativeNewtonGRequired = false
  negativeMetricMassNotRequired :
    nambuBubbleNegativeMetricMassRequired = false

theorem compile_end_to_end_conditional_antigravity
    {Stress : Type u}
    {E : CMP119RationalStressComponentEvaluator Stress}
    {stress : Stress}
    (normalized : NormalizedCrossSectorStressInstance E stress)
    (source : AgdaTraceSourceReceipt)
    (calibration : SourceToKottlerCalibration source) :
    EndToEndConditionalAntigravityWitness
      E stress normalized source calibration := by
  exact {
    activeSourceNegative := source.activeConnectedNumerator_negative
    sourceMagnitudePositive := source.sourceMagnitude_positive
    calibratedExteriorAmplitudePositive :=
      calibrated_exterior_amplitude_positive source calibration
    bubble := nambu_goto_repulsive_bubble_candidate normalized
    exteriorAccelerationPositive :=
      canonical_nambu_bubble_acceleration_positive
    negativeNewtonGNotRequired := rfl
    negativeMetricMassNotRequired := rfl
  }

/-!
Milestone surface.  These booleans are scheduler metadata, not physical proof.
They prevent the implementation queue from reopening work already compiled.
-/

def ag1LiteralTraceCalculusCompiled : Bool := true
def ag2QuantumTraceSignIsPhysicalLeaf : Bool := true
def ag3FourDiagonalCollapseCompiled : Bool := true
def ag4LocalRepulsionCompilerCompiled : Bool := true
def ag5SourceGeometryCalibrationExplicit : Bool := true
def ag6GlobalThinWallCandidateCompiled : Bool := true
def ag7CMP119PhysicalSameObjectStillRequired : Bool := true
def ag8ConditionalAssemblyCompiled : Bool := true

end Integration.AntigravitySourceGeometryWeld
