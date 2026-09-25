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
Physical source -> Einstein/Kottler calibration.

The earlier `SourceToKottlerCalibration` is retained as the minimal normalized
ABI.  The preferred physical ABI exposes the factors that its single scale had
compressed:

  sourceMagnitude                    dimensionless finite-source readout
  stressEnergyPerSourceUnit          physical stress-energy / source unit
  einsteinCoupling                   8*pi*G/c^4 in the chosen unit convention
  lengthScale                        physical length represented by one model unit

The dimensionless Kottler cosmological amplitude is therefore

  kappa * stressEnergyPerSourceUnit * sourceMagnitude * lengthScale^2.

No numerical value of G, lattice spacing, or stress normalization is invented.
-/

structure PhysicalEinsteinSourceCalibration
    (source : AgdaTraceSourceReceipt) where
  stressEnergyPerSourceUnit : Rat
  einsteinCoupling : Rat
  lengthScale : Rat
  stressScalePositive : 0 < stressEnergyPerSourceUnit
  einsteinCouplingPositive : 0 < einsteinCoupling
  lengthScalePositive : 0 < lengthScale
  exteriorAmplitudeCalibration :
    einsteinCoupling
      * stressEnergyPerSourceUnit
      * source.sourceMagnitude
      * lengthScale^2
      = nambuBubbleExteriorAmplitude

def PhysicalEinsteinSourceCalibration.dimensionlessExteriorAmplitude
    {source : AgdaTraceSourceReceipt}
    (calibration : PhysicalEinsteinSourceCalibration source) : Rat :=
  calibration.einsteinCoupling
    * calibration.stressEnergyPerSourceUnit
    * source.sourceMagnitude
    * calibration.lengthScale^2

theorem physical_calibration_exterior_amplitude
    (source : AgdaTraceSourceReceipt)
    (calibration : PhysicalEinsteinSourceCalibration source) :
    calibration.dimensionlessExteriorAmplitude
      = nambuBubbleExteriorAmplitude :=
  calibration.exteriorAmplitudeCalibration

theorem physical_calibration_exterior_amplitude_positive
    (source : AgdaTraceSourceReceipt)
    (calibration : PhysicalEinsteinSourceCalibration source) :
    0 < calibration.dimensionlessExteriorAmplitude := by
  rw [physical_calibration_exterior_amplitude source calibration]
  norm_num [nambuBubbleExteriorAmplitude]

theorem physical_calibration_factor_product_positive
    (source : AgdaTraceSourceReceipt)
    (calibration : PhysicalEinsteinSourceCalibration source) :
    0 <
      calibration.einsteinCoupling
        * calibration.stressEnergyPerSourceUnit
        * source.sourceMagnitude
        * calibration.lengthScale^2 := by
  exact physical_calibration_exterior_amplitude_positive source calibration

/-!
Authority boundary for the physical coupling.  The mathematical consumer needs
a positive typed coupling; accepted CODATA value/uncertainty provenance is a
separate receipt.  This mirrors the existing Agda
EinsteinPhysicalCouplingCalibrationExact boundary rather than silently treating
a decimal diagnostic as exact.
-/

structure PhysicalEinsteinCouplingAuthority
    (calibration : Rat) : Prop where
  positive : 0 < calibration
  acceptedMeasuredValue : Prop
  uncertaintyAccountedFor : Prop
  energyDensityConvention : Prop

def acceptedPhysicalEinsteinCouplingAlreadyDerived : Bool := false

/-!
The physically structured calibration can feed the end-to-end geometry
directly.  This avoids inventing an inverse "normalization scale".
-/

structure PhysicallyCalibratedAntigravityWitness
    {Stress : Type u}
    (E : CMP119RationalStressComponentEvaluator Stress)
    (stress : Stress)
    (normalized : NormalizedCrossSectorStressInstance E stress)
    (source : AgdaTraceSourceReceipt)
    (calibration : PhysicalEinsteinSourceCalibration source) : Prop where
  activeSourceNegative :
    source.activeConnectedNumerator < 0
  sourceMagnitudePositive :
    0 < source.sourceMagnitude
  physicalExteriorAmplitude :
    calibration.dimensionlessExteriorAmplitude
      = nambuBubbleExteriorAmplitude
  physicalExteriorAmplitudePositive :
    0 < calibration.dimensionlessExteriorAmplitude
  bubble :
    NambuGotoRepulsiveBubbleCandidate E stress normalized
  exteriorAccelerationPositive :
    0 < nambuBubbleAcceleration

theorem compile_physically_calibrated_antigravity
    {Stress : Type u}
    {E : CMP119RationalStressComponentEvaluator Stress}
    {stress : Stress}
    (normalized : NormalizedCrossSectorStressInstance E stress)
    (source : AgdaTraceSourceReceipt)
    (calibration : PhysicalEinsteinSourceCalibration source) :
    PhysicallyCalibratedAntigravityWitness
      E stress normalized source calibration := by
  exact {
    activeSourceNegative := source.activeConnectedNumerator_negative
    sourceMagnitudePositive := source.sourceMagnitude_positive
    physicalExteriorAmplitude :=
      physical_calibration_exterior_amplitude source calibration
    physicalExteriorAmplitudePositive :=
      physical_calibration_exterior_amplitude_positive source calibration
    bubble := nambu_goto_repulsive_bubble_candidate normalized
    exteriorAccelerationPositive :=
      canonical_nambu_bubble_acceleration_positive
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
def ag5PhysicalEinsteinFactorizationCompiled : Bool := true
def ag5MeasuredGCouplingAuthorityStillRequired : Bool := true
def ag5StressEnergyPerSourceUnitStillRequired : Bool := true
def ag5LengthScaleStillRequired : Bool := true
def ag6GlobalThinWallCandidateCompiled : Bool := true
def ag7CanonicalWilsonGibbsCompilerClosed : Bool := true
def ag7SymmetricMetricRechartClosed : Bool := true
def ag7CoordinateRoundTripStillRequired : Bool := false
def ag7SelectedCMP119SourceEqualityStillRequired : Bool := true
def ag7CMP119PhysicalSameObjectStillRequired : Bool := true
def ag8ConditionalAssemblyCompiled : Bool := true

end Integration.AntigravitySourceGeometryWeld
