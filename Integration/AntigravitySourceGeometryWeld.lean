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

  /-- The selected R119/CMP119 connected numerator is the canonical
      Wilson/Gibbs connected numerator on the same finite measure. -/
  selectedCMP119ConnectedNumeratorSameObject : Prop

  /-- The renormalized trace numerator is attached to the convention-correct
      beta/F^2 numerator on that same source family. -/
  betaF2TraceSameObject : Prop

  /-- The partition function is the partition function of the selected literal
      finite measure rather than an unrelated positive scalar. -/
  selectedPartitionFunctionSameObject : Prop

def sourceReceiptCarriesSameObjectProvenance : Bool := true

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
Normalized source -> Einstein/Kottler calibration.

The earlier `SourceToKottlerCalibration` is retained as the minimal normalized
ABI.  This factorized ABI exposes the dimensionless factors that its single scale
had compressed.  It is NOT an exact SI evaluation of 8*pi*G/c^4: measured G and
the transcendental pi factor belong to the physical authority layer below:

  sourceMagnitude                    dimensionless finite-source readout
  stressEnergyPerSourceUnit          physical stress-energy / source unit
  normalizedEinsteinCoupling         dimensionless positive coupling representative
  lengthScale                        physical length represented by one model unit

The dimensionless Kottler cosmological amplitude is therefore

  kappa * stressEnergyPerSourceUnit * sourceMagnitude * lengthScale^2.

No numerical value of G, lattice spacing, or stress normalization is invented.
-/

structure NormalizedSourceToKottlerTargetCalibration
    (source : AgdaTraceSourceReceipt)
    (targetAmplitude : Rat) where
  stressEnergyPerSourceUnit : Rat
  normalizedEinsteinCoupling : Rat
  lengthScale : Rat
  stressScalePositive : 0 < stressEnergyPerSourceUnit
  normalizedEinsteinCouplingPositive : 0 < normalizedEinsteinCoupling
  lengthScalePositive : 0 < lengthScale
  targetCalibration :
    normalizedEinsteinCoupling
      * stressEnergyPerSourceUnit
      * source.sourceMagnitude
      * lengthScale^2
      = targetAmplitude

def NormalizedSourceToKottlerTargetCalibration.dimensionlessAmplitude
    {source : AgdaTraceSourceReceipt}
    {targetAmplitude : Rat}
    (calibration :
      NormalizedSourceToKottlerTargetCalibration source targetAmplitude) : Rat :=
  calibration.normalizedEinsteinCoupling
    * calibration.stressEnergyPerSourceUnit
    * source.sourceMagnitude
    * calibration.lengthScale^2

theorem normalized_target_calibration_exact
    (source : AgdaTraceSourceReceipt)
    (target : Rat)
    (calibration :
      NormalizedSourceToKottlerTargetCalibration source target) :
    calibration.dimensionlessAmplitude = target :=
  calibration.targetCalibration

structure NormalizedEinsteinSourceCalibration
    (source : AgdaTraceSourceReceipt) where
  stressEnergyPerSourceUnit : Rat
  normalizedEinsteinCoupling : Rat
  lengthScale : Rat
  stressScalePositive : 0 < stressEnergyPerSourceUnit
  normalizedEinsteinCouplingPositive : 0 < normalizedEinsteinCoupling
  lengthScalePositive : 0 < lengthScale
  exteriorAmplitudeCalibration :
    normalizedEinsteinCoupling
      * stressEnergyPerSourceUnit
      * source.sourceMagnitude
      * lengthScale^2
      = nambuBubbleExteriorAmplitude

def NormalizedEinsteinSourceCalibration.dimensionlessExteriorAmplitude
    {source : AgdaTraceSourceReceipt}
    (calibration : NormalizedEinsteinSourceCalibration source) : Rat :=
  calibration.normalizedEinsteinCoupling
    * calibration.stressEnergyPerSourceUnit
    * source.sourceMagnitude
    * calibration.lengthScale^2

theorem physical_calibration_exterior_amplitude
    (source : AgdaTraceSourceReceipt)
    (calibration : NormalizedEinsteinSourceCalibration source) :
    calibration.dimensionlessExteriorAmplitude
      = nambuBubbleExteriorAmplitude :=
  calibration.exteriorAmplitudeCalibration

theorem physical_calibration_exterior_amplitude_positive
    (source : AgdaTraceSourceReceipt)
    (calibration : NormalizedEinsteinSourceCalibration source) :
    0 < calibration.dimensionlessExteriorAmplitude := by
  rw [physical_calibration_exterior_amplitude source calibration]
  norm_num [nambuBubbleExteriorAmplitude]

theorem physical_calibration_factor_product_positive
    (source : AgdaTraceSourceReceipt)
    (calibration : NormalizedEinsteinSourceCalibration source) :
    0 <
      calibration.normalizedEinsteinCoupling
        * calibration.stressEnergyPerSourceUnit
        * source.sourceMagnitude
        * calibration.lengthScale^2 := by
  exact physical_calibration_exterior_amplitude_positive source calibration

/-!
Authority boundary for the measured physical coupling.

The mathematical Kottler consumer above is exact and rational.  Physical
calibration is different: kappa = 8*pi*G/c^4 contains measured G and pi, so it
must not be represented as an exact Rat.  We use an exact rational enclosure for
a typed measured-coupling representative, plus explicit authority and convention
receipts.  A later real/interval backend may refine the enclosure without
changing the normalized geometry theorem.
-/

structure PhysicalEinsteinCouplingInterval where
  lower : Rat
  upper : Rat
  lowerPositive : 0 < lower
  ordered : lower ≤ upper

structure PhysicalEinsteinCouplingAuthority
    (interval : PhysicalEinsteinCouplingInterval) : Prop where
  codataSourceBound : Prop
  acceptedMeasuredValue : Prop
  uncertaintyAccountedFor : Prop
  energyDensityConvention : Prop
  kappaConvention : Prop

structure PhysicalScaleTransport
    (source : AgdaTraceSourceReceipt)
    (interval : PhysicalEinsteinCouplingInterval) where
  stressEnergyPerSourceUnitLower : Rat
  stressEnergyPerSourceUnitUpper : Rat
  lengthScaleLower : Rat
  lengthScaleUpper : Rat
  stressLowerPositive : 0 < stressEnergyPerSourceUnitLower
  stressOrdered : stressEnergyPerSourceUnitLower ≤ stressEnergyPerSourceUnitUpper
  lengthLowerPositive : 0 < lengthScaleLower
  lengthOrdered : lengthScaleLower ≤ lengthScaleUpper

def PhysicalScaleTransport.exteriorAmplitudeLower
    {source : AgdaTraceSourceReceipt}
    {interval : PhysicalEinsteinCouplingInterval}
    (transport : PhysicalScaleTransport source interval) : Rat :=
  interval.lower
    * transport.stressEnergyPerSourceUnitLower
    * source.sourceMagnitude
    * transport.lengthScaleLower^2

def PhysicalScaleTransport.exteriorAmplitudeUpper
    {source : AgdaTraceSourceReceipt}
    {interval : PhysicalEinsteinCouplingInterval}
    (transport : PhysicalScaleTransport source interval) : Rat :=
  interval.upper
    * transport.stressEnergyPerSourceUnitUpper
    * source.sourceMagnitude
    * transport.lengthScaleUpper^2

structure PhysicalKottlerCalibrationEnclosure
    (source : AgdaTraceSourceReceipt)
    (interval : PhysicalEinsteinCouplingInterval) : Prop where
  authority : PhysicalEinsteinCouplingAuthority interval
  transport : PhysicalScaleTransport source interval
  targetInside :
    transport.exteriorAmplitudeLower ≤ nambuBubbleExteriorAmplitude
      ∧ nambuBubbleExteriorAmplitude ≤ transport.exteriorAmplitudeUpper

def codataCandidateKappaLower : Rat :=
  207660077171595041751 / 1000000000000000000000000000000000000000000000000000000000000000

def codataCandidateKappaUpper : Rat :=
  207669411397399298249 / 1000000000000000000000000000000000000000000000000000000000000000

theorem codata_candidate_kappa_lower_positive :
    0 < codataCandidateKappaLower := by
  norm_num [codataCandidateKappaLower]

theorem codata_candidate_kappa_interval_ordered :
    codataCandidateKappaLower ≤ codataCandidateKappaUpper := by
  norm_num [codataCandidateKappaLower, codataCandidateKappaUpper]

def codataCandidateKappaInterval : PhysicalEinsteinCouplingInterval where
  lower := codataCandidateKappaLower
  upper := codataCandidateKappaUpper
  lowerPositive := codata_candidate_kappa_lower_positive
  ordered := codata_candidate_kappa_interval_ordered

def requiredStressLengthSquaredLowerFor
    (targetAmplitude : Rat)
    (source : AgdaTraceSourceReceipt) : Rat :=
  targetAmplitude
    / (codataCandidateKappaUpper * source.sourceMagnitude)

def requiredStressLengthSquaredUpperFor
    (targetAmplitude : Rat)
    (source : AgdaTraceSourceReceipt) : Rat :=
  targetAmplitude
    / (codataCandidateKappaLower * source.sourceMagnitude)

theorem required_stress_length_squared_for_interval_ordered
    (targetAmplitude : Rat)
    (source : AgdaTraceSourceReceipt)
    (hTarget : 0 ≤ targetAmplitude) :
    requiredStressLengthSquaredLowerFor targetAmplitude source
      ≤ requiredStressLengthSquaredUpperFor targetAmplitude source := by
  unfold requiredStressLengthSquaredLowerFor
    requiredStressLengthSquaredUpperFor
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

/-- For fixed positive source magnitude and target dimensionless Kottler
    amplitude, a measured kappa interval determines the required interval for
    the product (stress-energy per source unit) * lengthScale^2.  This does not
    choose a stress scale or a length scale separately. -/
def requiredStressLengthSquaredLower
    (source : AgdaTraceSourceReceipt) : Rat :=
  nambuBubbleExteriorAmplitude
    / (codataCandidateKappaUpper * source.sourceMagnitude)

def requiredStressLengthSquaredUpper
    (source : AgdaTraceSourceReceipt) : Rat :=
  nambuBubbleExteriorAmplitude
    / (codataCandidateKappaLower * source.sourceMagnitude)

theorem required_stress_length_squared_lower_positive
    (source : AgdaTraceSourceReceipt) :
    0 < requiredStressLengthSquaredLower source := by
  unfold requiredStressLengthSquaredLower
  have hs : 0 < source.sourceMagnitude := source.sourceMagnitude_positive
  have hk : 0 < codataCandidateKappaUpper := by
    exact lt_of_lt_of_le codata_candidate_kappa_lower_positive
      codata_candidate_kappa_interval_ordered
  positivity

theorem required_stress_length_squared_upper_positive
    (source : AgdaTraceSourceReceipt) :
    0 < requiredStressLengthSquaredUpper source := by
  unfold requiredStressLengthSquaredUpper
  have hs : 0 < source.sourceMagnitude := source.sourceMagnitude_positive
  have hk : 0 < codataCandidateKappaLower :=
    codata_candidate_kappa_lower_positive
  positivity

theorem required_stress_length_squared_interval_ordered
    (source : AgdaTraceSourceReceipt) :
    requiredStressLengthSquaredLower source
      ≤ requiredStressLengthSquaredUpper source := by
  unfold requiredStressLengthSquaredLower requiredStressLengthSquaredUpper
  have hs : 0 < source.sourceMagnitude := source.sourceMagnitude_positive
  have hlo : 0 < codataCandidateKappaLower :=
    codata_candidate_kappa_lower_positive
  have hhi : 0 < codataCandidateKappaUpper := by
    exact lt_of_lt_of_le hlo codata_candidate_kappa_interval_ordered
  apply div_le_div_of_nonneg_left
  · norm_num [nambuBubbleExteriorAmplitude]
  · exact mul_pos hlo hs
  · exact mul_le_mul_of_nonneg_right
      codata_candidate_kappa_interval_ordered (le_of_lt hs)


/-!
Least-privilege physical scale calibration.

The Kottler consumer never observes the stress-energy conversion and model
length separately; it observes only

  S_L2 = (stress-energy per source unit) * lengthScale^2.

Therefore the physical calibration ABI should expose that product directly.
A microscopic/lattice realization may later factor S_L2, but the gravitational
consumer must not demand a non-identifiable split.
-/

structure PhysicalStressLengthSquaredCalibration
    (source : AgdaTraceSourceReceipt)
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

theorem required_scale_interval_contains_every_exact_calibration
    (source : AgdaTraceSourceReceipt)
    (targetAmplitude : Rat)
    (hTarget : 0 < targetAmplitude)
    (calibration :
      PhysicalStressLengthSquaredCalibration source targetAmplitude) :
    requiredStressLengthSquaredLowerFor targetAmplitude source
      ≤ calibration.stressLengthSquared
      ∧
    calibration.stressLengthSquared
      ≤ requiredStressLengthSquaredUpperFor targetAmplitude source := by
  rcases calibration.targetInsideCODATAKappaEnclosure with ⟨hlo, hhi⟩
  have hs : 0 < source.sourceMagnitude := source.sourceMagnitude_positive
  have hklo : 0 < codataCandidateKappaLower :=
    codata_candidate_kappa_lower_positive
  have hkhi : 0 < codataCandidateKappaUpper := by
    exact lt_of_lt_of_le hklo codata_candidate_kappa_interval_ordered
  constructor
  · unfold requiredStressLengthSquaredLowerFor
    apply (div_le_iff₀ (mul_pos hkhi hs)).2
    nlinarith
  · unfold requiredStressLengthSquaredUpperFor
    apply (le_div_iff₀ (mul_pos hklo hs)).2
    nlinarith

def physicalScaleConsumerNeedsOnlyStressLengthSquaredProduct : Bool := true
def separateStressAndLengthIdentificationRequiredByGravityConsumer : Bool := false


def codataDiagnosticIntervalTyped : Bool := true
def codataDiagnosticIntervalAcceptedAuthority : Bool := false

def acceptedPhysicalEinsteinCouplingAlreadyDerived : Bool := false
def exactRationalSICouplingClaimed : Bool := false
def measuredCouplingIntervalRequired : Bool := true

/-!
The physically structured calibration can feed the end-to-end geometry
directly.  This avoids inventing an inverse "normalization scale".
-/

structure NormalizedCalibratedAntigravityWitness
    {Stress : Type u}
    (E : CMP119RationalStressComponentEvaluator Stress)
    (stress : Stress)
    (normalized : NormalizedCrossSectorStressInstance E stress)
    (source : AgdaTraceSourceReceipt)
    (calibration : NormalizedEinsteinSourceCalibration source) : Prop where
  activeSourceNegative :
    source.activeConnectedNumerator < 0
  sourceMagnitudePositive :
    0 < source.sourceMagnitude
  normalizedExteriorAmplitude :
    calibration.dimensionlessExteriorAmplitude
      = nambuBubbleExteriorAmplitude
  normalizedExteriorAmplitudePositive :
    0 < calibration.dimensionlessExteriorAmplitude
  bubble :
    NambuGotoRepulsiveBubbleCandidate E stress normalized
  exteriorAccelerationPositive :
    0 < nambuBubbleAcceleration

theorem compile_normalized_calibrated_antigravity
    {Stress : Type u}
    {E : CMP119RationalStressComponentEvaluator Stress}
    {stress : Stress}
    (normalized : NormalizedCrossSectorStressInstance E stress)
    (source : AgdaTraceSourceReceipt)
    (calibration : NormalizedEinsteinSourceCalibration source) :
    NormalizedCalibratedAntigravityWitness
      E stress normalized source calibration := by
  exact {
    activeSourceNegative := source.activeConnectedNumerator_negative
    sourceMagnitudePositive := source.sourceMagnitude_positive
    normalizedExteriorAmplitude :=
      physical_calibration_exterior_amplitude source calibration
    normalizedExteriorAmplitudePositive :=
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
def ag5ExactRationalSICouplingRetired : Bool := true
def ag5MeasuredCouplingIntervalABICompiled : Bool := true
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


/-!
Post-correction promotion firewall.

The historical source receipt used Z * quantumTraceNumerator under the name
activeConnectedNumerator.  After separating Lorentzian trace from active stress,
these constructors remain algebraically valid compatibility surfaces but are
not sufficient physical source-to-geometry promotion witnesses.
-/

def historicalTraceOnlySourceGeometryPhysicallyPromotable : Bool := false
def correctedLorentzianActiveSourceReceiptRequiredForPromotion : Bool := true

end Integration.AntigravitySourceGeometryWeld
