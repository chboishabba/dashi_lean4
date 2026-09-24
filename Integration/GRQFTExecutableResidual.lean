/-!
# Executable GR/QFT Einstein and stress-weld BIDI residuals

This module mirrors the executable-candidate discipline introduced in
DASHI Agda.  Missing promotion authority does not suppress an available
calculation: run the candidate objects, compute a residual, and distinguish an
exact witness from a counterexample.

The finite Einstein fixture is normalized.  `Coupling.pos` represents the
dimensionless kappa = 1 normalization of 8*pi*G in this fixture only.  It is
not SI calibration and does not promote a continuum GR or GR/QFT theorem.
-/

namespace Integration.GRQFTExecutableResidual

inductive Axis4 where
  | time | x | y | z
  deriving DecidableEq, Repr

inductive SourceCoefficient where
  | neg | zero | pos
  deriving DecidableEq, Repr

inductive Coupling where
  | neg | zero | pos
  deriving DecidableEq, Repr

inductive AttemptOutcome where
  | exactResidualZero
  | nonzeroResidualCounterexample
  deriving DecidableEq, Repr

def negateSource : SourceCoefficient → SourceCoefficient
  | .neg => .pos
  | .zero => .zero
  | .pos => .neg

def addSource : SourceCoefficient → SourceCoefficient → SourceCoefficient
  | .neg, .neg => .neg
  | .neg, .zero => .neg
  | .neg, .pos => .zero
  | .zero, .neg => .neg
  | .zero, .zero => .zero
  | .zero, .pos => .pos
  | .pos, .neg => .zero
  | .pos, .zero => .pos
  | .pos, .pos => .pos

def scaleSource : Coupling → SourceCoefficient → SourceCoefficient
  | .neg, .neg => .pos
  | .neg, .zero => .zero
  | .neg, .pos => .neg
  | .zero, _ => .zero
  | .pos, s => s

abbrev Tensor4 := Axis4 → Axis4 → SourceCoefficient

def computedEinsteinTensor : Tensor4
  | .time, .time => .pos
  | .x, .x => .neg
  | .y, .y => .neg
  | .z, .z => .neg
  | _, _ => .zero

def computedMatterStress : Tensor4
  | .time, .time => .pos
  | .x, .x => .neg
  | .y, .y => .neg
  | .z, .z => .neg
  | _, _ => .zero

def einsteinEquationResidual (kappa : Coupling) : Tensor4 :=
  fun a b =>
    addSource
      (computedEinsteinTensor a b)
      (negateSource (scaleSource kappa (computedMatterStress a b)))

def sourceIsZero : SourceCoefficient → Bool
  | .zero => true
  | _ => false

def allComponentsZero (tensor : Tensor4) : Bool :=
  sourceIsZero (tensor .time .time) &&
  sourceIsZero (tensor .time .x) &&
  sourceIsZero (tensor .time .y) &&
  sourceIsZero (tensor .time .z) &&
  sourceIsZero (tensor .x .time) &&
  sourceIsZero (tensor .x .x) &&
  sourceIsZero (tensor .x .y) &&
  sourceIsZero (tensor .x .z) &&
  sourceIsZero (tensor .y .time) &&
  sourceIsZero (tensor .y .x) &&
  sourceIsZero (tensor .y .y) &&
  sourceIsZero (tensor .y .z) &&
  sourceIsZero (tensor .z .time) &&
  sourceIsZero (tensor .z .x) &&
  sourceIsZero (tensor .z .y) &&
  sourceIsZero (tensor .z .z)

def runEinsteinEquationAttempt (kappa : Coupling) : AttemptOutcome :=
  if allComponentsZero (einsteinEquationResidual kappa) then
    .exactResidualZero
  else
    .nonzeroResidualCounterexample

theorem normalized_residual_pointwise (a b : Axis4) :
    einsteinEquationResidual .pos a b = .zero := by
  cases a <;> cases b <;> rfl

theorem normalized_all_components_zero :
    allComponentsZero (einsteinEquationResidual .pos) = true := rfl

theorem normalized_attempt_passes :
    runEinsteinEquationAttempt .pos = .exactResidualZero := rfl

theorem zero_coupling_time_time_counterexample :
    einsteinEquationResidual .zero .time .time = .pos := rfl

theorem zero_coupling_attempt_fails :
    runEinsteinEquationAttempt .zero = .nonzeroResidualCounterexample := rfl

theorem negative_coupling_time_time_counterexample :
    einsteinEquationResidual .neg .time .time = .pos := rfl

theorem negative_coupling_attempt_fails :
    runEinsteinEquationAttempt .neg = .nonzeroResidualCounterexample := rfl

structure StressWeldObjects (Stress : Type u) where
  gr : Stress
  qft : Stress

structure ResidualProbe (Stress : Type u) (Residual : Type v) where
  zeroResidual : Residual
  residual : Stress → Stress → Residual
  residualIsZero : Residual → Bool
  reflexiveResidualZero : ∀ stress, residual stress stress = zeroResidual
  reflexiveResidualClassifiesZero :
    ∀ stress, residualIsZero (residual stress stress) = true

def runStressWeldAttempt
    {Stress : Type u} {Residual : Type v}
    (probe : ResidualProbe Stress Residual)
    (objects : StressWeldObjects Stress) : AttemptOutcome :=
  if probe.residualIsZero (probe.residual objects.gr objects.qft) then
    .exactResidualZero
  else
    .nonzeroResidualCounterexample

structure StressWeldAttemptReceipt
    (Stress : Type u) (Residual : Type v) where
  objects : StressWeldObjects Stress
  probe : ResidualProbe Stress Residual
  computedResidual : Residual
  outcome : AttemptOutcome
  residualIsLiteral :
    computedResidual = probe.residual objects.gr objects.qft
  outcomeIsComputed :
    outcome = runStressWeldAttempt probe objects

def executeStressWeldAttempt
    {Stress : Type u} {Residual : Type v}
    (probe : ResidualProbe Stress Residual)
    (objects : StressWeldObjects Stress) :
    StressWeldAttemptReceipt Stress Residual where
  objects := objects
  probe := probe
  computedResidual := probe.residual objects.gr objects.qft
  outcome := runStressWeldAttempt probe objects
  residualIsLiteral := rfl
  outcomeIsComputed := rfl

def bidiAttemptRunsWithoutPromotionReceipt : Bool := true

theorem bidi_attempt_runs_without_promotion :
    bidiAttemptRunsWithoutPromotionReceipt = true := rfl

def physicalCalibrationStillOpen : Bool := true

theorem physical_calibration_still_open :
    physicalCalibrationStillOpen = true := rfl

structure RecoveryObjects (Carrier : Type u) where
  recovered : Carrier
  target : Carrier

def runRecoveryAttempt
    {Carrier : Type u} {Residual : Type v}
    (probe : ResidualProbe Carrier Residual)
    (objects : RecoveryObjects Carrier) : AttemptOutcome :=
  if probe.residualIsZero (probe.residual objects.recovered objects.target) then
    .exactResidualZero
  else
    .nonzeroResidualCounterexample

structure RecoveryAttemptReceipt
    (Carrier : Type u) (Residual : Type v) where
  objects : RecoveryObjects Carrier
  probe : ResidualProbe Carrier Residual
  computedResidual : Residual
  outcome : AttemptOutcome
  residualIsLiteral :
    computedResidual = probe.residual objects.recovered objects.target
  outcomeIsComputed :
    outcome = runRecoveryAttempt probe objects

def executeRecoveryAttempt
    {Carrier : Type u} {Residual : Type v}
    (probe : ResidualProbe Carrier Residual)
    (objects : RecoveryObjects Carrier) :
    RecoveryAttemptReceipt Carrier Residual where
  objects := objects
  probe := probe
  computedResidual := probe.residual objects.recovered objects.target
  outcome := runRecoveryAttempt probe objects
  residualIsLiteral := rfl
  outcomeIsComputed := rfl

def recoveryAttemptsDoNotRequirePromotionTokens : Bool := true

theorem recovery_attempts_do_not_require_promotion_tokens :
    recoveryAttemptsDoNotRequirePromotionTokens = true := rfl


theorem normalized_coupling_unique
    (coupling : Coupling)
    (h : runEinsteinEquationAttempt coupling = .exactResidualZero) :
    coupling = .pos := by
  cases coupling <;> simp [runEinsteinEquationAttempt, allComponentsZero,
    einsteinEquationResidual, computedEinsteinTensor, computedMatterStress,
    addSource, negateSource, scaleSource] at h ⊢

structure FiniteSourcedEinsteinLawReceipt where
  selectedCoupling : Coupling
  selectedCouplingIsNormalized : selectedCoupling = .pos
  sourcedEquationResidualZero :
    ∀ a b, einsteinEquationResidual selectedCoupling a b = .zero
  normalizedCouplingIsUnique :
    ∀ other,
      runEinsteinEquationAttempt other = .exactResidualZero →
      other = selectedCoupling
  matterSourceNonzero : computedMatterStress .time .time = .pos
  physicalW4CalibrationIdentified : Bool
  physicalW4CalibrationIdentifiedIsFalse :
    physicalW4CalibrationIdentified = false
  continuumEinsteinLawPromoted : Bool
  continuumEinsteinLawPromotedIsFalse :
    continuumEinsteinLawPromoted = false
  grqftPromoted : Bool
  grqftPromotedIsFalse : grqftPromoted = false

def finiteSourcedEinsteinLawReceipt : FiniteSourcedEinsteinLawReceipt where
  selectedCoupling := .pos
  selectedCouplingIsNormalized := rfl
  sourcedEquationResidualZero := normalized_residual_pointwise
  normalizedCouplingIsUnique := by
    intro other h
    exact normalized_coupling_unique other h
  matterSourceNonzero := rfl
  physicalW4CalibrationIdentified := false
  physicalW4CalibrationIdentifiedIsFalse := rfl
  continuumEinsteinLawPromoted := false
  continuumEinsteinLawPromotedIsFalse := rfl
  grqftPromoted := false
  grqftPromotedIsFalse := rfl

inductive W4CalibrationAttemptOutcome where
  | currentCandidateRejectedByResidual
  | candidatePassesLocalResidual
  deriving DecidableEq, Repr

structure W4CalibrationBidiReceipt where
  attemptRan : Bool
  outcome : W4CalibrationAttemptOutcome
  fittedScale : String
  chi2PerDof : String
  firstBinPull : String
  lastBinPull : String
  adequacyDecision : Bool
  externalDYAuthorityPresent : Bool
  candidate256PhysicalCalibrationPromoted : Bool
  replacementRequired : Bool
  deriving Repr

def w4CalibrationBidiReceipt : W4CalibrationBidiReceipt where
  attemptRan := true
  outcome := .currentCandidateRejectedByResidual
  fittedScale := "230534508.31238452"
  chi2PerDof := "298.8462841768543"
  firstBinPull := "-67.35457265472463"
  lastBinPull := "-51.62836040061707"
  adequacyDecision := false
  externalDYAuthorityPresent := false
  candidate256PhysicalCalibrationPromoted := false
  replacementRequired := true

theorem current_w4_candidate_rejected :
    w4CalibrationBidiReceipt.outcome =
      .currentCandidateRejectedByResidual := rfl

inductive ExecutableGapStatus where
  | locallyClosed
  | locallyRejected
  | executableInterfaceReadyConcreteInstanceMissing
  | externalInformationRequired
  deriving DecidableEq, Repr

structure GRQFTExecutableClosureMatrix where
  finiteSourcedEinsteinEquation : ExecutableGapStatus
  finiteNormalizedCouplingUniqueness : ExecutableGapStatus
  currentW4DirtyCalibration : ExecutableGapStatus
  sameCandidateGRRecovery : ExecutableGapStatus
  sameCandidateQFTRecovery : ExecutableGapStatus
  sameCarrierStressWeld : ExecutableGapStatus
  physicalUnitCalibration : ExecutableGapStatus
  continuumRecovery : ExecutableGapStatus
  empiricalGRQFTValidation : ExecutableGapStatus
  terminalPromotion : Bool
  deriving Repr

def executableClosureMatrix : GRQFTExecutableClosureMatrix where
  finiteSourcedEinsteinEquation := .locallyClosed
  finiteNormalizedCouplingUniqueness := .locallyClosed
  currentW4DirtyCalibration := .locallyRejected
  sameCandidateGRRecovery := .executableInterfaceReadyConcreteInstanceMissing
  sameCandidateQFTRecovery := .executableInterfaceReadyConcreteInstanceMissing
  sameCarrierStressWeld := .executableInterfaceReadyConcreteInstanceMissing
  physicalUnitCalibration := .externalInformationRequired
  continuumRecovery := .executableInterfaceReadyConcreteInstanceMissing
  empiricalGRQFTValidation := .externalInformationRequired
  terminalPromotion := false

theorem finite_equation_locally_closed :
    executableClosureMatrix.finiteSourcedEinsteinEquation =
      .locallyClosed := rfl

theorem current_w4_calibration_locally_rejected :
    executableClosureMatrix.currentW4DirtyCalibration =
      .locallyRejected := rfl


def directSelectedQFTTargetEqualityPrimitive : Bool := false
def directSelectedGRTargetEqualityPrimitive : Bool := false

theorem direct_qft_target_equality_not_primitive :
    directSelectedQFTTargetEqualityPrimitive = false := rfl

theorem direct_gr_target_equality_not_primitive :
    directSelectedGRTargetEqualityPrimitive = false := rfl

inductive GRQFTConcreteInstanceLeaf where
  | attachLiteralRound131YMToRecoveredQFT
  | attachLiteralNonflatGRToRecoveredGR
  | instantiateCommonEinsteinMetricVariation
  | instantiateCommonBalabanAllSectorProducer
  | instantiateSharedMetricProducerLanguage
  | evaluateSameCarrierStressResidual
  | replaceRejectedW4CalibrationCandidate
  deriving DecidableEq, Repr

def concreteInstanceLeaves : List GRQFTConcreteInstanceLeaf :=
  [ .attachLiteralRound131YMToRecoveredQFT
  , .attachLiteralNonflatGRToRecoveredGR
  , .instantiateCommonEinsteinMetricVariation
  , .instantiateCommonBalabanAllSectorProducer
  , .instantiateSharedMetricProducerLanguage
  , .evaluateSameCarrierStressResidual
  , .replaceRejectedW4CalibrationCandidate
  ]

structure GRQFTConcreteInstanceFrontier where
  directQFTTargetEqualityStillPrimitive : Bool
  directGRTargetEqualityStillPrimitive : Bool
  finiteEinsteinEquationStillOpen : Bool
  finiteNormalizedCouplingUniquenessStillOpen : Bool
  currentW4CandidateStillUnknown : Bool
  remainingLeaves : List GRQFTConcreteInstanceLeaf
  deriving Repr

def concreteInstanceFrontier : GRQFTConcreteInstanceFrontier where
  directQFTTargetEqualityStillPrimitive := false
  directGRTargetEqualityStillPrimitive := false
  finiteEinsteinEquationStillOpen := false
  finiteNormalizedCouplingUniquenessStillOpen := false
  currentW4CandidateStillUnknown := false
  remainingLeaves := concreteInstanceLeaves

theorem finite_einstein_no_longer_open :
    concreteInstanceFrontier.finiteEinsteinEquationStillOpen = false := rfl

theorem w4_candidate_no_longer_unknown :
    concreteInstanceFrontier.currentW4CandidateStillUnknown = false := rfl

end Integration.GRQFTExecutableResidual
