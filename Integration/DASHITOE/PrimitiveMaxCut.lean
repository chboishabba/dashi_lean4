namespace DASHITOE

/-!
Primitive-leaf recut of the current TOE frontier.

Sibling-branch receipts preserve source ownership. They are not local Lean proof
terms, and compiler availability is not same-object physical payment.
-/

inductive ReceiptAuthority where
  | dashiLocalTheorem
  | dashiSiblingFormalSource
  | externalFormalSource
  | externalScientificSource
  deriving Repr, DecidableEq

structure PrimitiveSourceReceipt where
  repository : String
  pullRequest : Nat
  headCommit : String
  moduleName : String
  ownerClaim : String
  authority : ReceiptAuthority
  localLeanTheorem : Bool
  deriving Repr

def siblingReceipt (repo : String) (pr : Nat) (head moduleName claim : String) :
    PrimitiveSourceReceipt :=
  { repository := repo
    pullRequest := pr
    headCommit := head
    moduleName := moduleName
    ownerClaim := claim
    authority := .dashiSiblingFormalSource
    localLeanTheorem := false }

def siblingFormalSourceIsLocalLeanTheorem : Bool := false

structure MonsterPrimitiveFrontier where
  linearHardeningSource : PrimitiveSourceReceipt
  hZetaCompilerSource : PrimitiveSourceReceipt
  isotypicCompilerSource : PrimitiveSourceReceipt
  genericClassifierStillTerminal : Bool
  genericIsotypicAssemblyStillTerminal : Bool
  actualWeightTwoLinearBridgePaid : Bool
  actualLinearRestrictionPaid : Bool
  actualWholeCharacterSimpleNonzeroInputsPaid : Bool
  actualHZetaSameObjectRecognitionPaid : Bool
  actualIsotypicRecognitionPaid : Bool
  actualMultiplicityNinetyPaid : Bool
  actualMultiplicityHomNormalizerActionPaid : Bool
  actualTwelveSeventyEightActionIntertwinerPaid : Bool
  deriving Repr

def monsterPrimitiveFrontier : MonsterPrimitiveFrontier :=
  { linearHardeningSource := siblingReceipt "chboishabba/dashi_agda" 1162
      "428e16375796971238ed3aaeb50e76e40aa78696"
      "DASHI.Moonshine.Monster3BLinearActionProofRelevantHardeningExact"
      "Proof-relevant weight-two/literal-zeta wrappers exist; actual selected Monster inhabitants remain absent."
    hZetaCompilerSource := siblingReceipt "chboishabba/dashi_agda" 1162
      "428e16375796971238ed3aaeb50e76e40aa78696"
      "DASHI.Moonshine.Monster3BHZetaCharacterTransportCompilerExact"
      "Concrete fixed-phase representation and same-character inputs compile the H_zeta equivariant isomorphism."
    isotypicCompilerSource := siblingReceipt "chboishabba/dashi_agda" 1162
      "428e16375796971238ed3aaeb50e76e40aa78696"
      "DASHI.Moonshine.Monster3BWholeCharacterIsotypicAssemblyLeanReceiptExact"
      "Generic simple classifier, isotypic assembly and post-recognition copy-count are source-written; actual Monster instantiation remains open."
    genericClassifierStillTerminal := false
    genericIsotypicAssemblyStillTerminal := false
    actualWeightTwoLinearBridgePaid := false
    actualLinearRestrictionPaid := false
    actualWholeCharacterSimpleNonzeroInputsPaid := false
    actualHZetaSameObjectRecognitionPaid := false
    actualIsotypicRecognitionPaid := false
    actualMultiplicityNinetyPaid := false
    actualMultiplicityHomNormalizerActionPaid := false
    actualTwelveSeventyEightActionIntertwinerPaid := false }

structure GaugePrimitiveFrontier where
  pinnedR457CompilerSource : PrimitiveSourceReceipt
  round131CompilerSource : PrimitiveSourceReceipt
  terminalSource : PrimitiveSourceReceipt
  round131AttachmentStillPrimitive : Bool
  r457PinnedConstructionIdentityStillPrimitive : Bool
  pinnedYangMillsConstructionPaid : Bool
  r114LiteralStressCoordinatePaid : Bool
  r119SelectedMetricStressSemanticsPaid : Bool
  r122LiteralDensityAnchoringPaid : Bool
  r124DensityFiniteMeasureWeldPaid : Bool
  r127SourceOSSchwingerWeldPaid : Bool
  pinnedLiteralSelectedQFTTargetIdentityPaid : Bool
  selectedGroupQuaternionSU2RealizationPaid : Bool
  selectedQFTCartanFieldRealizationPaid : Bool
  freeMaxwellActionNormalizationPaid : Bool
  selectedCurvatureSameObjectTransportPaid : Bool
  generatedActionPathStressAttachmentsPaid : Bool
  brownMaclayFullStressAttachmentPaid : Bool
  round131AllSectorAssemblyPaid : Bool
  einsteinCommonMetricVariationPaid : Bool
  primitiveSourceLeavesPaid : Bool
  deriving Repr

def gaugePrimitiveFrontier : GaugePrimitiveFrontier :=
  { pinnedR457CompilerSource := siblingReceipt "chboishabba/dashi_agda" 1165
      "64c8d33320a8e313064a565068ae399566b4de23"
      "DASHI.Physics.QuantumVacuum.CasimirPinnedR457SourceNativeCompilerExact"
      "R114+R119 -> R120; +R122 -> R123; +R124 -> R125; pinned continuum + R127 -> R126/R128/R457. Wrapper payments are contracted."
    round131CompilerSource := siblingReceipt "chboishabba/dashi_agda" 1165
      "64c8d33320a8e313064a565068ae399566b4de23"
      "DASHI.Physics.QuantumVacuum.CasimirRound131PinnedRecoveryCompilerExact"
      "Pinned-literal=qftTarget plus QFTRecoveryReceipt compiles Round131 recovery; pinned construction identity is not independent on the canonical route."
    terminalSource := siblingReceipt "chboishabba/dashi_agda" 1165
      "64c8d33320a8e313064a565068ae399566b4de23"
      "DASHI.Physics.QuantumVacuum.Casimir369StressEnergySourceNativeTerminalExact"
      "Authoritative primitive source-leaf ordering for selected Casimir/GRQFT."
    round131AttachmentStillPrimitive := false
    r457PinnedConstructionIdentityStillPrimitive := false
    pinnedYangMillsConstructionPaid := false
    r114LiteralStressCoordinatePaid := false
    r119SelectedMetricStressSemanticsPaid := false
    r122LiteralDensityAnchoringPaid := false
    r124DensityFiniteMeasureWeldPaid := false
    r127SourceOSSchwingerWeldPaid := false
    pinnedLiteralSelectedQFTTargetIdentityPaid := false
    selectedGroupQuaternionSU2RealizationPaid := false
    selectedQFTCartanFieldRealizationPaid := false
    freeMaxwellActionNormalizationPaid := false
    selectedCurvatureSameObjectTransportPaid := false
    generatedActionPathStressAttachmentsPaid := false
    brownMaclayFullStressAttachmentPaid := false
    round131AllSectorAssemblyPaid := false
    einsteinCommonMetricVariationPaid := false
    primitiveSourceLeavesPaid := false }

structure ArithmeticPrimitiveFrontier where
  canonicalCubicCharacterCubeFibreCertificatePaid : Bool
  cubicJacobiSelectedPrimaryEvaluationPaid : Bool
  splitPrimeFrobeniusPaid : Bool
  sameCurveHeckeGroessencharacterPaid : Bool
  allGoodPrimeEulerAgreementPaid : Bool
  deriving Repr

def arithmeticPrimitiveFrontier : ArithmeticPrimitiveFrontier :=
  { canonicalCubicCharacterCubeFibreCertificatePaid := false
    cubicJacobiSelectedPrimaryEvaluationPaid := false
    splitPrimeFrobeniusPaid := false
    sameCurveHeckeGroessencharacterPaid := false
    allGoodPrimeEulerAgreementPaid := false }

structure QuantumPrimitiveFrontier where
  selectedHilbertToFiniteGTPSAttachmentPaid : Bool
  physicalSourceGTPSPaid : Bool
  physicalHamiltonianAttachmentPaid : Bool
  minimizerDerivativePullbackPaid : Bool
  thermodynamicLimitPaid : Bool
  sameStateRTHolographicWeldPaid : Bool
  deriving Repr

def quantumPrimitiveFrontier : QuantumPrimitiveFrontier :=
  { selectedHilbertToFiniteGTPSAttachmentPaid := false
    physicalSourceGTPSPaid := false
    physicalHamiltonianAttachmentPaid := false
    minimizerDerivativePullbackPaid := false
    thermodynamicLimitPaid := false
    sameStateRTHolographicWeldPaid := false }

structure CurrentPrimitiveMaxCut where
  monster : MonsterPrimitiveFrontier
  gaugeQFTGR : GaugePrimitiveFrontier
  arithmeticCM : ArithmeticPrimitiveFrontier
  quantumMatter : QuantumPrimitiveFrontier
  wrapperDebtContracted : Bool
  attributionFirewallRetained : Bool
  deriving Repr

def currentPrimitiveMaxCut : CurrentPrimitiveMaxCut :=
  { monster := monsterPrimitiveFrontier
    gaugeQFTGR := gaugePrimitiveFrontier
    arithmeticCM := arithmeticPrimitiveFrontier
    quantumMatter := quantumPrimitiveFrontier
    wrapperDebtContracted := true
    attributionFirewallRetained := true }

end DASHITOE
