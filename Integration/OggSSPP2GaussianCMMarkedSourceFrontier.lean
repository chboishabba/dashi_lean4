import Mathlib
import Integration.OggSSPP2F4FrobeniusCandidateNoGo
import Integration.OggSSPP2F4AntipodalStratifiedRefinement
import Integration.OggSSPP2F4DependentMarkedCover
import Integration.OggSSPP2FrobeniusRetainedTarget
import Integration.OggSSPP2BalancedTernaryPuncturedPlane
import Integration.OggSSPP2PuncturedKernel2Bidi
import Integration.OggSSPP2TrialecticNineObserverReconciliation
import Integration.OggSSPP2TrialecticNineObserverArithmeticLoss
import Integration.OggSSPP2TrialecticNineCentreResidualBidi
import Integration.OggSSPP2DualDependentCodecBidi
import Integration.OggSSPP2ArithmeticBidiDualCodecTransport
import Integration.OggSSPP2SupersingularUniversalDeformationSource
import Integration.OggSSPP2WittPowerSeriesBase
import Integration.OggSSPP2UniversalDeformationImplementationFrontier
import Integration.OggSSPP2BalancedTernaryNeutralCompletionBridge
import Integration.OggSSPP2BadPrimeLevelStructureBoundary
import Integration.OggSSPP2Gamma0FourMarkedSubgroupSchemeSource
import Integration.OggSSPP2Gamma0FourRefinedModuliBoundary
import Integration.OggSSPP2Gamma0FourTwoIsogenyChainSource
import Integration.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparation
import Integration.OggSSPP2UniqueGamma0FourMarkingBidi
import Integration.OggSSPP2Gamma0FourSubgroupIsogenyChainBidi

/-!
# p=2 Gaussian-CM marked-source frontier

Lean capstone for the finite p=2 recognition state.

Paid:
* raw F4 Frobenius three-orbit presentation;
* nonuniform 1+1+8 target rechart;
* exact dependent marked-cover normal form;
* fixed/free stabilizer-type compatibility;
* moving-Frobenius no-go against the identity-only target;
* twenty-state moving-C2 positive control with ten orbit components.

Open:
* the actual arithmetic Gaussian-CM / X0(4) marked-state construction;
* proof that its residual family is the 1+1+8 family (or a falsification);
* arithmetic action/orbit/stabilizer recognition.
-/

namespace Integration.OggSSPP2GaussianCMMarkedSourceFrontier

open Integration.OggSSPP2F4FrobeniusCandidateNoGo
open Integration.OggSSPP2F4AntipodalStratifiedRefinement
open Integration.OggSSPP2F4DependentMarkedCover
open Integration.OggSSPP2FrobeniusRetainedTarget

inductive Residual
  | missingFormalKerFrobeniusSquaredFiniteFlatConstruction
  | missingFormalWittPowerSeriesUniversalDeformation
  | missingGamma0FourMarkedDeformationStates
  | missingUniversalDeformationTenStateBidi
  | missingSubgroupIsogenyChainBidi
  | missingFrobeniusCompatibleRecognition
  deriving DecidableEq, Repr

theorem raw_f4_orbit_count_is_three :
    Fintype.card F4Orbit = 3 := by decide

theorem dependent_target_profile_is_one_one_eight :
    markFibreSize .zeroFixed = 1 ∧
    markFibreSize .oneFixed = 1 ∧
    markFibreSize .conjugatePair = 8 :=
  mark_fibre_profile

theorem dependent_target_total_is_ten :
    markFibreSize .zeroFixed +
      markFibreSize .oneFixed +
      markFibreSize .conjugatePair = 10 :=
  total_marked_component_count

theorem uniform_three_orbit_lift_is_impossible :
    ¬ ∃ k : Nat, uniformMarkedOrbitCount k = 10 :=
  no_uniform_three_orbit_lift_to_ten

theorem stabilizer_type_match_is_paid
    (s : StratifiedTargetState) :
    rawF4OrbitStabilizerSize (stratumOf s) =
      inheritedAntipodalStabilizerSize (toRetainedTarget s) :=
  stratified_rechart_preserves_stabilizer_type s

structure ArithmeticGaussianCMRecognition where
  marking : ArithmeticGaussianCMMarking
  arithmeticCMOrbitEquivalence : Prop
  frobeniusCompatibleRecognition : Prop

inductive ClaimOrigin
  | repositoryCrossModuleInference
  | openArithmeticRecognition
  deriving DecidableEq, Repr

def finiteFrontierOrigin : ClaimOrigin := .repositoryCrossModuleInference
def arithmeticRecognitionOrigin : ClaimOrigin := .openArithmeticRecognition

structure Boundary where
  rawF4ThreeOrbitPresentationOwned : Bool
  uniformThreeOrbitLiftRuledOut : Bool
  oneOneEightDependentTargetNormalFormOwned : Bool
  balancedTernaryPuncturedPlaneNormalFormOwned : Bool
  puncturedKernel2BidiNormalFormOwned : Bool
  trialecticSharedNineObserverReconciliationOwned : Bool
  trialecticNineObserverArithmeticLossPaid : Bool
  trialecticNineCentreOnlyResidualCodecOwned : Bool
  dualDependentCodecBidiOwned : Bool
  arithmeticBidiDualCodecTransportOwned : Bool
  universalSupersingularDeformationSourceSocketOwned : Bool
  mathlibWittPowerSeriesCarrierOwned : Bool
  mathlibWittPowerSeriesLocalRingOwned : Bool
  mathlibPowerSeriesCompletenessLayersOwned : Bool
  powerSeriesMaximalIdealIdentified : Bool
  maximalIdealAdicCompletenessConstructed : Bool
  universalDeformationImplementationFrontierOwned : Bool
  singleArithmeticBidiDischargesBothFiniteCodecRecognitions : Bool
  separateArithmeticOneOneEightProofRequiredAfterBidi : Bool
  duplicatedCentreCompletionBridgeOwned : Bool
  badPrimeLevelStructureBoundaryOwned : Bool
  gamma0FourMarkedSubgroupSchemeSocketOwned : Bool
  gamma0FourRefinedCompactificationBoundaryOwned : Bool
  gamma0FourTwoIsogenyChainSocketOwned : Bool
  uniqueRawSupersingularGamma0FourSubgroupSourceBacked : Bool
  rawSubgroupChoiceCountOneVsResidualTenSeparated : Bool
  uniqueGamma0MarkingBidiContractOwned : Bool
  subgroupIsogenyChainBidiContractOwned : Bool
  gamma0FourOrderTwoSubflagRequired : Bool
  naiveFullE4PointSetIdentificationRuledOut : Bool
  stabilizerTypeCompatibilityOwned : Bool
  movingFrobeniusDiscreteTargetNoGoOwned : Bool
  movingC2TenOrbitPositiveControlOwned : Bool
  arithmeticCMOrbitEquivalenceConstructed : Bool
  arithmeticOneOneEightMarkingConstructed : Bool
  arithmeticRecognitionConstructed : Bool
  firstResidual : Residual
  deriving Repr

def canonicalBoundary : Boundary where
  rawF4ThreeOrbitPresentationOwned := true
  uniformThreeOrbitLiftRuledOut := true
  oneOneEightDependentTargetNormalFormOwned := true
  balancedTernaryPuncturedPlaneNormalFormOwned := true
  puncturedKernel2BidiNormalFormOwned := true
  trialecticSharedNineObserverReconciliationOwned := true
  trialecticNineObserverArithmeticLossPaid := true
  trialecticNineCentreOnlyResidualCodecOwned := true
  dualDependentCodecBidiOwned := true
  arithmeticBidiDualCodecTransportOwned := true
  universalSupersingularDeformationSourceSocketOwned := true
  mathlibWittPowerSeriesCarrierOwned := true
  mathlibWittPowerSeriesLocalRingOwned := true
  mathlibPowerSeriesCompletenessLayersOwned := true
  powerSeriesMaximalIdealIdentified := true
  maximalIdealAdicCompletenessConstructed := false
  universalDeformationImplementationFrontierOwned := true
  singleArithmeticBidiDischargesBothFiniteCodecRecognitions := true
  separateArithmeticOneOneEightProofRequiredAfterBidi := false
  duplicatedCentreCompletionBridgeOwned := true
  badPrimeLevelStructureBoundaryOwned := true
  gamma0FourMarkedSubgroupSchemeSocketOwned := true
  gamma0FourRefinedCompactificationBoundaryOwned := true
  gamma0FourTwoIsogenyChainSocketOwned := true
  uniqueRawSupersingularGamma0FourSubgroupSourceBacked := true
  rawSubgroupChoiceCountOneVsResidualTenSeparated := true
  uniqueGamma0MarkingBidiContractOwned := true
  subgroupIsogenyChainBidiContractOwned := true
  gamma0FourOrderTwoSubflagRequired := true
  naiveFullE4PointSetIdentificationRuledOut := true
  stabilizerTypeCompatibilityOwned := true
  movingFrobeniusDiscreteTargetNoGoOwned := true
  movingC2TenOrbitPositiveControlOwned := true
  arithmeticCMOrbitEquivalenceConstructed := false
  arithmeticOneOneEightMarkingConstructed := false
  arithmeticRecognitionConstructed := false
  firstResidual := .missingFormalKerFrobeniusSquaredFiniteFlatConstruction

end Integration.OggSSPP2GaussianCMMarkedSourceFrontier
