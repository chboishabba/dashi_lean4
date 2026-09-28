import Mathlib
import Integration.OggSSPP2F4FrobeniusCandidateNoGo
import Integration.OggSSPP2F4AntipodalStratifiedRefinement
import Integration.OggSSPP2F4DependentMarkedCover
import Integration.OggSSPP2FrobeniusRetainedTarget
import Integration.OggSSPP2BalancedTernaryPuncturedPlane
import Integration.OggSSPP2BalancedTernaryNeutralCompletionBridge
import Integration.OggSSPP2BadPrimeLevelStructureBoundary

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
  | missingFormalCMOrbitEquivalence
  | missingArithmeticOneOneEightMarking
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
  duplicatedCentreCompletionBridgeOwned : Bool
  badPrimeLevelStructureBoundaryOwned : Bool
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
  duplicatedCentreCompletionBridgeOwned := true
  badPrimeLevelStructureBoundaryOwned := true
  naiveFullE4PointSetIdentificationRuledOut := true
  stabilizerTypeCompatibilityOwned := true
  movingFrobeniusDiscreteTargetNoGoOwned := true
  movingC2TenOrbitPositiveControlOwned := true
  arithmeticCMOrbitEquivalenceConstructed := false
  arithmeticOneOneEightMarkingConstructed := false
  arithmeticRecognitionConstructed := false
  firstResidual := .missingFormalCMOrbitEquivalence

end Integration.OggSSPP2GaussianCMMarkedSourceFrontier
