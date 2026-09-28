import Mathlib
import Synthesis.RiemannQuarticProducerRoleCertificate
import Integration.RiemannSSP15FilteredProvenanceCapstone
import Integration.RiemannSSP15SignedFRACTRAN

/-!
# Same-source-graph RH producer -> SSP15 signed FRACTRAN weld

This branch is rooted at the RH analytic donor, so the actual source-native
producer certificate and the lightweight SSP15 integration machinery coexist
in one Lean source graph.

The crucial binding is:
* capstone poleCoordinate   := RH producer .pole
* capstone originCoordinate := RH producer .origin
* capstone jCoordinate      := RH producer .j
* capstone sCoordinate      := RH producer .target

Thus the SSP15 s role is explicitly the RH quartic target S, not an
independently invented fourth analytic coordinate.

The marked depth-five roles then compile through the already-proved SSP15
chosen-prime indexing into signed FRACTRAN:
* origin -> inverse-prime token
* j      -> empty arithmetic program while retaining selected prime
* s      -> positive-prime token

No claim is made that this chosen 5x3 indexing is canonical arithmetic
semantics.
-/

namespace Integration.RiemannSSP15RHProducerSameGraphWeld

namespace RH := Synthesis.RiemannQuarticProducerRoleCertificate
namespace Cap := Integration.RiemannSSP15FilteredProvenanceCapstone
namespace Codec := Integration.RiemannSSP15DepthFiveRoleCodec
namespace SF := Integration.RiemannSSP15SignedFRACTRAN
namespace Prov := Integration.RiemannSSP15SignedProvenanceBridge

def importedProducerCertificate : Cap.PrimitiveRowProducerRoleCertificate where
  ProducerCoordinate := RH.ProducerRole
  poleCoordinate := .pole
  originCoordinate := .origin
  jCoordinate := .j
  sCoordinate := .target
  coefficientOf := RH.coefficient
  poleCoefficientExact := RH.pole_coefficient_exact
  originCoefficientExact := RH.origin_coefficient_exact
  jCoefficientExact := RH.j_coefficient_exact
  sCoefficientExact := RH.target_coefficient_exact
  sourceOwner :=
    "Synthesis.RiemannQuarticProducerRoleCertificate.canonicalSourceNativeProducerRoleCertificate"

theorem imported_certificate_inhabited :
    Nonempty Cap.PrimitiveRowProducerRoleCertificate :=
  ⟨importedProducerCertificate⟩

theorem imported_pole_is_source_pole :
    importedProducerCertificate.poleCoordinate = RH.ProducerRole.pole := rfl

theorem imported_origin_is_source_origin :
    importedProducerCertificate.originCoordinate = RH.ProducerRole.origin := rfl

theorem imported_j_is_source_j :
    importedProducerCertificate.jCoordinate = RH.ProducerRole.j := rfl

theorem imported_s_is_source_target :
    importedProducerCertificate.sCoordinate = RH.ProducerRole.target := rfl

theorem imported_depth_five_coefficients :
    importedProducerCertificate.depthFiveCoefficient .origin = 243 ∧
    importedProducerCertificate.depthFiveCoefficient .j = 1215 ∧
    importedProducerCertificate.depthFiveCoefficient .s = 972 := by
  exact
    ⟨Cap.PrimitiveRowProducerRoleCertificate.origin_coefficient _,
      Cap.PrimitiveRowProducerRoleCertificate.j_coefficient _,
      Cap.PrimitiveRowProducerRoleCertificate.s_coefficient _⟩

theorem imported_source_primitive_kernel
    (lam mu : ℝ) :
    RH.weightedCoordinate .pole lam mu
      + RH.weightedCoordinate .origin lam mu
      + RH.weightedCoordinate .j lam mu
      + RH.weightedCoordinate .target lam mu
      = 0 :=
  RH.primitive_kernel_via_source_roles lam mu

def depthFiveSourceRole : Codec.RHDepthFiveRole → RH.ProducerRole
  | .origin => .origin
  | .j => .j
  | .s => .target

theorem depth_five_source_role_is_certificate_coordinate
    (role : Codec.RHDepthFiveRole) :
    importedProducerCertificate.depthFiveCoordinate role
      = depthFiveSourceRole role := by
  cases role <;> rfl

theorem depth_five_source_coefficient_exact
    (role : Codec.RHDepthFiveRole) :
    importedProducerCertificate.depthFiveCoefficient role
      = RH.coefficient (depthFiveSourceRole role) := by
  cases role <;> rfl

def markedCode
    (mode : Codec.Mode5)
    (role : Codec.RHDepthFiveRole) :
    Cap.ProducerMarkedSSP15Code importedProducerCertificate :=
  Cap.canonicalProducerMarkedCode importedProducerCertificate mode role

def signedSeed
    (mode : Codec.Mode5)
    (role : Codec.RHDepthFiveRole) :
    SF.PointedSeed :=
  SF.seed (markedCode mode role).erase

theorem signed_seed_reopens_marked_role
    (mode : Codec.Mode5)
    (role : Codec.RHDepthFiveRole) :
    Prov.primeToRoleCode (signedSeed mode role).pointed.selectedPrime
      = (mode, role) := by
  simpa [signedSeed, markedCode] using
    SF.pointed_seed_reopens_role_code (mode, role)

theorem origin_role_executes_inverse
    (mode : Codec.Mode5) :
    (SF.executeSeed (signedSeed mode .origin)).inversePrimeTokens = 1 := by
  simpa [signedSeed, markedCode] using SF.origin_has_one_inverse mode

theorem j_role_executes_empty
    (mode : Codec.Mode5) :
    SF.executeSeed (signedSeed mode .j) = SF.emptyEffect := by
  simpa [signedSeed, markedCode] using SF.j_effect_empty mode

theorem s_target_role_executes_positive
    (mode : Codec.Mode5) :
    (SF.executeSeed (signedSeed mode .s)).positivePrimeTokens = 1 := by
  simpa [signedSeed, markedCode] using SF.s_has_one_positive mode

theorem producer_origin_orientation_inverse
    (mode : Codec.Mode5) :
    (SF.hyperformLane (markedCode mode .origin).erase).orientation
      = .inverse := by
  simpa [markedCode] using SF.origin_hyperform_orientation_inverse mode

theorem producer_j_orientation_mediated
    (mode : Codec.Mode5) :
    (SF.hyperformLane (markedCode mode .j).erase).orientation
      = .mediated := by
  simpa [markedCode] using SF.j_hyperform_orientation_mediated mode

theorem producer_s_target_orientation_forward
    (mode : Codec.Mode5) :
    (SF.hyperformLane (markedCode mode .s).erase).orientation
      = .forward := by
  simpa [markedCode] using SF.s_hyperform_orientation_forward mode

theorem neutral_j_selected_primes_survive :
    ((signedSeed .mode09 .j).pointed.selectedPrime,
     (signedSeed .mode18 .j).pointed.selectedPrime,
     (signedSeed .mode27 .j).pointed.selectedPrime,
     (signedSeed .mode36 .j).pointed.selectedPrime,
     (signedSeed .mode45 .j).pointed.selectedPrime)
    =
    (.p3,.p11,.p19,.p31,.p59) := rfl

theorem neutral_j_execution_collapses :
    SF.executeSeed (signedSeed .mode09 .j)
      = SF.executeSeed (signedSeed .mode18 .j) ∧
    SF.executeSeed (signedSeed .mode18 .j)
      = SF.executeSeed (signedSeed .mode27 .j) ∧
    SF.executeSeed (signedSeed .mode27 .j)
      = SF.executeSeed (signedSeed .mode36 .j) ∧
    SF.executeSeed (signedSeed .mode36 .j)
      = SF.executeSeed (signedSeed .mode45 .j) := by
  simpa [signedSeed, markedCode] using SF.five_neutral_states_same_effect

structure RoleExecutionReceipt
    (mode : Codec.Mode5)
    (role : Codec.RHDepthFiveRole) where
  sourceRole : RH.ProducerRole
  sourceRoleExact : sourceRole = depthFiveSourceRole role
  sourceCoefficient : Nat
  sourceCoefficientExact :
    sourceCoefficient = RH.coefficient sourceRole
  selectedPrime : Grid.Prime15
  selectedPrimeExact :
    selectedPrime = (signedSeed mode role).pointed.selectedPrime
  orientation : SF.FibreOrientation
  orientationExact :
    orientation = (SF.hyperformLane (markedCode mode role).erase).orientation
  execution : SF.Effect
  executionExact :
    execution = SF.executeSeed (signedSeed mode role)

def canonicalRoleExecutionReceipt
    (mode : Codec.Mode5)
    (role : Codec.RHDepthFiveRole) :
    RoleExecutionReceipt mode role where
  sourceRole := depthFiveSourceRole role
  sourceRoleExact := rfl
  sourceCoefficient := RH.coefficient (depthFiveSourceRole role)
  sourceCoefficientExact := rfl
  selectedPrime := (signedSeed mode role).pointed.selectedPrime
  selectedPrimeExact := rfl
  orientation := (SF.hyperformLane (markedCode mode role).erase).orientation
  orientationExact := rfl
  execution := SF.executeSeed (signedSeed mode role)
  executionExact := rfl

theorem source_role_to_signed_execution_commutes
    (mode : Codec.Mode5)
    (role : Codec.RHDepthFiveRole) :
    let receipt := canonicalRoleExecutionReceipt mode role
    receipt.sourceCoefficient
      = RH.coefficient (depthFiveSourceRole role) ∧
    receipt.selectedPrime
      = (signedSeed mode role).pointed.selectedPrime ∧
    receipt.orientation
      = (SF.hyperformLane (markedCode mode role).erase).orientation ∧
    receipt.execution
      = SF.executeSeed (signedSeed mode role) := by
  simp [canonicalRoleExecutionReceipt]

theorem origin_source_to_inverse_execution
    (mode : Codec.Mode5) :
    RH.coefficient (depthFiveSourceRole .origin) = 243 ∧
    (canonicalRoleExecutionReceipt mode .origin).orientation = .inverse ∧
    (canonicalRoleExecutionReceipt mode .origin).execution.inversePrimeTokens = 1 := by
  simp [depthFiveSourceRole, canonicalRoleExecutionReceipt, signedSeed, markedCode,
    SF.hyperformLane, SF.orientationOfRole, SF.executeSeed, SF.seed, SF.roleProgram,
    SF.executeProgram, SF.applyInstruction, SF.emptyEffect]

theorem j_source_to_neutral_execution
    (mode : Codec.Mode5) :
    RH.coefficient (depthFiveSourceRole .j) = 1215 ∧
    (canonicalRoleExecutionReceipt mode .j).orientation = .mediated ∧
    (canonicalRoleExecutionReceipt mode .j).execution = SF.emptyEffect := by
  simp [depthFiveSourceRole, canonicalRoleExecutionReceipt, signedSeed, markedCode,
    SF.hyperformLane, SF.orientationOfRole, SF.executeSeed, SF.seed, SF.roleProgram,
    SF.executeProgram, SF.emptyEffect]

theorem s_source_target_to_positive_execution
    (mode : Codec.Mode5) :
    RH.coefficient (depthFiveSourceRole .s) = 972 ∧
    depthFiveSourceRole .s = RH.ProducerRole.target ∧
    (canonicalRoleExecutionReceipt mode .s).orientation = .forward ∧
    (canonicalRoleExecutionReceipt mode .s).execution.positivePrimeTokens = 1 := by
  simp [depthFiveSourceRole, canonicalRoleExecutionReceipt, signedSeed, markedCode,
    SF.hyperformLane, SF.orientationOfRole, SF.executeSeed, SF.seed, SF.roleProgram,
    SF.executeProgram, SF.applyInstruction, SF.emptyEffect]

structure Boundary where
  sourceNativeProducerCertificateImported : Bool
  sourcePoleOriginJTargetSameObjectOwned : Bool
  sRoleBoundToSourceTarget : Bool
  primitiveKernelSameGraphOwned : Bool
  markedRoleToPointedSignedSeedOwned : Bool
  originInverseJEmptySPositiveExecutionOwned : Bool
  hyperformOrientationOwned : Bool
  neutralJPrimeProvenanceRetained : Bool
  neutralJExecutionCollapseOwned : Bool
  sourceRoleToSignedExecutionReceiptOwned : Bool
  chosenSSPIndexingPromotedToCanonicalArithmeticSemantics : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  sourceNativeProducerCertificateImported := true
  sourcePoleOriginJTargetSameObjectOwned := true
  sRoleBoundToSourceTarget := true
  primitiveKernelSameGraphOwned := true
  markedRoleToPointedSignedSeedOwned := true
  originInverseJEmptySPositiveExecutionOwned := true
  hyperformOrientationOwned := true
  neutralJPrimeProvenanceRetained := true
  neutralJExecutionCollapseOwned := true
  sourceRoleToSignedExecutionReceiptOwned := true
  chosenSSPIndexingPromotedToCanonicalArithmeticSemantics := false

end Integration.RiemannSSP15RHProducerSameGraphWeld
