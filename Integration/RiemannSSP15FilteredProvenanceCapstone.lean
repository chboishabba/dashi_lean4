import Integration.RiemannSSP15RHProducerDonorManifest
import Mathlib
import Integration.RiemannPrimitiveKernelSmithFiltrationSeparation
import Integration.RiemannSSP15DepthFiveRoleCodec
import Integration.RiemannSSP15SignedProvenanceBridge
import Integration.RiemannSSP15PartitionSeparation
import Integration.RiemannSSP15ChosenGridTransversality

/-!
# RH filtered provenance / SSP15 capstone

The finite/lattice work is paid.  The remaining semantic gate is a
producer-side same-object certificate giving four actual analytic coordinates
with coefficients 80, 243, 1215, 972.

Only after such a certificate exists may the O/j/s depth-five roles be treated
as source-native analytic provenance rather than repository indexing.
-/

namespace Integration.RiemannSSP15FilteredProvenanceCapstone

open Integration.RiemannSSP15DepthFiveRoleCodec

structure PrimitiveRowProducerRoleCertificate where
  ProducerCoordinate : Type
  poleCoordinate : ProducerCoordinate
  originCoordinate : ProducerCoordinate
  jCoordinate : ProducerCoordinate
  sCoordinate : ProducerCoordinate
  coefficientOf : ProducerCoordinate → Nat
  poleCoefficientExact : coefficientOf poleCoordinate = 80
  originCoefficientExact : coefficientOf originCoordinate = 243
  jCoefficientExact : coefficientOf jCoordinate = 1215
  sCoefficientExact : coefficientOf sCoordinate = 972
  sourceOwner : String

namespace PrimitiveRowProducerRoleCertificate

def depthFiveCoordinate
    (C : PrimitiveRowProducerRoleCertificate) :
    RHDepthFiveRole → C.ProducerCoordinate
  | .origin => C.originCoordinate
  | .j => C.jCoordinate
  | .s => C.sCoordinate

def depthFiveCoefficient
    (C : PrimitiveRowProducerRoleCertificate)
    (r : RHDepthFiveRole) : Nat :=
  C.coefficientOf (C.depthFiveCoordinate r)

theorem origin_coefficient
    (C : PrimitiveRowProducerRoleCertificate) :
    C.depthFiveCoefficient .origin = 243 :=
  C.originCoefficientExact

theorem j_coefficient
    (C : PrimitiveRowProducerRoleCertificate) :
    C.depthFiveCoefficient .j = 1215 :=
  C.jCoefficientExact

theorem s_coefficient
    (C : PrimitiveRowProducerRoleCertificate) :
    C.depthFiveCoefficient .s = 972 :=
  C.sCoefficientExact

end PrimitiveRowProducerRoleCertificate

structure ProducerMarkedSSP15Code
    (C : PrimitiveRowProducerRoleCertificate) where
  mode : Mode5
  role : RHDepthFiveRole
  producerCoordinate : C.ProducerCoordinate
  producerCoordinateIsRoleCoordinate :
    producerCoordinate = C.depthFiveCoordinate role

def canonicalProducerMarkedCode
    (C : PrimitiveRowProducerRoleCertificate)
    (m : Mode5)
    (r : RHDepthFiveRole) :
    ProducerMarkedSSP15Code C :=
  ⟨m,r,C.depthFiveCoordinate r,rfl⟩

def ProducerMarkedSSP15Code.erase
    {C : PrimitiveRowProducerRoleCertificate}
    (x : ProducerMarkedSSP15Code C) :
    RHSSP15RoleCode :=
  (x.mode,x.role)

theorem producer_marked_role_code_roundtrip
    (C : PrimitiveRowProducerRoleCertificate)
    (m : Mode5)
    (r : RHDepthFiveRole) :
    decodeRoleCode
      (encodeRoleCode
        (canonicalProducerMarkedCode C m r).erase)
      =
    (m,r) := by
  simpa using decode_encode (m,r)

inductive PromotionError
  | repositoryCodecAloneCreatesProducerCertificate
  | finiteFifteenCodecCreatesAnalyticSameObject
  deriving DecidableEq, Repr

structure Boundary where
  primitiveSmithInvariantOnePaid : Bool
  rawDepthTupleBasisInvariant : Bool
  mod243KernelTransportPaid : Bool
  fiveByThreeRoleCodecPaid : Bool
  pointedSignedProvenancePaid : Bool
  partitionSeparationPaid : Bool
  chosenGridTransversalityPaid : Bool
  producerRoleCertificateTypeDefined : Bool
  sourceNativeProducerTheoremLocatedAndPinned : Bool
  sourceNativeFourCoordinateTermsLocated : Bool
  donorImportedIntoCurrentSourceGraph : Bool
  producerRoleCertificateInhabitedHere : Bool
  analyticRolePromotionPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  primitiveSmithInvariantOnePaid := true
  rawDepthTupleBasisInvariant := false
  mod243KernelTransportPaid := true
  fiveByThreeRoleCodecPaid := true
  pointedSignedProvenancePaid := true
  partitionSeparationPaid := true
  chosenGridTransversalityPaid := true
  producerRoleCertificateTypeDefined := true
  sourceNativeProducerTheoremLocatedAndPinned := true
  sourceNativeFourCoordinateTermsLocated := true
  donorImportedIntoCurrentSourceGraph := false
  producerRoleCertificateInhabitedHere := false
  analyticRolePromotionPaid := false

end Integration.RiemannSSP15FilteredProvenanceCapstone
