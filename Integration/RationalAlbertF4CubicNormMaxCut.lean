import Integration.RationalAlbertCubicNormStructure
import Integration.RationalAlbertCubicRigidity
import Integration.RationalAlbertTracePairNondegenerate
import Integration.RationalAlbertNormUnitRigidityProof
import Integration.RationalAlbertF4ClassificationInstantiation
import Integration.RationalAlbertF4SplitRootDatumReceipt

/-!
# Current Albert/F4 max-cut after native cubic-norm rigidity

This is the authoritative post-split-root ledger.

Paid locally on the literal rational `H₃(O_Q)` carrier:

* standard cubic, bilinear trace, quadratic adjoint and cross product;
* `(x#)# = N(x)x`;
* exact cubic polarization/gradient identity;
* `1 × x = T(x)1 - x`;
* exact Jordan-product recovery from `(N,#,T,1)`;
* positive-definite/nondegenerate trace pairing;
* reconstruction of trace and bilinear trace from `N` and `1`;
* Q-linear norm symmetry fixing `1` preserves the adjoint;
* therefore every unit-fixing norm symmetry is a Jordan automorphism;
* native Cartan plus companion exact split-F4 root grading.

The remaining theorem is no longer product recovery or a local root-space
problem.  It is the characteristic-zero Q-form/algebraic-group classification:
identify the concrete cubic symmetry group as type E6 and its unit stabilizer /
Jordan automorphism group as the corresponding type-F4 group.
-/

namespace Integration.RationalAlbertF4CubicNormMaxCut

open Integration.RationalAlbertCubicNormStructure
open Integration.RationalAlbertCubicRigidity
open Integration.RationalAlbertNormUnitRigidityProof
open Integration.RationalAlbertF4ClassificationInstantiation
open Integration.RationalAlbertF4SplitRootDatumReceipt

structure CurrentBoundary where
  nativeCubicNormTyped : Bool
  adjointIdentityPaid : Bool
  cubicPolarizationPaid : Bool
  tracePairNondegenerate : Bool
  traceRecoveredFromNorm : Bool
  tracePairRecoveredFromNorm : Bool
  jordanRecoveredFromCubicData : Bool
  normUnitForcesAdjointPreservation : Bool
  unitFixingNormSymmetryIsJordan : Bool
  splitF4RootDatumRecognized : Bool
  originalQFormClassified : Bool
  autJordanTypeF4 : Bool
  cubicStructureGroupTypeE6 : Bool
  f4EqualsE6UnitStabilizerAsNamedGroups : Bool
  deriving Repr

def canonicalBoundary : CurrentBoundary where
  nativeCubicNormTyped := true
  adjointIdentityPaid := true
  cubicPolarizationPaid := true
  tracePairNondegenerate := true
  traceRecoveredFromNorm := true
  tracePairRecoveredFromNorm := true
  jordanRecoveredFromCubicData := true
  normUnitForcesAdjointPreservation := true
  unitFixingNormSymmetryIsJordan := true
  splitF4RootDatumRecognized := true
  originalQFormClassified := false
  autJordanTypeF4 := false
  cubicStructureGroupTypeE6 := false
  f4EqualsE6UnitStabilizerAsNamedGroups := false

/-- All local cubic-rigidity data is now inhabited explicitly. -/
def nativeRigidityPayment : NormUnitRigidity := canonicalNormUnitRigidity

/-- Only the external/general characteristic-zero classification premise remains
for the group/form naming layer. -/
structure TerminalClassificationPayment where
  classification : CharacteristicZeroAlbertClassificationTheorem
  instantiation : ClassificationInstantiation classification

end Integration.RationalAlbertF4CubicNormMaxCut
