import Integration.RationalAlbertCubicNormStructure
import Integration.RationalAlbertCubicRigidity
import Integration.RationalAlbertF4ClassificationInstantiation
import Integration.RationalAlbertF4SplitRootDatumReceipt

/-!
# Current Albert/F4 max-cut after native cubic-norm reconstruction

This owner is the authoritative ledger for the post-split-root, post-cubic-norm
state.  It supersedes earlier shorthand that treated `unit + cubic` rigidity as
already automatic.

Paid locally:

* literal rational `H₃(O_Q)` Jordan algebra;
* standard cubic, bilinear trace, quadratic adjoint and cross product;
* `(x#)# = N(x)x`;
* exact cubic polarization/gradient identity;
* `1 × x = T(x)1 - x`;
* exact recovery of the existing Jordan product from `(N,#,T,1)`;
* cubic-norm-structure automorphism -> Jordan automorphism;
* native Cartan and companion exact split-F4 root grading.

Still separate:

* prove that a merely linear cubic symmetry fixing `1` preserves the adjoint
  (equivalently finish the nondegenerate gradient-uniqueness compiler);
* classify the resulting rational automorphism/structure groups as the desired
  Q-form of F4/E6.
-/

namespace Integration.RationalAlbertF4CubicNormMaxCut

open Integration.RationalAlbertCubicNormStructure
open Integration.RationalAlbertCubicRigidity
open Integration.RationalAlbertF4ClassificationInstantiation
open Integration.RationalAlbertF4SplitRootDatumReceipt

structure CurrentBoundary where
  nativeCubicNormTyped : Bool
  adjointIdentityPaid : Bool
  cubicPolarizationPaid : Bool
  traceRecoveredFromNorm : Bool
  tracePairRecoveredFromNorm : Bool
  jordanRecoveredFromCubicData : Bool
  cubicNormAutomorphismCompilesToJordan : Bool
  normUnitForcesAdjointPreservation : Bool
  splitF4RootDatumRecognized : Bool
  originalQFormClassified : Bool
  autJordanTypeF4 : Bool
  cubicStructureGroupTypeE6 : Bool
  f4EqualsE6UnitStabilizer : Bool
  deriving Repr

def canonicalBoundary : CurrentBoundary where
  nativeCubicNormTyped := true
  adjointIdentityPaid := true
  cubicPolarizationPaid := true
  traceRecoveredFromNorm := true
  tracePairRecoveredFromNorm := true
  jordanRecoveredFromCubicData := true
  cubicNormAutomorphismCompilesToJordan := true
  normUnitForcesAdjointPreservation := false
  splitF4RootDatumRecognized := true
  originalQFormClassified := false
  autJordanTypeF4 := false
  cubicStructureGroupTypeE6 := false
  f4EqualsE6UnitStabilizer := false

/-- The next local theorem is now isolated independently of group naming. -/
structure NativeNormUnitRigidityPayment where
  rigidity : NormUnitRigidity

/-- Once native norm/unit rigidity and the external characteristic-zero
classification are both supplied, no carrier-level or root-level premise is
left hidden in this lane. -/
structure TerminalPayments where
  nativeRigidity : NativeNormUnitRigidityPayment
  classification : CharacteristicZeroAlbertClassificationTheorem
  instantiation : ClassificationInstantiation classification

end Integration.RationalAlbertF4CubicNormMaxCut
