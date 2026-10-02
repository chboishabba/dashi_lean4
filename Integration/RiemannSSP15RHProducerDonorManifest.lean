import Mathlib

/-!
# Pinned RH producer donor for the SSP15 filtered-provenance socket

The actual analytic producer lives on dashi_lean4 PR #22, not on the current
SSP15/369 integration branch.

Pinned donor:
* commit: 85f10467c453bea93bd8199ed80054b1fb41b46a
* file: Synthesis/RiemannQuarticBalancedTernaryStencil.lean
* stencil git blob: 138153858e329469048175fcdeeaf75c182078be\n* certificate file: Synthesis/RiemannQuarticProducerRoleCertificate.lean\n* certificate git blob: cb89ebc956cedd55179042cf63ff2eaf3d44f073

Load-bearing theorems:
* quarticFourAtomic_primitive_integer_kernel
* quarticFourAtomic_sparse_shift_kernel
* quarticFourAtomic_depth_five_block_kernel

The first theorem uses the actual source-native coordinates:
  quarticFourAtomicHighPoleResidual
  quarticFourAtomicProjectiveOriginCoordinate
  quarticFourAtomicJAt ... 2
  quarticFourAtomicTargetStrengthAt

with coefficients 80,243,1215,972.

This manifest does not pretend that a theorem on another branch is imported
into the current Lean environment.
-/

namespace Integration.RiemannSSP15RHProducerDonorManifest

def donorCommit : String :=
  "85f10467c453bea93bd8199ed80054b1fb41b46a"

def donorFile : String :=
  "Synthesis/RiemannQuarticBalancedTernaryStencil.lean"

def donorBlob : String :=
  "138153858e329469048175fcdeeaf75c182078be"

def producerCertificateFile : String :=
  "Synthesis/RiemannQuarticProducerRoleCertificate.lean"

def producerCertificateBlob : String :=
  "cb89ebc956cedd55179042cf63ff2eaf3d44f073"

def producerCertificateTheorem : String :=
  "Synthesis.RiemannQuarticProducerRoleCertificate.canonical_certificate_inhabited"

def sourceRoleKernelTheorem : String :=
  "Synthesis.RiemannQuarticProducerRoleCertificate.primitive_kernel_via_source_roles"

def primitiveKernelTheorem : String :=
  "Synthesis.RiemannQuarticBalancedTernaryStencil.quarticFourAtomic_primitive_integer_kernel"

def sparseShiftTheorem : String :=
  "Synthesis.RiemannQuarticBalancedTernaryStencil.quarticFourAtomic_sparse_shift_kernel"

def depthFiveBlockTheorem : String :=
  "Synthesis.RiemannQuarticBalancedTernaryStencil.quarticFourAtomic_depth_five_block_kernel"

def poleCoordinateTerm : String :=
  "quarticFourAtomicHighPoleResidual"

def originCoordinateTerm : String :=
  "quarticFourAtomicProjectiveOriginCoordinate"

def jCoordinateTerm : String :=
  "quarticFourAtomicJAt ... 2"

def targetCoordinateTerm : String :=
  "quarticFourAtomicTargetStrengthAt"

def sameGraphWeldPR : String :=
  "dashi_lean4 PR #33"

def sameGraphWeldBranch : String :=
  "agent/rh-ssp15-same-graph-weld-20260928"

def sameGraphWeldHead : String :=
  "3fb8061d2ce31a19f64b56ff6d3e0a087e019e9e"

def sameGraphWeldTheorem : String :=
  "Integration.RiemannSSP15RHProducerSameGraphWeld.imported_certificate_inhabited"

def sameGraphSignedFRACTRANTheorem : String :=
  "Integration.RiemannSSP15RHProducerSameGraphWeld.source_role_to_signed_execution_commutes"

structure Boundary where
  donorCommitPinned : Bool
  donorBlobPinned : Bool
  primitiveKernelTheoremLocated : Bool
  sparseShiftTheoremLocated : Bool
  depthFiveBlockTheoremLocated : Bool
  fourSourceNativeCoordinateTermsLocated : Bool
  sourceNativeProducerCertificateInhabitedOnDonorBranch : Bool
  sourceRoleKernelTheoremLocated : Bool
  contentAddressedVerifierOwned : Bool
  exactHeadVerifierObserved : Bool
  donorImportedIntoCurrentBranch : Bool
  sameGraphWeldSourceWritten : Bool
  sameGraphSignedFRACTRANWeldSourceWritten : Bool
  sameGraphExactHeadKernelObserved : Bool
  sameGraphProducerCertificateInhabited : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  donorCommitPinned := true
  donorBlobPinned := true
  primitiveKernelTheoremLocated := true
  sparseShiftTheoremLocated := true
  depthFiveBlockTheoremLocated := true
  fourSourceNativeCoordinateTermsLocated := true
  sourceNativeProducerCertificateInhabitedOnDonorBranch := true
  sourceRoleKernelTheoremLocated := true
  contentAddressedVerifierOwned := true
  exactHeadVerifierObserved := false
  donorImportedIntoCurrentBranch := false
  sameGraphWeldSourceWritten := true
  sameGraphSignedFRACTRANWeldSourceWritten := true
  sameGraphExactHeadKernelObserved := false
  sameGraphProducerCertificateInhabited := false

theorem donor_commit_is_pinned :
    canonicalBoundary.donorCommitPinned = true := rfl

theorem content_addressed_verifier_is_owned :
    canonicalBoundary.contentAddressedVerifierOwned = true := rfl

theorem exact_head_verifier_not_yet_observed :
    canonicalBoundary.exactHeadVerifierObserved = false := rfl

theorem donor_not_imported_into_current_branch :
    canonicalBoundary.donorImportedIntoCurrentBranch = false := rfl

end Integration.RiemannSSP15RHProducerDonorManifest
