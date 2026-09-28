import Mathlib

/-!
# Pinned RH producer donor for the SSP15 filtered-provenance socket

The actual analytic producer lives on dashi_lean4 PR #22, not on the current
SSP15/369 integration branch.

Pinned donor:
* commit: 824f84cddf5cf424c643688c2d24e351795dac07
* file: Synthesis/RiemannQuarticBalancedTernaryStencil.lean
* git blob: 138153858e329469048175fcdeeaf75c182078be

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
  "824f84cddf5cf424c643688c2d24e351795dac07"

def donorFile : String :=
  "Synthesis/RiemannQuarticBalancedTernaryStencil.lean"

def donorBlob : String :=
  "138153858e329469048175fcdeeaf75c182078be"

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

structure Boundary where
  donorCommitPinned : Bool
  donorBlobPinned : Bool
  primitiveKernelTheoremLocated : Bool
  sparseShiftTheoremLocated : Bool
  depthFiveBlockTheoremLocated : Bool
  fourSourceNativeCoordinateTermsLocated : Bool
  contentAddressedVerifierOwned : Bool
  exactHeadVerifierObserved : Bool
  donorImportedIntoCurrentBranch : Bool
  sameGraphProducerCertificateInhabited : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  donorCommitPinned := true
  donorBlobPinned := true
  primitiveKernelTheoremLocated := true
  sparseShiftTheoremLocated := true
  depthFiveBlockTheoremLocated := true
  fourSourceNativeCoordinateTermsLocated := true
  contentAddressedVerifierOwned := true
  exactHeadVerifierObserved := false
  donorImportedIntoCurrentBranch := false
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
