import RequestProject.QuantumMereologyCandidatePointerObservable
import RequestProject.QuantumMereologyStandardBasisProjector
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Typed finite-Hermitian refinement of a selected Candidate Pointer Observable

The generic CPO carrier intentionally keeps its source-facing admissibility
obligations abstract.  In particular, the fields named `leftHermitian` and
`rightHermitian` are propositions with supplied authorities; they are not
identified with mathlib's `LinearMap.IsSymmetric` predicate.

This module adds a strictly stronger, optional refinement for a selected CPO.
For each finite factor it requires:

* an explicit orthonormal basis;
* a literal `LinearMap.IsSymmetric` proof for the same selected factor map.

Pinned mathlib v4.28 then supplies the exact bridge from that linear map to a
Hermitian matrix in the chosen orthonormal basis.  The finite matrix spectral
theorem from `QuantumMereologyStandardBasisProjector` then supplies the
orthonormal eigenbasis/unitary diagonalisation.

Nothing here manufactures the refinement from the generic admissibility record,
selects a preferred TPS, proves the CPO minimizer exists, or promotes the basis
to an empirically correct pointer basis.
-/

namespace QuantumMereology
namespace FiniteHermitianCPO

open CandidatePointerObservable

/-! ## One finite factor -/

structure FactorRefinement
    (I E : Type*)
    [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : E →ₗ[ℂ] E) where
  basis : OrthonormalBasis I ℂ E
  symmetric : f.IsSymmetric

namespace FactorRefinement

variable
  {I E : Type*}
  [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {f : E →ₗ[ℂ] E}

/-- Matrix of the exact same linear map in the supplied orthonormal basis. -/
def matrix (F : FactorRefinement I E f) : Matrix I I ℂ :=
  f.toMatrix F.basis.toBasis F.basis.toBasis

/-- A symmetric factor map becomes a Hermitian matrix in an orthonormal basis. -/
theorem matrix_hermitian (F : FactorRefinement I E f) :
    F.matrix.IsHermitian := by
  exact (LinearMap.isHermitian_toMatrix_iff F.basis).2 F.symmetric

/-- The finite spectral theorem is therefore available on the exact factor
matrix, not merely on an unrelated Hermitian witness. -/
noncomputable def eigenvectorBasis (F : FactorRefinement I E f) :=
  (F.matrix_hermitian).eigenvectorBasis

noncomputable def eigenvalues (F : FactorRefinement I E f) : I → ℝ :=
  (F.matrix_hermitian).eigenvalues

noncomputable def eigenvectorUnitary (F : FactorRefinement I E f) :=
  (F.matrix_hermitian).eigenvectorUnitary

theorem spectral_theorem (F : FactorRefinement I E f) :
    F.matrix =
      Unitary.conjStarAlgAut ℂ _ F.eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘ F.eigenvalues)) :=
  F.matrix_hermitian.spectral_theorem

end FactorRefinement

/-! ## Same selected CPO -/

structure SelectedRefinement
    {Left Right : Type*}
    [NormedAddCommGroup Left] [InnerProductSpace ℂ Left]
    [NormedAddCommGroup Right] [InnerProductSpace ℂ Right]
    {S : CandidatePointerObservable.Search (Left := Left) (Right := Right)}
    (R : CandidatePointerObservable.Receipt S)
    (IL IR : Type*)
    [Fintype IL] [DecidableEq IL]
    [Fintype IR] [DecidableEq IR] where
  left :
    FactorRefinement IL Left (S.candidate R.selected).left
  right :
    FactorRefinement IR Right (S.candidate R.selected).right

namespace SelectedRefinement

variable
  {Left Right : Type*}
  [NormedAddCommGroup Left] [InnerProductSpace ℂ Left]
  [NormedAddCommGroup Right] [InnerProductSpace ℂ Right]
  {S : CandidatePointerObservable.Search (Left := Left) (Right := Right)}
  {R : CandidatePointerObservable.Receipt S}
  {IL IR : Type*}
  [Fintype IL] [DecidableEq IL]
  [Fintype IR] [DecidableEq IR]

/-- Concrete Hermitian matrix of the exact selected left CPO factor. -/
def leftMatrix (F : SelectedRefinement R IL IR) : Matrix IL IL ℂ :=
  F.left.matrix

/-- Concrete Hermitian matrix of the exact selected right CPO factor. -/
def rightMatrix (F : SelectedRefinement R IL IR) : Matrix IR IR ℂ :=
  F.right.matrix

theorem leftMatrix_hermitian (F : SelectedRefinement R IL IR) :
    F.leftMatrix.IsHermitian :=
  F.left.matrix_hermitian

theorem rightMatrix_hermitian (F : SelectedRefinement R IL IR) :
    F.rightMatrix.IsHermitian :=
  F.right.matrix_hermitian

noncomputable def leftEigenvectorBasis (F : SelectedRefinement R IL IR) :=
  F.left.eigenvectorBasis

noncomputable def rightEigenvectorBasis (F : SelectedRefinement R IL IR) :=
  F.right.eigenvectorBasis

noncomputable def leftEigenvalues (F : SelectedRefinement R IL IR) : IL → ℝ :=
  F.left.eigenvalues

noncomputable def rightEigenvalues (F : SelectedRefinement R IL IR) : IR → ℝ :=
  F.right.eigenvalues

theorem left_spectral_theorem (F : SelectedRefinement R IL IR) :
    F.leftMatrix =
      Unitary.conjStarAlgAut ℂ _ F.left.eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘ F.leftEigenvalues)) :=
  F.left.spectral_theorem

theorem right_spectral_theorem (F : SelectedRefinement R IL IR) :
    F.rightMatrix =
      Unitary.conjStarAlgAut ℂ _ F.right.eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘ F.rightEigenvalues)) :=
  F.right.spectral_theorem

end SelectedRefinement

/-! ## Promotion firewall -/

structure Boundary where
  typedSelectedCPORefinementCompilesHermitianMatrices : Bool := true
  typedSelectedCPORefinementCompilesSpectralBases : Bool := true
  genericAdmissibilityConstructsTypedSymmetry : Bool := false
  genericHermitianLabelEqualsIsSymmetric : Bool := false
  spectralBasisIsAutomaticallyPhysicalPointerBasis : Bool := false
  spectralRefinementSelectsPreferredTPS : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem typed_selected_cpo_refinement_compiles_hermitian_matrices :
    canonicalBoundary.typedSelectedCPORefinementCompilesHermitianMatrices = true := rfl

theorem typed_selected_cpo_refinement_compiles_spectral_bases :
    canonicalBoundary.typedSelectedCPORefinementCompilesSpectralBases = true := rfl

theorem generic_admissibility_does_not_construct_typed_symmetry :
    canonicalBoundary.genericAdmissibilityConstructsTypedSymmetry = false := rfl

theorem generic_hermitian_label_not_identified_with_isSymmetric :
    canonicalBoundary.genericHermitianLabelEqualsIsSymmetric = false := rfl

theorem spectral_basis_not_promoted_to_physical_pointer_basis :
    canonicalBoundary.spectralBasisIsAutomaticallyPhysicalPointerBasis = false := rfl

def dashiFiniteHermitianCPOReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI Lean"
  claim := "A same-selected-CPO refinement carrying orthonormal factor bases and literal LinearMap.IsSymmetric witnesses compiles via mathlib v4.28 into Hermitian factor matrices and their finite spectral bases. Generic source-facing Hermitian labels do not automatically inhabit this stronger refinement, and no physical pointer-basis or preferred-TPS claim is created."

end FiniteHermitianCPO
end QuantumMereology
