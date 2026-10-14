import RequestProject.QuantumMereologyCandidatePointerObservable
import RequestProject.QuantumMereologyStandardBasisProjector
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Typed finite-Hermitian refinement of a selected Candidate Pointer Observable

The generic CPO carrier intentionally keeps its source-facing admissibility
obligations abstract. In particular, the fields named `leftHermitian` and
`rightHermitian` are propositions with supplied authorities; they are not
identified with mathlib's `LinearMap.IsSymmetric` predicate.

This module adds a strictly stronger, optional refinement for a selected CPO.
For each finite factor it requires an explicit orthonormal basis and a literal
`LinearMap.IsSymmetric` proof for the same selected factor map.

Pinned mathlib v4.28 then supplies two complementary spectral routes:
* exact Hermitian matrices in the chosen factor bases, with matrix spectral
  bases/unitary diagonalisation;
* native orthonormal eigenbases of the self-adjoint factor linear maps.

The native factor eigenbases tensor to an orthonormal eigenbasis of the exact
selected product observable `O_L tensor O_R`; each pure-tensor basis vector has
eigenvalue equal to the product of the corresponding factor eigenvalues.

Nothing here manufactures the typed refinement from the generic admissibility
record, proves the source search domain is finite/nonempty, creates uniqueness,
or promotes the mathematical CPO eigenbasis to an empirically validated pointer
basis.
-/

namespace QuantumMereology
namespace FiniteHermitianCPO

open CandidatePointerObservable
open scoped TensorProduct

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

/-- Matrix spectral basis in the supplied coordinate chart. -/
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

/-! ## Native factor spectral basis

The supplied finite orthonormal basis gives finite-dimensionality of `E`, so the
self-adjoint linear-map spectral theorem can be used directly on the same map
`f`, without first identifying the matrix eigenvectors back with vectors of E.
-/

noncomputable def nativeEigenvectorBasis
    (F : FactorRefinement I E f) :
    OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E := by
  letI : FiniteDimensional ℂ E := F.basis.toBasis.finiteDimensional_of_finite
  exact F.symmetric.eigenvectorBasis rfl

noncomputable def nativeEigenvalues
    (F : FactorRefinement I E f) :
    Fin (Module.finrank ℂ E) → ℝ := by
  letI : FiniteDimensional ℂ E := F.basis.toBasis.finiteDimensional_of_finite
  exact F.symmetric.eigenvalues rfl

/-- Literal eigenvector equation for the exact same factor linear map. -/
theorem native_eigenvector_equation
    (F : FactorRefinement I E f)
    (i : Fin (Module.finrank ℂ E)) :
    f (F.nativeEigenvectorBasis i) =
      (F.nativeEigenvalues i : ℂ) • F.nativeEigenvectorBasis i := by
  letI : FiniteDimensional ℂ E := F.basis.toBasis.finiteDimensional_of_finite
  simpa [nativeEigenvectorBasis, nativeEigenvalues] using
    F.symmetric.apply_eigenvectorBasis (n := Module.finrank ℂ E) rfl i

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

/-! ## Full selected product-CPO eigenbasis

Because the selected CPO is exactly `O_L tensor O_R`, the native factor
orthonormal eigenbases tensor to a full orthonormal basis of the selected CPO's
tensor-product carrier.
-/

noncomputable def productEigenvectorBasis
    (F : SelectedRefinement R IL IR) :
    OrthonormalBasis
      (Fin (Module.finrank ℂ Left) × Fin (Module.finrank ℂ Right))
      ℂ (TensorProduct ℂ Left Right) :=
  F.left.nativeEigenvectorBasis.tensorProduct
    F.right.nativeEigenvectorBasis

noncomputable def productEigenvalues
    (F : SelectedRefinement R IL IR) :
    (Fin (Module.finrank ℂ Left) × Fin (Module.finrank ℂ Right)) → ℝ :=
  fun ij => F.left.nativeEigenvalues ij.1 * F.right.nativeEigenvalues ij.2

/-- Every vector of the tensor-product orthonormal basis is an eigenvector of
the exact same selected product CPO, with product eigenvalue. -/
theorem selectedOperator_productEigenvector
    (F : SelectedRefinement R IL IR)
    (i : Fin (Module.finrank ℂ Left))
    (j : Fin (Module.finrank ℂ Right)) :
    CandidatePointerObservable.selectedOperator R
        (F.productEigenvectorBasis (i, j)) =
      (F.productEigenvalues (i, j) : ℂ) •
        F.productEigenvectorBasis (i, j) := by
  rw [productEigenvectorBasis, OrthonormalBasis.tensorProduct_apply]
  change
    CandidatePointerObservable.productOperator
        (S.candidate R.selected).left
        (S.candidate R.selected).right
        (F.left.nativeEigenvectorBasis i ⊗ₜ[ℂ]
          F.right.nativeEigenvectorBasis j) = _
  rw [CandidatePointerObservable.productOperator_tmul]
  rw [F.left.native_eigenvector_equation i,
      F.right.native_eigenvector_equation j]
  simp [productEigenvalues, TensorProduct.smul_tmul',
    TensorProduct.tmul_smul, smul_smul, mul_assoc]

end SelectedRefinement

/-! ## Promotion firewall -/

structure Boundary where
  typedSelectedCPORefinementCompilesHermitianMatrices : Bool := true
  typedSelectedCPORefinementCompilesSpectralBases : Bool := true
  typedSelectedCPORefinementCompilesProductEigenbasis : Bool := true
  genericAdmissibilityConstructsTypedSymmetry : Bool := false
  genericHermitianLabelEqualsIsSymmetric : Bool := false
  productEigenbasisIsAutomaticallyPhysicalPointerBasis : Bool := false
  spectralRefinementSelectsPreferredTPS : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem typed_selected_cpo_refinement_compiles_hermitian_matrices :
    canonicalBoundary.typedSelectedCPORefinementCompilesHermitianMatrices = true := rfl

theorem typed_selected_cpo_refinement_compiles_spectral_bases :
    canonicalBoundary.typedSelectedCPORefinementCompilesSpectralBases = true := rfl

theorem typed_selected_cpo_refinement_compiles_product_eigenbasis :
    canonicalBoundary.typedSelectedCPORefinementCompilesProductEigenbasis = true := rfl

theorem generic_admissibility_does_not_construct_typed_symmetry :
    canonicalBoundary.genericAdmissibilityConstructsTypedSymmetry = false := rfl

theorem generic_hermitian_label_not_identified_with_isSymmetric :
    canonicalBoundary.genericHermitianLabelEqualsIsSymmetric = false := rfl

theorem product_eigenbasis_not_promoted_to_physical_pointer_basis :
    canonicalBoundary.productEigenbasisIsAutomaticallyPhysicalPointerBasis = false := rfl

def dashiFiniteHermitianCPOReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI Lean"
  claim := "A same-selected-CPO refinement carrying finite orthonormal factor bases and literal LinearMap.IsSymmetric witnesses compiles via mathlib v4.28 into Hermitian factor matrices, native factor spectral bases, and an orthonormal tensor-product eigenbasis of the exact selected product observable with eigenvalues lambda_i mu_j. Generic source-facing Hermitian labels do not automatically inhabit this refinement, and the mathematical product eigenbasis is not promoted to an empirically validated pointer basis or preferred-TPS claim."

end FiniteHermitianCPO
end QuantumMereology
