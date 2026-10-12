import RequestProject.QuantumMereologyPointerProbability
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Matrix.Mul

/-!
# Constructive finite spectral projector chart

The existing pointer-probability owner deliberately leaves projector algebra as
an explicit authority because the generic CPO owner does not construct an
eigenbasis.  This file pays two finite-dimensional pieces:

1. the coordinate rank-one projector family, with Hermitian, idempotent,
   pairwise-orthogonal and completeness theorems;
2. the upstream mathlib spectral theorem for every finite Hermitian complex
   matrix, exposing an orthonormal eigenbasis, real eigenvalues and a unitary
   diagonalisation.

What remains unpaid is the same-object representation bridge from the generic
selected Carroll--Singh CPO factor operator (currently a linear-map carrier) to
a concrete finite Hermitian matrix on which the spectral theorem is applied.
No preferred TPS or physical pointer basis is created by this module.
-/

namespace QuantumMereology
namespace StandardBasisProjector

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Indicator of one coordinate of the finite basis. -/
def indicator (j : I) : I → ℂ :=
  fun i => if i = j then 1 else 0

/-- Rank-one coordinate projector onto basis label `j`. -/
def projector (j : I) : Matrix I I ℂ :=
  Matrix.diagonal (indicator j)

/-- Coordinate projectors are Hermitian. -/
theorem projector_hermitian (j : I) : (projector j).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i k
  by_cases hik : i = k
  · subst k
    simp [projector, indicator]
  · simp [projector, indicator, hik, Ne.symm hik]

/-- Coordinate projectors are idempotent. -/
theorem projector_idempotent (j : I) :
    projector j * projector j = projector j := by
  rw [projector, Matrix.diagonal_mul_diagonal]
  ext i k
  by_cases hik : i = k
  · subst k
    by_cases hij : i = j <;> simp [indicator, hij]
  · simp [indicator, hik]

/-- Distinct coordinate projectors are orthogonal. -/
theorem projector_orthogonal {j k : I} (hjk : j ≠ k) :
    projector j * projector k = 0 := by
  rw [projector, projector, Matrix.diagonal_mul_diagonal]
  ext i l
  by_cases hil : i = l
  · subst l
    by_cases hij : i = j
    · subst i
      simp [indicator, hjk]
    · simp [indicator, hij]
  · simp [indicator, hil]

/-- The coordinate projectors resolve the identity. -/
theorem projector_complete :
    (∑ j : I, projector j) = 1 := by
  ext i k
  by_cases hik : i = k
  · subst k
    simp [projector, indicator]
  · simp [projector, indicator, hik]

/-- The concrete projector family consumed by the finite pointer-probability
owner.  Unlike the generic socket, its orthogonality and completeness fields are
actual matrix propositions with local proofs. -/
def family : PointerProbability.ProjectorFamily (I := I) (J := I) where
  projector := projector
  hermitian := projector_hermitian
  idempotent := projector_idempotent
  OrthogonalAuthority :=
    ∀ j k : I, j ≠ k → projector j * projector k = 0
  orthogonalAuthority := fun _ _ h => projector_orthogonal h
  CompletenessAuthority := (∑ j : I, projector j) = 1
  completenessAuthority := projector_complete

/-- A real-spectrum observable diagonal in the coordinate chart. -/
def diagonalObservable (eigenvalue : I → ℝ) : Matrix I I ℂ :=
  Matrix.diagonal (fun i => (eigenvalue i : ℂ))

/-- Each coordinate projector is a right spectral projector for a diagonal
observable. -/
theorem projector_mul_diagonalObservable
    (eigenvalue : I → ℝ) (j : I) :
    projector j * diagonalObservable eigenvalue =
      (eigenvalue j : ℂ) • projector j := by
  ext i k
  by_cases hik : i = k
  · subst k
    by_cases hij : i = j
    · subst i
      simp [projector, indicator, diagonalObservable,
        Matrix.diagonal_mul_diagonal]
    · simp [projector, indicator, diagonalObservable,
        Matrix.diagonal_mul_diagonal, hij]
  · simp [projector, indicator, diagonalObservable,
      Matrix.diagonal_mul_diagonal, hik]

/-- And likewise on the left. -/
theorem diagonalObservable_mul_projector
    (eigenvalue : I → ℝ) (j : I) :
    diagonalObservable eigenvalue * projector j =
      (eigenvalue j : ℂ) • projector j := by
  ext i k
  by_cases hik : i = k
  · subst k
    by_cases hij : i = j
    · subst i
      simp [projector, indicator, diagonalObservable,
        Matrix.diagonal_mul_diagonal]
    · simp [projector, indicator, diagonalObservable,
        Matrix.diagonal_mul_diagonal, hij]
  · simp [projector, indicator, diagonalObservable,
      Matrix.diagonal_mul_diagonal, hik]

/-! ## Finite Hermitian spectral theorem donor

Mathlib v4.28 already proves the nonconstructive finite spectral theorem needed
for a *concrete Hermitian matrix*.  We expose the exact donor rather than
leaving "eigenbasis construction" as one undifferentiated obligation.
-/

/-- Canonical orthonormal eigenbasis supplied by mathlib for a finite Hermitian
complex matrix. -/
noncomputable def hermitianEigenvectorBasis
    {A : Matrix I I ℂ} (hA : A.IsHermitian) :=
  hA.eigenvectorBasis

/-- Real eigenvalue function paired with the canonical eigenbasis. -/
noncomputable def hermitianEigenvalues
    {A : Matrix I I ℂ} (hA : A.IsHermitian) : I → ℝ :=
  hA.eigenvalues

/-- Canonical unitary change of basis whose columns are the eigenvectors. -/
noncomputable def hermitianEigenvectorUnitary
    {A : Matrix I I ℂ} (hA : A.IsHermitian) :=
  hA.eigenvectorUnitary

/-- Same-object finite spectral theorem: every concrete Hermitian complex matrix
is the unitary conjugate of the diagonal matrix of its real eigenvalues. -/
theorem hermitian_spectral_theorem
    {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    A =
      Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) :=
  hA.spectral_theorem

/-- The eigenbasis vectors satisfy the literal matrix eigenvector equation. -/
theorem hermitian_eigenvector_equation
    {A : Matrix I I ℂ} (hA : A.IsHermitian) (j : I) :
    A *ᵥ ⇑(hA.eigenvectorBasis j) =
      (hA.eigenvalues j) • ⇑(hA.eigenvectorBasis j) :=
  hA.mulVec_eigenvectorBasis j

/-- A same-object attachment is still required from the generic selected CPO
factor operator to a concrete Hermitian matrix.  Once such a representative is
provided, mathlib supplies its spectral chart; this record does not fabricate
the representation weld. -/
structure SelectedCPOHermitianMatrixAttachment where
  selectedCPOFactorMatrix : Matrix I I ℂ
  selectedCPOFactorHermitian : selectedCPOFactorMatrix.IsHermitian
  SameObjectCPOFactorMatrix : Prop
  sameObjectCPOFactorMatrix : SameObjectCPOFactorMatrix

namespace SelectedCPOHermitianMatrixAttachment

noncomputable def eigenvectorBasis
    (A : SelectedCPOHermitianMatrixAttachment (I := I)) :=
  A.selectedCPOFactorHermitian.eigenvectorBasis

noncomputable def eigenvalues
    (A : SelectedCPOHermitianMatrixAttachment (I := I)) : I → ℝ :=
  A.selectedCPOFactorHermitian.eigenvalues

noncomputable def eigenvectorUnitary
    (A : SelectedCPOHermitianMatrixAttachment (I := I)) :=
  A.selectedCPOFactorHermitian.eigenvectorUnitary

theorem spectral_theorem
    (A : SelectedCPOHermitianMatrixAttachment (I := I)) :
    A.selectedCPOFactorMatrix =
      Unitary.conjStarAlgAut ℂ _ A.eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘ A.eigenvalues)) :=
  A.selectedCPOFactorHermitian.spectral_theorem

end SelectedCPOHermitianMatrixAttachment

structure Boundary where
  standardBasisProjectorFamilyPaid : Bool := true
  diagonalSpectralProjectorLawPaid : Bool := true
  finiteHermitianSpectralBasisPaid : Bool := true
  arbitrarySelectedCPOEigenbasisPaid : Bool := false
  sameObjectCPOFactorMatrixAutomatic : Bool := false
  projectorCompilerCreatesPreferredTPS : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem standard_basis_projector_family_paid :
    canonicalBoundary.standardBasisProjectorFamilyPaid = true := rfl

theorem diagonal_spectral_projector_law_paid :
    canonicalBoundary.diagonalSpectralProjectorLawPaid = true := rfl

theorem finite_hermitian_spectral_basis_paid :
    canonicalBoundary.finiteHermitianSpectralBasisPaid = true := rfl

theorem arbitrary_selected_cpo_eigenbasis_not_paid :
    canonicalBoundary.arbitrarySelectedCPOEigenbasisPaid = false := rfl

theorem same_object_cpo_factor_matrix_not_automatic :
    canonicalBoundary.sameObjectCPOFactorMatrixAutomatic = false := rfl

def dashiStandardBasisProjectorReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI Lean"
  claim := "Constructs finite coordinate rank-one projectors and proves Hermitian, idempotent, pairwise-orthogonal, complete and diagonal spectral laws. It also exposes mathlib v4.28's finite Hermitian eigenbasis/unitary spectral theorem. The remaining selected-CPO obligation is the same-object bridge from the generic CPO factor linear map to a concrete Hermitian matrix representative; no preferred TPS or physical pointer basis is manufactured."

end StandardBasisProjector
end QuantumMereology
