import RequestProject.QuantumMereologyPointerProbability
import Mathlib.Data.Matrix.Mul

/-!
# Constructive finite standard-basis projector family

The existing pointer-probability owner deliberately leaves projector algebra as
an explicit authority because the generic CPO owner does not construct an
eigenbasis.  This file pays the mechanical finite part for a concrete spectral
chart: the coordinate basis of a finite matrix space.

For every finite decidable index type `I`, the diagonal coordinate projectors
are proved Hermitian, idempotent, pairwise orthogonal and complete.  They are
also spectral projectors for every observable diagonal in that same chart.

This does **not** diagonalize an arbitrary selected Carroll--Singh CPO.  The
remaining physical/mathematical payment is a same-object eigenbasis/unitary
attachment taking the selected CPO factor operator into such a diagonal chart.
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

/-- And likewise on the left, so the projector commutes with the diagonal
observable and selects exactly its labelled eigenspace. -/
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

/-- A same-object attachment is the remaining bridge from an actual selected CPO
factor observable to this constructive spectral chart.  The record carries an
explicit matrix representative and equality to the diagonal observable; it does
not assert that every CPO has already been transported into this chart. -/
structure SelectedCPOChartAttachment where
  selectedCPOFactorMatrix : Matrix I I ℂ
  eigenvalue : I → ℝ
  sameObjectDiagonalChart :
    selectedCPOFactorMatrix = diagonalObservable eigenvalue

namespace SelectedCPOChartAttachment

/-- Once the same-object diagonal chart is supplied, the concrete family really
is an eigenprojector family for that selected matrix representative. -/
theorem projector_is_selected_spectral
    (A : SelectedCPOChartAttachment (I := I)) (j : I) :
    projector j * A.selectedCPOFactorMatrix =
      (A.eigenvalue j : ℂ) • projector j := by
  rw [A.sameObjectDiagonalChart]
  exact projector_mul_diagonalObservable A.eigenvalue j

end SelectedCPOChartAttachment

structure Boundary where
  standardBasisProjectorFamilyPaid : Bool := true
  diagonalSpectralProjectorLawPaid : Bool := true
  arbitrarySelectedCPOEigenbasisPaid : Bool := false
  sameObjectCPOChartAttachmentAutomatic : Bool := false
  projectorCompilerCreatesPreferredTPS : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem standard_basis_projector_family_paid :
    canonicalBoundary.standardBasisProjectorFamilyPaid = true := rfl

theorem diagonal_spectral_projector_law_paid :
    canonicalBoundary.diagonalSpectralProjectorLawPaid = true := rfl

theorem arbitrary_selected_cpo_eigenbasis_not_paid :
    canonicalBoundary.arbitrarySelectedCPOEigenbasisPaid = false := rfl

theorem same_object_cpo_chart_attachment_not_automatic :
    canonicalBoundary.sameObjectCPOChartAttachmentAutomatic = false := rfl

def dashiStandardBasisProjectorReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI Lean"
  claim := "Constructs the finite coordinate rank-one projector family and proves Hermitian, idempotent, pairwise-orthogonal, complete, and diagonal spectral laws. It does not prove that an arbitrary selected Carroll--Singh CPO is already diagonal in this chart."

end StandardBasisProjector
end QuantumMereology
