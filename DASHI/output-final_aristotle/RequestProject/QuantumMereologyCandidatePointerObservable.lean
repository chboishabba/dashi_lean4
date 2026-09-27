import RequestProject.QuantumMereologyOperatorLocality
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Candidate Pointer Observable carrier

External source:
Sean M. Carroll and Ashmeet Singh, Phys. Rev. A 103, 022213 (2021),
DOI 10.1103/PhysRevA.103.022213, Eqs. (24)--(26).

For a fixed bipartite factorisation, the paper defines a Candidate Pointer
Observable as a nontrivial product observable O_A tensor O_B whose commutator with
the interaction Hamiltonian has minimum Frobenius norm, with the two factor
operators constrained to be Hermitian, traceless and unit-Frobenius-norm.

DASHI makes the product operator and its commutator exact here. The
Hermitian/traceless/Frobenius constraints and minimizer existence are explicit
producer obligations; they are not manufactured from the source citation.
-/

namespace QuantumMereology

open scoped TensorProduct

namespace CandidatePointerObservable

variable
  {Left Right : Type*}
  [AddCommGroup Left] [Module ℂ Left]
  [AddCommGroup Right] [Module ℂ Right]

def productOperator
    (left : Left →ₗ[ℂ] Left)
    (right : Right →ₗ[ℂ] Right) :
    TensorProduct ℂ Left Right →ₗ[ℂ] TensorProduct ℂ Left Right :=
  TensorProduct.map left right

@[simp] theorem productOperator_tmul
    (left : Left →ₗ[ℂ] Left)
    (right : Right →ₗ[ℂ] Right)
    (x : Left) (y : Right) :
    productOperator left right (x ⊗ₜ[ℂ] y) =
      left x ⊗ₜ[ℂ] right y := by
  simp [productOperator]

def commutator
    (interaction : TensorProduct ℂ Left Right →ₗ[ℂ] TensorProduct ℂ Left Right)
    (observable : TensorProduct ℂ Left Right →ₗ[ℂ] TensorProduct ℂ Left Right) :
    TensorProduct ℂ Left Right →ₗ[ℂ] TensorProduct ℂ Left Right :=
  interaction.comp observable - observable.comp interaction

structure Candidate where
  left : Left →ₗ[ℂ] Left
  right : Right →ₗ[ℂ] Right

namespace Candidate

def operator (C : Candidate (Left := Left) (Right := Right)) :
    TensorProduct ℂ Left Right →ₗ[ℂ] TensorProduct ℂ Left Right :=
  productOperator C.left C.right

end Candidate

structure Admissibility
    (C : Candidate (Left := Left) (Right := Right)) where
  leftHermitian : Prop
  leftHermitianAuthority : leftHermitian
  rightHermitian : Prop
  rightHermitianAuthority : rightHermitian
  leftTraceless : Prop
  leftTracelessAuthority : leftTraceless
  rightTraceless : Prop
  rightTracelessAuthority : rightTraceless
  leftUnitFrobenius : Prop
  leftUnitFrobeniusAuthority : leftUnitFrobenius
  rightUnitFrobenius : Prop
  rightUnitFrobeniusAuthority : rightUnitFrobenius
  nontrivialProduct : Prop
  nontrivialProductAuthority : nontrivialProduct

structure Search where
  interaction :
    TensorProduct ℂ Left Right →ₗ[ℂ] TensorProduct ℂ Left Right
  CandidateIndex : Type
  candidate : CandidateIndex → Candidate (Left := Left) (Right := Right)
  admissible : CandidateIndex → Prop
  admissibility :
    ∀ i, admissible i → Admissibility (candidate i)
  frobeniusScore : CandidateIndex → ℝ

structure Receipt (S : Search (Left := Left) (Right := Right)) where
  selected : S.CandidateIndex
  selectedAdmissible : S.admissible selected
  minimizes :
    ∀ other, S.admissible other →
      S.frobeniusScore selected ≤ S.frobeniusScore other

def selectedOperator
    {S : Search (Left := Left) (Right := Right)}
    (R : Receipt S) :
    TensorProduct ℂ Left Right →ₗ[ℂ] TensorProduct ℂ Left Right :=
  (S.candidate R.selected).operator

def selectedCommutator
    {S : Search (Left := Left) (Right := Right)}
    (R : Receipt S) :
    TensorProduct ℂ Left Right →ₗ[ℂ] TensorProduct ℂ Left Right :=
  commutator S.interaction R.selectedOperator

theorem selected_is_minimal
    {S : Search (Left := Left) (Right := Right)}
    (R : Receipt S)
    (other : S.CandidateIndex)
    (hOther : S.admissible other) :
    S.frobeniusScore R.selected ≤ S.frobeniusScore other :=
  R.minimizes other hOther

structure Boundary where
  sourceDefinitionCreatesCPOExistence : Bool := false
  oneCPOReceiptCreatesUniqueness : Bool := false
  abstractScoreIsAlreadyFrobeniusNorm : Bool := false
  productObservableIsAutomaticallyHermitian : Bool := false
  productObservableIsAutomaticallyTraceless : Bool := false
  cpoIsAutomaticallyPhysicalPointerObservable : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem source_definition_does_not_create_cpo_existence :
    canonicalBoundary.sourceDefinitionCreatesCPOExistence = false := rfl

theorem abstract_score_not_promoted_to_frobenius_norm :
    canonicalBoundary.abstractScoreIsAlreadyFrobeniusNorm = false := rfl

end CandidatePointerObservable

def carrollSinghCPOClaim : AttributionReceipt where
  role := .externalSourceClaim
  owner := "Sean M. Carroll; Ashmeet Singh, Phys. Rev. A 103, 022213 (2021)"
  claim := "Eqs. (24)--(26): CPO is a nontrivial product observable with Hermitian traceless unit-Frobenius-norm factors minimizing the Frobenius norm of its commutator with H_int."

def dashiCPOOperatorReconstructionReceipt : AttributionReceipt where
  role := .localFormalReconstruction
  owner := "DASHI"
  claim := "Constructs the product linear operator and interaction commutator exactly; leaves Frobenius realization, admissibility, existence, uniqueness, and physical pointer-observable promotion explicit."

end QuantumMereology
