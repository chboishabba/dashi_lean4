import RequestProject.QuantumMereologyReducedState
import RequestProject.QuantumMereologySchwingerObjective
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Finite pointer probability and pointer entropy

Carroll--Singh Eq. (22) uses

  p_j(t) = Tr(rho_A(t) O_j)

for rank-one projectors O_j onto eigenstates of the candidate pointer
observable, followed by Eq. (21)

  S_pointer = 1 - sum_j p_j^2.

This module formalises that finite matrix readout. It does not construct the CPO
eigenbasis, prove Born-probability nonnegativity/normalisation, or create time
derivatives.
-/

namespace QuantumMereology

open scoped BigOperators

namespace PointerProbability

variable
  {I J : Type*}
  [Fintype I] [DecidableEq I]
  [Fintype J]

/-- A finite pointer-projector family. Projector algebra is kept as explicit
authority because the current CPO module does not yet construct an eigenbasis. -/
structure ProjectorFamily where
  projector : J → Matrix I I ℂ
  hermitian : ∀ j, (projector j).IsHermitian
  idempotent : ∀ j, projector j * projector j = projector j
  OrthogonalAuthority : Prop
  orthogonalAuthority : OrthogonalAuthority
  CompletenessAuthority : Prop
  completenessAuthority : CompletenessAuthority

/-- Eq. (22), taking the real part at the finite matrix boundary. -/
def probability
    (rho : ReducedState.DensityMatrix I)
    (P : ProjectorFamily (I := I) (J := J))
    (j : J) : ℝ :=
  Complex.re (Matrix.trace (rho.matrix * P.projector j))

/-- Eq. (21) on the projector-induced probability family. -/
def pointerEntropy
    (rho : ReducedState.DensityMatrix I)
    (P : ProjectorFamily (I := I) (J := J)) : ℝ :=
  SchwingerObjective.pointerEntropy (fun j => probability rho P j)

theorem pointerEntropy_eq_source_formula
    (rho : ReducedState.DensityMatrix I)
    (P : ProjectorFamily (I := I) (J := J)) :
    pointerEntropy rho P =
      1 - ∑ j : J, (probability rho P j) ^ 2 :=
  rfl

structure ProbabilityAuthority
    (rho : ReducedState.DensityMatrix I)
    (P : ProjectorFamily (I := I) (J := J)) : Prop where
  nonnegative : ∀ j, 0 ≤ probability rho P j
  normalized : ∑ j : J, probability rho P j = 1

structure Boundary where
  projectorNamesCreateCPOEigenbasis : Bool := false
  traceReadoutAutomaticallyProvesProbabilityAxioms : Bool := false
  probabilityFormulaCreatesTimeDerivative : Bool := false
  pointerEntropyCreatesPredictabilityTheorem : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem projector_family_not_promoted_to_cpo_eigenbasis :
    canonicalBoundary.projectorNamesCreateCPOEigenbasis = false := rfl

theorem probability_axioms_remain_separate :
    canonicalBoundary.traceReadoutAutomaticallyProvesProbabilityAxioms = false := rfl

end PointerProbability

def carrollSinghPointerProbabilityClaim : AttributionReceipt where
  role := .externalSourceClaim
  owner := "Sean M. Carroll; Ashmeet Singh, Phys. Rev. A 103, 022213 (2021)"
  claim := "Eqs. (21)--(22): p_j(t)=Tr_A(rho_A(t) O_j) for pointer-basis projectors and S_pointer(t)=1-sum_j p_j(t)^2."

def dashiPointerProbabilityReconstructionReceipt : AttributionReceipt where
  role := .localFormalReconstruction
  owner := "DASHI"
  claim := "Reconstructs the finite matrix trace readout and pointer entropy while keeping CPO eigenbasis, probability axioms, time evolution and derivative authority explicit."

end QuantumMereology
