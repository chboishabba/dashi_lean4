import RequestProject.QuantumMereologyDensityEvolution
import RequestProject.QuantumMereologyPointerProbability
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Entropy acceleration on a finite unitary path

This pays the calculus shape required by Carroll--Singh's source objective.

Given a time-indexed unitary matrix U(t) and an initial bipartite density matrix,
we construct

  rho_AB(t) = U(t) rho_AB(0) U(t)ᴴ,
  rho_A(t)  = Tr_B rho_AB(t),

then the concrete linear-entropy and pointer-entropy paths. A second derivative
receipt is an actual pair of derivative proofs, not an arbitrary numeric label.

This module does not yet derive U(t) = exp(-iHt) from a Hamiltonian, nor compute
the derivatives symbolically from H. Those are the remaining analytic leaves.
-/

namespace QuantumMereology

namespace EntropyAcceleration

variable
  {A B J : Type*}
  [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]
  [Fintype J]

structure UnitaryPath where
  U : ℝ → Matrix (A × B) (A × B) ℂ
  unitary :
    ∀ t, U t ∈ Matrix.unitaryGroup (A × B) ℂ

def globalDensityAt
    (path : UnitaryPath (A := A) (B := B))
    (rho0 : ReducedState.DensityMatrix (A × B))
    (t : ℝ) :
    ReducedState.DensityMatrix (A × B) :=
  DensityEvolution.evolveDensity
    (path.U t)
    (path.unitary t)
    rho0

def reducedDensityAt
    (path : UnitaryPath (A := A) (B := B))
    (rho0 : ReducedState.DensityMatrix (A × B))
    (t : ℝ) :
    ReducedState.DensityMatrix A :=
  ReducedState.partialTraceDensityRight
    (globalDensityAt path rho0 t)

def linearEntropyPath
    (path : UnitaryPath (A := A) (B := B))
    (rho0 : ReducedState.DensityMatrix (A × B)) :
    ℝ → ℝ :=
  fun t =>
    ReducedState.linearEntropy
      (reducedDensityAt path rho0 t)

def pointerEntropyPath
    (path : UnitaryPath (A := A) (B := B))
    (rho0 : ReducedState.DensityMatrix (A × B))
    (projectors :
      PointerProbability.ProjectorFamily (I := A) (J := J)) :
    ℝ → ℝ :=
  fun t =>
    PointerProbability.pointerEntropy
      (reducedDensityAt path rho0 t)
      projectors

/-- Exact second-derivative receipt at a point. The intermediary first-
derivative function is explicit, so no informal double-prime notation is used
as theorem authority. -/
structure SecondDerivativeAt
    (f : ℝ → ℝ)
    (t0 : ℝ)
    (acceleration : ℝ) : Prop where
  firstDerivative : ℝ → ℝ
  firstDerivativeCorrect :
    ∀ t, HasDerivAt f (firstDerivative t) t
  secondDerivativeCorrect :
    HasDerivAt firstDerivative acceleration t0

theorem secondDerivativeAt_hasDerivAt
    {f : ℝ → ℝ}
    {t0 acceleration : ℝ}
    (h : SecondDerivativeAt f t0 acceleration) :
    HasDerivAt h.firstDerivative acceleration t0 :=
  h.secondDerivativeCorrect

/-- Source-ready pair of t=0 entropy accelerations for one pointer-projector
family and one initial bipartite density matrix. -/
structure Receipt
    (path : UnitaryPath (A := A) (B := B))
    (rho0 : ReducedState.DensityMatrix (A × B))
    (projectors :
      PointerProbability.ProjectorFamily (I := A) (J := J)) where
  linearAcceleration : ℝ
  pointerAcceleration : ℝ

  linearSecondDerivative :
    SecondDerivativeAt
      (linearEntropyPath path rho0)
      0
      linearAcceleration

  pointerSecondDerivative :
    SecondDerivativeAt
      (pointerEntropyPath path rho0 projectors)
      0
      pointerAcceleration

def schwingerPenalty
    {path : UnitaryPath (A := A) (B := B)}
    {rho0 : ReducedState.DensityMatrix (A × B)}
    {projectors :
      PointerProbability.ProjectorFamily (I := A) (J := J)}
    (R : Receipt path rho0 projectors) : ℝ :=
  SchwingerObjective.penalty
    R.linearAcceleration
    R.pointerAcceleration

theorem schwingerPenalty_eq_source_max
    {path : UnitaryPath (A := A) (B := B)}
    {rho0 : ReducedState.DensityMatrix (A × B)}
    {projectors :
      PointerProbability.ProjectorFamily (I := A) (J := J)}
    (R : Receipt path rho0 projectors) :
    schwingerPenalty R =
      max R.linearAcceleration R.pointerAcceleration :=
  rfl

structure Boundary where
  unitaryPathCreatesSchrodingerGenerator : Bool := false
  secondDerivativeReceiptComputesAccelerationFromHamiltonian : Bool := false
  projectorFamilyCreatesCPOEigenbasis : Bool := false
  entropyAccelerationCreatesPreferredTPS : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem derivative_receipt_not_hamiltonian_derivation :
    canonicalBoundary.secondDerivativeReceiptComputesAccelerationFromHamiltonian = false := rfl

theorem unitary_path_not_schrodinger_generator :
    canonicalBoundary.unitaryPathCreatesSchrodingerGenerator = false := rfl

end EntropyAcceleration

def carrollSinghEntropyAccelerationClaim : AttributionReceipt where
  role := .externalSourceClaim
  owner := "Sean M. Carroll; Ashmeet Singh, Phys. Rev. A 103, 022213 (2021)"
  claim := "The preferred-factorisation objective uses the second time derivatives at t=0 of linear entropy and pointer entropy for candidate-pointer initial states."

def mathlibDerivativeSource : AttributionReceipt where
  role := .importedFormalTheoremSource
  owner := "mathlib v4.28.0, HasDerivAt"
  claim := "Supplies the real derivative proof objects used to represent first and second derivatives of the finite entropy paths."

def dashiEntropyAccelerationReconstructionReceipt : AttributionReceipt where
  role := .localFormalReconstruction
  owner := "DASHI"
  claim := "Constructs time-indexed global/reduced density matrices and entropy paths from a supplied unitary path, and requires actual HasDerivAt proofs for both source-required t=0 accelerations."

end QuantumMereology
