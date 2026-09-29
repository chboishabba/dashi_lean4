import RequestProject.QuantumMereologyCandidatePointerObservable
import RequestProject.QuantumMereologySchwingerObjective
import RequestProject.QuantumMereologyOperatorLocality
import RequestProject.QuantumMereologyEntropyAcceleration

/-!
# Same-TPS CPO -> Schwinger producer compiler

This is a DASHI cross-module theorem. External source authority remains with
Carroll--Singh for the algorithmic scientific claims; DASHI owns only the
same-object wiring.

For every candidate factorisation, the CPO search must consume exactly the
interaction term V from that candidate's own operator-locality decomposition.
Only after a CPO minimizer and entropy-acceleration authorities are supplied
does the compiler expose source-shaped Schwinger SearchData.
-/

namespace QuantumMereology

open scoped TensorProduct

namespace SchwingerProducer

variable
  {H Left Right PointerInit : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Left] [InnerProductSpace ℂ Left]
  [NormedAddCommGroup Right] [InnerProductSpace ℂ Right]
  [Fintype PointerInit] [Nonempty PointerInit]

/-- The exact producer payload for one factorisation and one candidate-pointer
initial state. This generic interface predates the concrete finite matrix
producer. It remains useful for non-matrix consumers, but finite quantum
instances should prefer the derivative-backed ReducedState / DensityEvolution /
EntropyAcceleration lane rather than treating these fields as primary authority. -/
structure AccelerationAuthority where
  linearEntropyAcceleration : ℝ
  pointerEntropyAcceleration : ℝ
  ReducedStateAuthority : Prop
  reducedStateAuthority : ReducedStateAuthority
  LinearEntropySecondDerivativeAuthority : Prop
  linearEntropySecondDerivativeAuthority :
    LinearEntropySecondDerivativeAuthority
  PointerProbabilityAuthority : Prop
  pointerProbabilityAuthority : PointerProbabilityAuthority
  PointerEntropySecondDerivativeAuthority : Prop
  pointerEntropySecondDerivativeAuthority :
    PointerEntropySecondDerivativeAuthority

namespace AccelerationAuthority

variable
  {A B J : Type*}
  [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]
  [Fintype J]

/-- Finite matrix instances enter the generic compiler only through an actual
derivative-backed entropy-acceleration receipt. The generic authority fields are
instantiated by concrete theorem statements, not by True placeholders. -/
def ofConcreteReceipt
    {path : EntropyAcceleration.UnitaryPath (A := A) (B := B)}
    {rho0 : ReducedState.DensityMatrix (A × B)}
    {projectors :
      PointerProbability.ProjectorFamily (I := A) (J := J)}
    (R : EntropyAcceleration.Receipt path rho0 projectors) :
    AccelerationAuthority where
  linearEntropyAcceleration := R.linearAcceleration
  pointerEntropyAcceleration := R.pointerAcceleration
  ReducedStateAuthority :=
    ReducedState.partialTraceDensityRight
      (EntropyAcceleration.globalDensityAt path rho0 0)
      =
    EntropyAcceleration.reducedDensityAt path rho0 0
  reducedStateAuthority := rfl
  LinearEntropySecondDerivativeAuthority :=
    EntropyAcceleration.SecondDerivativeAt
      (EntropyAcceleration.linearEntropyPath path rho0)
      0
      R.linearAcceleration
  linearEntropySecondDerivativeAuthority :=
    R.linearSecondDerivative
  PointerProbabilityAuthority :=
    EntropyAcceleration.pointerEntropyPath path rho0 projectors
      =
    (fun t =>
      PointerProbability.pointerEntropy
        (EntropyAcceleration.reducedDensityAt path rho0 t)
        projectors)
  pointerProbabilityAuthority := rfl
  PointerEntropySecondDerivativeAuthority :=
    EntropyAcceleration.SecondDerivativeAt
      (EntropyAcceleration.pointerEntropyPath path rho0 projectors)
      0
      R.pointerAcceleration
  pointerEntropySecondDerivativeAuthority :=
    R.pointerSecondDerivative

end AccelerationAuthority

/-- Canonical bare world used by the finite linear/operator producer. -/
def linearWorld (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    BareQuantumWorld where
  State := H
  Hamiltonian := H →ₗ[ℂ] H
  evolve := fun A state => A state

/-- Complete same-object source producer for a fixed ambient operator and a
family of candidate TPSs of the same factor dimensions. The abstract
quantum-mereology TPS and the concrete inner-product tensor reconstruction are
kept separate and joined only by an explicit application-supplied weld. -/
structure Pipeline where
  CandidateIndex : Type
  tps : CandidateIndex → BipartiteInnerProductTPS H Left Right
  abstractTPS :
    CandidateIndex → TensorProductStructure (linearWorld H)

  AbstractConcreteTPSWeld : CandidateIndex → Prop
  abstractConcreteTPSWeld :
    ∀ candidate, AbstractConcreteTPSWeld candidate

  admissible : CandidateIndex → Prop

  globalOperator : H →ₗ[ℂ] H

  locality :
    ∀ candidate,
      OperatorLocality.Witness (tps candidate) globalOperator

  cpoSearch :
    ∀ candidate,
      CandidatePointerObservable.Search (Left := Left) (Right := Right)

  cpoSearchUsesSameInteraction :
    ∀ candidate,
      (cpoSearch candidate).interaction =
        (locality candidate).interaction

  cpoReceipt :
    ∀ candidate,
      admissible candidate →
      CandidatePointerObservable.Receipt (cpoSearch candidate)

  acceleration :
    CandidateIndex → PointerInit → AccelerationAuthority

namespace Pipeline

noncomputable def schwingerSearchData
    (P : Pipeline
      (H := H) (Left := Left) (Right := Right)
      (PointerInit := PointerInit)) :
    SchwingerObjective.SearchData (linearWorld H) PointerInit where
  Candidate := P.CandidateIndex
  realizes := P.abstractTPS
  Admissible := P.admissible
  accelerations :=
    { linearEntropyAcceleration :=
        fun candidate pointer =>
          (P.acceleration candidate pointer).linearEntropyAcceleration
      pointerEntropyAcceleration :=
        fun candidate pointer =>
          (P.acceleration candidate pointer).pointerEntropyAcceleration }

/-!
The generic TensorProductStructure carrier does not itself retain the concrete
LinearIsometryEquiv reconstruction. The two views are therefore joined only by
P.abstractConcreteTPSWeld, whose semantics remain an application obligation.
-/

/-- Compile an already-selected Schwinger minimizer through the source-exact
score layer. -/
theorem selectedMinimizesCompiledSchwingerScore
    (P : Pipeline
      (H := H) (Left := Left) (Right := Right)
      (PointerInit := PointerInit))
    (receipt :
      PreferredTPSSelectionReceipt
        P.schwingerSearchData.selectionProblem)
    (other : P.CandidateIndex)
    (hOther : P.admissible other) :
    P.schwingerSearchData.score receipt.selected ≤
      P.schwingerSearchData.score other :=
  SchwingerObjective.SearchData.selected_minimizes_schwinger_score
    P.schwingerSearchData receipt other hOther

/-- Same-object interaction equality can be read directly at the selected
factorisation. -/
theorem cpoInteractionIsSelectedLocalityInteraction
    (P : Pipeline
      (H := H) (Left := Left) (Right := Right)
      (PointerInit := PointerInit))
    (candidate : P.CandidateIndex) :
    (P.cpoSearch candidate).interaction =
      (P.locality candidate).interaction :=
  P.cpoSearchUsesSameInteraction candidate

end Pipeline

structure Boundary where
  sameInteractionWeldCreatesCPOReceipt : Bool := false
  cpoReceiptCreatesEntropyAccelerations : Bool := false
  genericAccelerationSocketIsFiniteReducedStateProof : Bool := false
  compiledSearchCreatesMinimizerExistence : Bool := false
  compiledSearchCreatesPreferredTPSUniqueness : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem same_interaction_weld_does_not_create_cpo_minimizer :
    canonicalBoundary.sameInteractionWeldCreatesCPOReceipt = false := rfl

theorem generic_acceleration_socket_is_not_finite_reduced_state_proof :
    canonicalBoundary.genericAccelerationSocketIsFiniteReducedStateProof = false := rfl

end SchwingerProducer

def dashiSameTPSProducerCompilerReceipt : AttributionReceipt where
  role := .crossModuleInference
  owner := "DASHI"
  claim := "Welds each candidate TPS operator-locality interaction to that candidate's CPO search and compiles explicit acceleration authorities into the source-shaped Schwinger score; no external source is credited with the same-object compiler."

end QuantumMereology
