import RequestProject.QuantumMereologyCandidatePointerObservable
import RequestProject.QuantumMereologySchwingerObjective
import RequestProject.QuantumMereologyOperatorLocality

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
initial state. Formula correctness is carried explicitly because the current
repo still lacks a reduced-density-matrix / partial-trace derivative stack. -/
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

/-- Complete same-object source producer for a fixed ambient operator and a
family of candidate TPSs of the same factor dimensions. -/
structure Pipeline where
  CandidateIndex : Type
  tps : CandidateIndex → BipartiteInnerProductTPS H Left Right
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
    SchwingerObjective.SearchData
      { State := H
        Hamiltonian := H →ₗ[ℂ] H
        evolve := fun A state => A state }
      PointerInit where
  Candidate := P.CandidateIndex
  realizes := fun candidate =>
    { Subsystem := Sum Left Right
      FactorIndex := Bool
      subsystemAt := fun
        | false => Sum.inl (0 : Left)
        | true => Sum.inr (0 : Right)
      partOfCarrier := fun _ => True
      reconstructsCarrier := True
      reconstruction := trivial
      Entangled := fun _ _ _ => Prop
      Interacts := fun _ _ _ => Prop }
  Admissible := P.admissible
  accelerations :=
    { linearEntropyAcceleration :=
        fun candidate pointer =>
          (P.acceleration candidate pointer).linearEntropyAcceleration
      pointerEntropyAcceleration :=
        fun candidate pointer =>
          (P.acceleration candidate pointer).pointerEntropyAcceleration }

/-!
The generic TensorProductStructure carrier does not yet retain the concrete
LinearIsometryEquiv reconstruction, so the realizes field above is only the
existing abstract subsystem interface. Same-object linkage to the concrete TPS
is retained separately by P.tps. This is intentionally not a claim that the
abstract subsystemAt encoding reconstructs the Hilbert tensor product.
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
  accelerationAuthorityCreatesReducedStateTheory : Bool := false
  compiledSearchCreatesMinimizerExistence : Bool := false
  compiledSearchCreatesPreferredTPSUniqueness : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem same_interaction_weld_does_not_create_cpo_minimizer :
    canonicalBoundary.sameInteractionWeldCreatesCPOReceipt = false := rfl

theorem acceleration_socket_does_not_create_reduced_state_theory :
    canonicalBoundary.accelerationAuthorityCreatesReducedStateTheory = false := rfl

end SchwingerProducer

def dashiSameTPSProducerCompilerReceipt : AttributionReceipt where
  role := .crossModuleInference
  owner := "DASHI"
  claim := "Welds each candidate TPS operator-locality interaction to that candidate's CPO search and compiles explicit acceleration authorities into the source-shaped Schwinger score; no external source is credited with the same-object compiler."

end QuantumMereology
