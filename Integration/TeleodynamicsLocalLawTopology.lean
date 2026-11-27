import Mathlib

/-!
# Teleodynamic local-law / coupling-topology factorisation

Productive cross-pollination from Agda IIT/phi PR #1148.  That sibling keeps a
fixed recurrent gluing topology while varying the local synthesis law and
reports different finite system-phi behaviour.  This Lean owner imports no Agda
theorem authority; it pays the generic structural fact needed by the local
teleodynamics/model lane itself:

    coupling topology != local state-update law != resulting future.

Therefore a topology or architecture-similarity coordinate cannot determine a
local transition rule or future trace by definition.
-/

namespace Integration.TeleodynamicsLocalLawTopology

structure BoolTriple where
  a b c : Bool
  deriving DecidableEq, Repr

def xorB : Bool → Bool → Bool
  | false, false => false
  | false, true  => true
  | true,  false => true
  | true,  true  => false

def orB : Bool → Bool → Bool
  | false, false => false
  | false, true  => true
  | true,  false => true
  | true,  true  => true

/-- Fixed recurrent wiring `A'=C`, `B'=A`, `C'=mu(A,B)`.  Only the local law
`mu` varies. -/
def recurrentStep (μ : Bool → Bool → Bool) (s : BoolTriple) : BoolTriple :=
  ⟨s.c, s.a, μ s.a s.b⟩

def counterexampleState : BoolTriple := ⟨true, true, false⟩

/-- Same recurrent topology, different local synthesis law, different future. -/
theorem xorOrCounterexample :
    recurrentStep xorB counterexampleState ≠
      recurrentStep orB counterexampleState := by
  intro h
  have hc := congrArg BoolTriple.c h
  simp [recurrentStep, counterexampleState, xorB, orB] at hc

structure Factorisation where
  stateCarrierLabel : String
  couplingTopologyLabel : String
  localUpdateLawLabel : String
  interventionLabel : String
  observerOrConsumerLabel : String
  resultingFutureTraceLabel : String
  topologyReceipt : String
  localLawReceipt : String
  transitionReceipt : String
  deriving Repr

def canonicalFactorisation : Factorisation where
  stateCarrierLabel := "declared learner/system state"
  couplingTopologyLabel := "declared directed coupling/gluing graph"
  localUpdateLawLabel := "declared local state-update/synthesis law"
  interventionLabel := "declared intervention/query action"
  observerOrConsumerLabel := "declared decoder or future consumer"
  resultingFutureTraceLabel := "held-out transition trace"
  topologyReceipt := "topology fixed independently of local law"
  localLawReceipt := "local law fixed independently of topology"
  transitionReceipt := "transition evaluated from both topology and local law"

structure MatchedGateSiblingReceipt where
  sourcePR : Nat
  fixedRecurrentFabricReported : Bool
  localGateVariedReported : Bool
  xorOrAndComparedReported : Bool
  ternaryTriXorComparedReported : Bool
  systemPhiChangesUnderFixedTopologyReported : Bool
  importedAsLocalLeanTheorem : Bool
  deriving Repr

def canonicalMatchedGateSiblingReceipt : MatchedGateSiblingReceipt where
  sourcePR := 1148
  fixedRecurrentFabricReported := true
  localGateVariedReported := true
  xorOrAndComparedReported := true
  ternaryTriXorComparedReported := true
  systemPhiChangesUnderFixedTopologyReported := true
  importedAsLocalLeanTheorem := false

structure Boundary where
  sameTopologyDifferentLocalLawCanChangeFuture : Bool
  topologyDeterminesLocalTransitionByDefinition : Bool
  localLawDeterminesCouplingTopologyByDefinition : Bool
  sameArchitectureSimilarityDeterminesLocalLaw : Bool
  sameArchitectureSimilarityDeterminesFutureTrace : Bool
  topologyAndLocalLawMustBeDeclaredSeparately : Bool
  observerConsumerMustBeDeclaredSeparately : Bool
  iitMatchedGateScanReportedInSibling : Bool
  siblingReceiptCreatesLocalIITTheorem : Bool
  localLawTopologyFactorisationCreatesPhenomenalIdentity : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  sameTopologyDifferentLocalLawCanChangeFuture := true
  topologyDeterminesLocalTransitionByDefinition := false
  localLawDeterminesCouplingTopologyByDefinition := false
  sameArchitectureSimilarityDeterminesLocalLaw := false
  sameArchitectureSimilarityDeterminesFutureTrace := false
  topologyAndLocalLawMustBeDeclaredSeparately := true
  observerConsumerMustBeDeclaredSeparately := true
  iitMatchedGateScanReportedInSibling := true
  siblingReceiptCreatesLocalIITTheorem := false
  localLawTopologyFactorisationCreatesPhenomenalIdentity := false

structure MatchedExperiment where
  sameStateSet : Bool
  sameCouplingTopology : Bool
  sameParameterBudget : Bool
  sameInterventionFamily : Bool
  sameDeclaredConsumer : Bool
  varyOnlyLocalLaw : Bool
  reportTransitionDifference : Bool
  reportConsumerDifference : Bool
  optionallyReportIITDifference : Bool
  architectureScalarAloneCountsAsExplanation : Bool
  deriving Repr

def canonicalMatchedExperiment : MatchedExperiment where
  sameStateSet := true
  sameCouplingTopology := true
  sameParameterBudget := true
  sameInterventionFamily := true
  sameDeclaredConsumer := true
  varyOnlyLocalLaw := true
  reportTransitionDifference := true
  reportConsumerDifference := true
  optionallyReportIITDifference := true
  architectureScalarAloneCountsAsExplanation := false

end Integration.TeleodynamicsLocalLawTopology
