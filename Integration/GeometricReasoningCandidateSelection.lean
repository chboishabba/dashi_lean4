import Mathlib

/-!
# Geometric reasoning candidate selection

E8, Monster 3A/3B/3C and an unstructured baseline are treated as competing
candidate geometries.  Fit and compression are experiment receipts, not ontology.
The action-compression quality surface below is a DASHI proposal, not an external
source definition.
-/

namespace Integration.GeometricReasoningCandidateSelection

universe u v w

inductive GeometricReasoningCandidate
  | unstructuredBaseline
  | lilaE8RootPrior
  | monster3ALocalGeometry
  | monster3BHeisenbergGeometry
  | monster3CLocalGeometry
  | genericFiniteActionGeometry
  deriving DecidableEq, Repr

def candidateName : GeometricReasoningCandidate → String
  | .unstructuredBaseline => "unstructured-baseline"
  | .lilaE8RootPrior => "lila-e8-root-prior"
  | .monster3ALocalGeometry => "monster-3a-local"
  | .monster3BHeisenbergGeometry => "monster-3b-heisenberg"
  | .monster3CLocalGeometry => "monster-3c-local"
  | .genericFiniteActionGeometry => "generic-finite-action"

structure ActionCandidate (G : Type u) (Z : Type v) where
  identity : G
  compose : G → G → G
  act : G → Z → Z
  identityLaw : ∀ z, act identity z = z
  compositionLaw : ∀ g h z, act (compose g h) z = act g (act h z)
  constructionJustification : String

structure InterventionActionFit
    {I : Type u} {G : Type v} {X : Type w} {Z : Type*}
    (candidate : ActionCandidate G Z)
    (encode : X → Z)
    (intervene : I → X → X) where
  labelAction : I → G
  fits : ∀ i x, encode (intervene i x) = candidate.act (labelAction i) (encode x)
  fitJustification : String

structure CompositionReceipt (I : Type u) (G : Type v) where
  composeIntervention : I → I → I
  composeAction : G → G → G
  fittedAction : I → G
  compositionAgrees : ∀ i j,
    fittedAction (composeIntervention i j) = composeAction (fittedAction i) (fittedAction j)
  provenance : String

structure NuisanceInvarianceReceipt (N : Type u) (X : Type v) (Z : Type w) where
  encode : X → Z
  nuisance : N → X → X
  invariant : ∀ n x, encode (nuisance n x) = encode x
  provenance : String

structure GeometricReasoningLayerTrace where
  layer : Nat
  interventionId : String
  candidate : GeometricReasoningCandidate
  pairAccuracy : Float
  displacementAlignment : Float
  rootEntropyOrOccupancy : Float
  quantizationError : Float
  actionFitError : Float
  compositionDefect : Float
  cocycleDefect : Float
  nuisanceResponse : Float
  dashiDeltaAdmissibility : Bool
  traceProvenance : String
  deriving Repr

/-- DASHI-proposed action-compression quality surface.  Concrete numerical
instantiations choose a score algebra and evidence protocol. -/
structure ActionCompressionQualityDefinition (Score : Type u) where
  semanticInformation : Score
  compositionFidelity : Score
  actionComplexity : Score
  residualComplexity : Score
  combine : Score → Score → Score
  penalize : Score → Score → Score
  quality : Score
  qualityDefinition :
    quality = penalize (combine semanticInformation compositionFidelity)
      (combine actionComplexity residualComplexity)
  proposedByDASHINotAttributedToExternalSource : Bool
  proposalFlagIsTrue : proposedByDASHINotAttributedToExternalSource = true

structure CandidateEvaluationReceipt where
  candidate : GeometricReasoningCandidate
  fitScore : Float
  compositionScore : Float
  nuisanceScore : Float
  residualCost : Float
  datasetOrPairSet : String
  evaluationProtocol : String
  heldOut : Bool
  deriving Repr

structure CandidateComparisonReceipt where
  left : CandidateEvaluationReceipt
  right : CandidateEvaluationReceipt
  comparisonResult : Ordering
  provenance : String
  deriving Repr

inductive FitSelectsMechanismPermission : Prop
inductive LowestResidualImpliesTrueOntologyPermission : Prop
inductive TernaryCarrierImpliesMonsterClassPermission : Prop

theorem fitCannotAutoSelectMechanism : ¬ FitSelectsMechanismPermission := by
  intro h; cases h

theorem residualCannotAutoCreateOntology : ¬ LowestResidualImpliesTrueOntologyPermission := by
  intro h; cases h

theorem ternaryCannotAutoSelectMonsterClass : ¬ TernaryCarrierImpliesMonsterClassPermission := by
  intro h; cases h

def successfulFitAutomaticallySelectsMechanism : Bool := false

structure Boundary where
  baselineCandidateTyped : Bool
  e8CandidateTyped : Bool
  monster3A3B3CDistinct : Bool
  genericActionLawTyped : Bool
  compositionDiagnosticTyped : Bool
  nuisanceInvarianceTyped : Bool
  layerTraceTyped : Bool
  actionCompressionQualityMarkedAsDASHIProposal : Bool
  successfulFitCreatesMechanism : Bool
  lowResidualCreatesOntology : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  baselineCandidateTyped := true
  e8CandidateTyped := true
  monster3A3B3CDistinct := true
  genericActionLawTyped := true
  compositionDiagnosticTyped := true
  nuisanceInvarianceTyped := true
  layerTraceTyped := true
  actionCompressionQualityMarkedAsDASHIProposal := true
  successfulFitCreatesMechanism := false
  lowResidualCreatesOntology := false

end Integration.GeometricReasoningCandidateSelection
