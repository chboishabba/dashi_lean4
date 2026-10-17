import Integration.TeleodynamicsExceptionalPrior
import Integration.GeometricReasoningCandidateSelection

/-!
# Teleodynamic prior arms as geometric-reasoning candidates

DASHI experiment routing only.  It does not identify the best-fitting candidate
with a true mechanism or ontology.
-/

namespace Integration.TeleodynamicsGeometricCandidateBridge

open Integration.GeometricReasoningCandidateSelection

inductive Arm
  | noPrior
  | randomMatched
  | g2Root
  | f4Root
  | e6Root
  | e7Root
  | e8Root
  | leechLike
  | learnedCodebook
  | monster3A
  | monster3B
  | monster3C
  deriving DecidableEq, Repr

def reasoningCandidate : Arm → GeometricReasoningCandidate
  | .noPrior => .unstructuredBaseline
  | .randomMatched => .genericFiniteActionGeometry
  | .g2Root => .genericFiniteActionGeometry
  | .f4Root => .genericFiniteActionGeometry
  | .e6Root => .genericFiniteActionGeometry
  | .e7Root => .genericFiniteActionGeometry
  | .e8Root => .lilaE8RootPrior
  | .leechLike => .genericFiniteActionGeometry
  | .learnedCodebook => .genericFiniteActionGeometry
  | .monster3A => .monster3ALocalGeometry
  | .monster3B => .monster3BHeisenbergGeometry
  | .monster3C => .monster3CLocalGeometry

structure Evaluation where
  arm : Arm
  reasoningReceipt : CandidateEvaluationReceipt
  currentTaskMetric : Float
  actionFitError : Float
  compositionDefect : Float
  nuisanceResponse : Float
  futureLanguageMetric : Float
  compressionLoss : Float
  accessibilityLoss : Float
  dynamicCommutationDefect : Float
  provenance : String
  deriving Repr

structure Comparison where
  left right : Evaluation
  reasoningComparison : CandidateComparisonReceipt
  matchedParameterBudget : Bool
  matchedOptimizer : Bool
  matchedDataAndSeeds : Bool
  modelHeldOut : Bool
  temporalHeldOut : Bool
  compositionHeldOut : Bool
  deriving Repr

structure Boundary where
  exceptionalFamiliesRemainDistinct : Bool
  rootAndRepresentationModesRemainDistinct : Bool
  e8HasDedicatedLilaCandidate : Bool
  monster3A3B3CRemainDistinct : Bool
  cosineSimilarityAloneClosesSelection : Bool
  lowestResidualCreatesOntology : Bool
  bestCandidateCreatesMechanism : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  exceptionalFamiliesRemainDistinct := true
  rootAndRepresentationModesRemainDistinct := true
  e8HasDedicatedLilaCandidate := true
  monster3A3B3CRemainDistinct := true
  cosineSimilarityAloneClosesSelection := false
  lowestResidualCreatesOntology := false
  bestCandidateCreatesMechanism := false

end Integration.TeleodynamicsGeometricCandidateBridge
