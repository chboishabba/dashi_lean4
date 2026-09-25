import Mathlib

/-!
# Nongin 1.1-army refinement

Repository-owned formalisation of the user-supplied historical nongin metaphor:

  1.0 carrier X
  1.1 carrier X × F

The richer carrier forgets to X, but a nontrivial frame coordinate can preserve
distinctions unavailable to the 1.0 projection.  No literal ten-percent
performance law or universal superiority claim is made.
-/

namespace Integration.NonginOnePointOneArmyRefinement

abbrev OnePointOneCarrier (Base Frame : Type) := Base × Frame

def onePointZeroProject {Base Frame : Type} :
    OnePointOneCarrier Base Frame → Base := Prod.fst

def onePointOneProject {Base Frame : Type} :
    OnePointOneCarrier Base Frame → OnePointOneCarrier Base Frame := id

structure NontrivialFrame (Frame : Type) where
  firstFrame : Frame
  secondFrame : Frame
  framesDistinct : firstFrame ≠ secondFrame

theorem same_base_distinct_frames_collide_at_one_point_zero
    {Base Frame : Type}
    (base : Base)
    (w : NontrivialFrame Frame) :
    onePointZeroProject (base, w.firstFrame) =
      onePointZeroProject (base, w.secondFrame) := rfl

theorem one_point_zero_not_injective
    {Base Frame : Type}
    (base : Base)
    (w : NontrivialFrame Frame) :
    ¬ Function.Injective
      (onePointZeroProject :
        OnePointOneCarrier Base Frame → Base) := by
  intro h
  have pairEq : (base, w.firstFrame) = (base, w.secondFrame) :=
    h rfl
  exact w.framesDistinct (congrArg Prod.snd pairEq)

structure FrameSensitiveConsumer
    {Base Frame Output : Type}
    (consume : OnePointOneCarrier Base Frame → Output) where
  baseWitness : Base
  frameWitness : NontrivialFrame Frame
  consumerSeparatesFrames :
    consume (baseWitness, frameWitness.firstFrame) ≠
      consume (baseWitness, frameWitness.secondFrame)

theorem no_consumer_factorization_through_one_point_zero
    {Base Frame Output : Type}
    {consume : OnePointOneCarrier Base Frame → Output}
    (s : FrameSensitiveConsumer consume) :
    ¬ ∃ coarseConsume : Base → Output,
      ∀ state, consume state = coarseConsume (onePointZeroProject state) := by
  rintro ⟨coarseConsume, h⟩
  have left := h (s.baseWitness, s.frameWitness.firstFrame)
  have right := h (s.baseWitness, s.frameWitness.secondFrame)
  exact s.consumerSeparatesFrames (left.trans right.symm)

inductive Base1 | sharedSituation
  deriving DecidableEq, Repr

inductive Frame2 | immersed | frameAware
  deriving DecidableEq, Repr

def canonicalFrameWitness : NontrivialFrame Frame2 where
  firstFrame := .immersed
  secondFrame := .frameAware
  framesDistinct := by decide

inductive Response2 | lowerFrameResponse | frameBearingResponse
  deriving DecidableEq, Repr

def frameSensitiveResponse : OnePointOneCarrier Base1 Frame2 → Response2
  | (.sharedSituation, .immersed) => .lowerFrameResponse
  | (.sharedSituation, .frameAware) => .frameBearingResponse

def canonicalFrameSensitiveConsumer :
    FrameSensitiveConsumer frameSensitiveResponse where
  baseWitness := .sharedSituation
  frameWitness := canonicalFrameWitness
  consumerSeparatesFrames := by decide

structure NonginOnePointOneArmyBoundary where
  nonginGenealogyRetained : Bool
  onePointOneFactorsToOnePointZero : Bool
  nontrivialFrameCanSplitOldFibre : Bool
  usefulnessRequiresFrameSensitiveConsumer : Bool
  literalTenPercentPerformanceLawClaimed : Bool
  onePointOneAgentsUniversallySuperiorClaimed : Bool
  deriving Repr

def canonicalBoundary : NonginOnePointOneArmyBoundary where
  nonginGenealogyRetained := true
  onePointOneFactorsToOnePointZero := true
  nontrivialFrameCanSplitOldFibre := true
  usefulnessRequiresFrameSensitiveConsumer := true
  literalTenPercentPerformanceLawClaimed := false
  onePointOneAgentsUniversallySuperiorClaimed := false

end Integration.NonginOnePointOneArmyRefinement
