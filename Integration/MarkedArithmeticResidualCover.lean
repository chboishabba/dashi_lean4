import Mathlib

/-!
# Marked arithmetic residual-cover acquisition pattern

Lean mirror of the generic pattern extracted from the source-native p=11 lane.

A marked arithmetic source consists of a fine carrier projected to a coarse
arithmetic surface, an exact reopening residual, and a nontrivial automorphism
that preserves the coarse surface.  Exact reopening forces any such hidden
motion to change the residual.

This is an acquisition pattern only; it does not construct p=2/p=3 exponent-
residual arithmetic sources.
-/

namespace Integration.MarkedArithmeticResidualCover

structure SectionedProjection (Fine Coarse : Type) where
  project : Fine → Coarse
  representative : Coarse → Fine
  section : ∀ c, project (representative c) = c

structure ResidualReopening
    {Fine Coarse : Type}
    (P : SectionedProjection Fine Coarse) where
  Residual : Type
  residual : Fine → Residual
  reopen : Coarse → Residual → Fine
  reopenExact : ∀ x, reopen (P.project x) (residual x) = x

structure FibreAutomorphism
    {Fine Coarse : Type}
    (P : SectionedProjection Fine Coarse) where
  forward : Fine → Fine
  backward : Fine → Fine
  forwardPreservesSurface : ∀ x, P.project (forward x) = P.project x
  backwardPreservesSurface : ∀ x, P.project (backward x) = P.project x
  backwardAfterForward : ∀ x, backward (forward x) = x
  forwardAfterBackward : ∀ x, forward (backward x) = x

structure NontrivialFibreAutomorphism
    {Fine Coarse : Type}
    (P : SectionedProjection Fine Coarse) where
  automorphism : FibreAutomorphism P
  movedPoint : Fine
  movedPointActuallyMoves :
    automorphism.forward movedPoint ≠ movedPoint

structure MarkedArithmeticResidualCover where
  Fine : Type
  Coarse : Type
  projection : SectionedProjection Fine Coarse
  reopening : ResidualReopening projection
  hiddenSymmetry : NontrivialFibreAutomorphism projection
  arithmeticProvenance : String
  constructionReference : String

namespace MarkedArithmeticResidualCover

theorem projection_not_injective
    (C : MarkedArithmeticResidualCover) :
    ¬ Function.Injective C.projection.project := by
  intro hinj
  apply C.hiddenSymmetry.movedPointActuallyMoves
  apply hinj
  exact C.hiddenSymmetry.automorphism.forwardPreservesSurface _

theorem hidden_symmetry_changes_residual
    (C : MarkedArithmeticResidualCover) :
    C.reopening.residual
        (C.hiddenSymmetry.automorphism.forward C.hiddenSymmetry.movedPoint)
      ≠
    C.reopening.residual C.hiddenSymmetry.movedPoint := by
  intro hres
  apply C.hiddenSymmetry.movedPointActuallyMoves
  calc
    C.hiddenSymmetry.automorphism.forward C.hiddenSymmetry.movedPoint =
        C.reopening.reopen
          (C.projection.project
            (C.hiddenSymmetry.automorphism.forward C.hiddenSymmetry.movedPoint))
          (C.reopening.residual
            (C.hiddenSymmetry.automorphism.forward C.hiddenSymmetry.movedPoint)) := by
              symm
              exact C.reopening.reopenExact _
    _ =
        C.reopening.reopen
          (C.projection.project C.hiddenSymmetry.movedPoint)
          (C.reopening.residual C.hiddenSymmetry.movedPoint) := by
            rw [C.hiddenSymmetry.automorphism.forwardPreservesSurface, hres]
    _ = C.hiddenSymmetry.movedPoint :=
      C.reopening.reopenExact _

end MarkedArithmeticResidualCover

inductive ExceptionalResidualPrime
  | p2
  | p3
  deriving DecidableEq, Repr

structure MarkedResidualSourceCandidate (p : ExceptionalResidualPrime) where
  cover : MarkedArithmeticResidualCover
  coarseSurfaceHasArithmeticMeaning : Prop
  coarseSurfaceArithmeticReference : String
  hiddenSymmetryHasArithmeticMeaning : Prop
  hiddenSymmetryArithmeticReference : String

structure ExistingPatternReceipt where
  sourceOwner : String
  coarseArithmeticClassFixed : Bool
  markedStateMoves : Bool
  exactReopeningResidualMoves : Bool
  patternPromotedToP2P3Source : Bool
  deriving Repr

def p11PatternReceipt : ExistingPatternReceipt where
  sourceOwner := "DASHI.Moonshine.P11MarkedFrobeniusResidualReceiptExact"
  coarseArithmeticClassFixed := true
  markedStateMoves := true
  exactReopeningResidualMoves := true
  patternPromotedToP2P3Source := false

structure Boundary where
  genericMarkedCoverPatternOwned : Bool
  exactReopeningRequired : Bool
  nontrivialFibreSymmetryRequired : Bool
  hiddenSymmetryForcesResidualMotion : Bool
  coarseProjectionProvablyLossyUnderHiddenMotion : Bool
  p11PatternRecordedAsExistingInstance : Bool
  p11PatternPromotedToP2P3ArithmeticSource : Bool
  p2CandidateInhabitedHere : Bool
  p3CandidateInhabitedHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  genericMarkedCoverPatternOwned := true
  exactReopeningRequired := true
  nontrivialFibreSymmetryRequired := true
  hiddenSymmetryForcesResidualMotion := true
  coarseProjectionProvablyLossyUnderHiddenMotion := true
  p11PatternRecordedAsExistingInstance := true
  p11PatternPromotedToP2P3ArithmeticSource := false
  p2CandidateInhabitedHere := false
  p3CandidateInhabitedHere := false

end Integration.MarkedArithmeticResidualCover
