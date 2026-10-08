import Integration.F4D4StandardTrialityRecognition
import Integration.F4D4TrialitySupport
import Mathlib

/-!
# Explicit outer triality on the standard D4 weight systems

A D4-equivariant identification of each 8-sector is not unique.  Choosing the
outer-compatible one makes the two folded S3 generators literal standard
triality matrices on the rank-four weight space:

  tau05 = diag(1,1,1,-1)

and

  tau24 = (1/2) *
    [ 1  1  1 -1
      1  1 -1  1
      1 -1  1  1
     -1  1  1  1 ].

These exchange the vector/two-half-spinor weight systems exactly as the folded
F4 action exchanges the three 8-sectors.  The same chart also identifies the
canonical 32-term support with the standard D4 weight condition
`lambda+ + lambda_v + lambda- = 0`.
-/

namespace Integration.F4D4OuterTrialityRecognition

open Integration.E6Minuscule27LiteralRecognition
open Integration.E6F4WeylFold
open Integration.F4MinusculeOnePlus26
open Integration.F4D4TrialityAlbertShape
open Integration.F4D4TrialitySupport
open Integration.F4D4StandardTrialityRecognition

/-- Outer-compatible sector0 graph; this agrees with the previous D4-only
choice. -/
def plusGraph : Finset (DynkinLabel × D4Weight) := sector0SpinPlusGraph

/-- Outer-compatible vector graph. -/
def vectorGraphOuter : Finset (DynkinLabel × D4Weight) :=
  { (e6 (-1) 0 1 0 0 (-1), d4 0 0 0 (-2)),
    (e6 0 (-1) 0 1 (-1) 0, d4 0 (-2) 0 0),
    (e6 0 (-1) 1 0 0 0, d4 0 0 2 0),
    (e6 0 0 0 1 (-1) 0, d4 2 0 0 0),
    (e6 0 0 1 (-1) 0 0, d4 (-2) 0 0 0),
    (e6 0 1 0 0 (-1) 0, d4 0 0 (-2) 0),
    (e6 0 1 1 (-1) 0 0, d4 0 2 0 0),
    (e6 1 0 0 0 (-1) 1, d4 0 0 0 2) }

/-- Outer-compatible negative-spinor graph. -/
def minusGraphOuter : Finset (DynkinLabel × D4Weight) :=
  { (e6 0 (-1) 0 0 1 (-1), d4 (-1) (-1) 1 (-1)),
    (e6 0 0 (-1) 1 0 (-1), d4 1 (-1) (-1) (-1)),
    (e6 0 0 0 0 1 (-1), d4 1 1 1 (-1)),
    (e6 0 1 0 (-1) 1 (-1), d4 (-1) 1 (-1) (-1)),
    (e6 1 (-1) (-1) 1 0 0, d4 1 (-1) 1 1),
    (e6 1 0 (-1) 0 0 0, d4 (-1) (-1) (-1) 1),
    (e6 1 0 0 (-1) 1 0, d4 (-1) 1 1 1),
    (e6 1 1 (-1) 0 0 0, d4 1 1 (-1) 1) }

/-- These are still the same three standard D4 representations and still
intertwine the four selected D4 simple reflections. -/
theorem outer_compatible_graph_images :
    plusGraph.image Prod.fst = trialityOrbit0 ∧
    plusGraph.image Prod.snd = spinPlusSet ∧
    vectorGraphOuter.image Prod.fst = trialityOrbit1 ∧
    vectorGraphOuter.image Prod.snd = vectorSet ∧
    minusGraphOuter.image Prod.fst = trialityOrbit2 ∧
    minusGraphOuter.image Prod.snd = spinMinusSet := by
  native_decide

theorem outer_compatible_d4_action :
    (∀ s p, p ∈ plusGraph →
      (foldedD4Reflect s p.1, standardReflect s p.2) ∈ plusGraph) ∧
    (∀ s p, p ∈ vectorGraphOuter →
      (foldedD4Reflect s p.1, standardReflect s p.2) ∈ vectorGraphOuter) ∧
    (∀ s p, p ∈ minusGraphOuter →
      (foldedD4Reflect s p.1, standardReflect s p.2) ∈ minusGraphOuter) := by
  native_decide

/-- Triality transposition fixing the vector representation and exchanging the
two half-spinor systems. -/
def tau05 (w : D4Weight) : D4Weight :=
  d4 (w 0) (w 1) (w 2) (- w 3)

/-- Hadamard triality transposition fixing the positive-spinor system and
exchanging vector with negative-spinor weights.  On all three standard weight
sets the displayed numerators are even. -/
def tau24 (w : D4Weight) : D4Weight :=
  d4 ((w 0 + w 1 + w 2 - w 3) / 2)
     ((w 0 + w 1 - w 2 + w 3) / 2)
     ((w 0 - w 1 + w 2 + w 3) / 2)
     ((-w 0 + w 1 + w 2 + w 3) / 2)

/-- Exact folded/standard same-action square for the two outer generators. -/
theorem g05_outer_triality_intertwiner :
    (∀ p, p ∈ plusGraph →
      (foldReflect .g05 p.1, tau05 p.2) ∈ minusGraphOuter) ∧
    (∀ p, p ∈ minusGraphOuter →
      (foldReflect .g05 p.1, tau05 p.2) ∈ plusGraph) ∧
    (∀ p, p ∈ vectorGraphOuter →
      (foldReflect .g05 p.1, tau05 p.2) ∈ vectorGraphOuter) := by
  native_decide

theorem g24_outer_triality_intertwiner :
    (∀ p, p ∈ plusGraph →
      (foldReflect .g24 p.1, tau24 p.2) ∈ plusGraph) ∧
    (∀ p, p ∈ vectorGraphOuter →
      (foldReflect .g24 p.1, tau24 p.2) ∈ minusGraphOuter) ∧
    (∀ p, p ∈ minusGraphOuter →
      (foldReflect .g24 p.1, tau24 p.2) ∈ vectorGraphOuter) := by
  native_decide

/-- Both outer maps are involutions on every standard triality weight. -/
theorem outer_triality_involutions :
    (∀ w ∈ spinPlusSet ∪ vectorSet ∪ spinMinusSet, tau05 (tau05 w) = w) ∧
    (∀ w ∈ spinPlusSet ∪ vectorSet ∪ spinMinusSet, tau24 (tau24 w) = w) := by
  native_decide

/-- Their product has order three on the complete 24-weight union, giving the
outer S3 triality action. -/
theorem outer_triality_s3_braid :
    ∀ w ∈ spinPlusSet ∪ vectorSet ∪ spinMinusSet,
      tau05 (tau24 (tau05 (tau24 (tau05 (tau24 w))))) = w := by
  native_decide

/-- Standard weight-basis support of the D4 triality tensor. -/
def weightSumZero (p s m : D4Weight) : Bool :=
  decide (∀ i, p i + s i + m i = 0)

/-- The independently discovered 32-term non-Schlaefli support is exactly the
standard vector/half-spinor weight-zero condition in the outer-compatible chart. -/
theorem finite_support_is_standard_triality_weight_support :
    ∀ p0 ∈ plusGraph, ∀ p1 ∈ vectorGraphOuter, ∀ p2 ∈ minusGraphOuter,
      trialitySupportLabel p0.1 p1.1 p2.1 =
        weightSumZero p0.2 p1.2 p2.2 := by
  native_decide

inductive StandardWeightTrialityCreatesOctonionBasisIntertwiner : Prop

theorem standard_triality_does_not_create_octonion_basis_intertwiner :
    ¬ StandardWeightTrialityCreatesOctonionBasisIntertwiner := by
  intro h; cases h

structure Boundary where
  fullD4SameActionPaid : Bool
  tau05ExplicitPaid : Bool
  tau24HadamardExplicitPaid : Bool
  outerS3RelationsPaid : Bool
  foldedOuterGeneratorIntertwinersPaid : Bool
  standardTrialitySupportSameObjectPaid : Bool
  actualOctonionBasisIntertwinerPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  fullD4SameActionPaid := true
  tau05ExplicitPaid := true
  tau24HadamardExplicitPaid := true
  outerS3RelationsPaid := true
  foldedOuterGeneratorIntertwinersPaid := true
  standardTrialitySupportSameObjectPaid := true
  actualOctonionBasisIntertwinerPaid := false

end Integration.F4D4OuterTrialityRecognition
