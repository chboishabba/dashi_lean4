import Integration.E6F4WeylFold
import Mathlib

/-!
# Folded E6 minuscule weights as the F4 short-root orbit

`E6F4WeylFold` paid the four diagram-fold generators, their 1152-element
closure, and the 24+3 restriction of the E6 minuscule 27.  This file identifies
the resulting rank-four reflection law with an explicit F4 Cartan matrix and
shows that the 24 nonzero restricted minuscule weights are exactly one of the
two 24-root Weyl orbits.

This is a finite Weyl/root-system theorem.  It still does not identify the
continuous Jordan automorphism group `Aut(J)` with the compact/real F4 group.
-/

namespace Integration.E6F4ShortRootRecognition

open Integration.E6Minuscule27LiteralRecognition
open Integration.E6Minuscule27SchlafliRecognition
open Integration.E6F4WeylFold

/-- F4 Cartan matrix in the folded-node order
`g1 --3-- g3 --4-- g24 --3-- g05`, written in the internal index order
`g1,g3,g05,g24`. -/
def f4Cartan (j i : Fin 4) : Int :=
  ![![ 2, -1,  0,  0],
    ![-1,  2,  0, -1],
    ![ 0,  0,  2, -1],
    ![ 0, -2, -1,  2]] j i

/-- Fold-generator to its rank-four simple-reflection coordinate. -/
def foldIndex : FoldGenerator → Fin 4
  | .g1  => 0
  | .g3  => 1
  | .g05 => 2
  | .g24 => 3

/-- Simple reflection on rank-four Dynkin labels for the explicit folded
Cartan matrix. -/
def f4ReflectLabel (i : Fin 4) (lambda : FoldedLabel) : FoldedLabel :=
  fun j => lambda j - lambda i * f4Cartan j i

/-- On every paid omega5 weight, restriction after the E6 diagram-fold action
is exactly the explicit F4 Cartan reflection.  The finite carrier makes this a
closed exact computation rather than a symbolic ambient-weight assumption. -/
theorem folded_label_action_is_f4_cartan_on_omega5 :
    ∀ g (w : Omega5Weight),
      foldedLabel (foldReflect g w.1) =
        f4ReflectLabel (foldIndex g) (foldedLabel w.1) := by
  native_decide

/-- Dynkin label of the `i`-th simple root: the `i`-th Cartan column. -/
def simpleRootLabel (i : Fin 4) : FoldedLabel := fun j => f4Cartan j i

/-- Close a rank-four weight set under all four F4 simple reflections. -/
def expandF4Weights (S : Finset FoldedLabel) : Finset FoldedLabel :=
  S ∪ S.image (f4ReflectLabel 0) ∪ S.image (f4ReflectLabel 1) ∪
      S.image (f4ReflectLabel 2) ∪ S.image (f4ReflectLabel 3)

def f4WeightOrbitN (seed : FoldedLabel) : Nat → Finset FoldedLabel
  | 0 => {seed}
  | n + 1 => expandF4Weights (f4WeightOrbitN seed n)

/-- The two simple-root length classes.  Local exact preflight found diameter 8
for both root orbits.  In this numbering node 2 belongs to the 24-root class
seen in the restricted minuscule representation. -/
def f4ShortRootSet : Finset FoldedLabel := f4WeightOrbitN (simpleRootLabel 2) 8
def f4LongRootSet  : Finset FoldedLabel := f4WeightOrbitN (simpleRootLabel 0) 8

theorem f4_short_root_card_24 : f4ShortRootSet.card = 24 := by
  native_decide

theorem f4_long_root_card_24 : f4LongRootSet.card = 24 := by
  native_decide

theorem f4_root_orbits_disjoint : Disjoint f4ShortRootSet f4LongRootSet := by
  native_decide

/-- The finite F4 root system has the expected 48 roots. -/
def f4RootSet : Finset FoldedLabel := f4ShortRootSet ∪ f4LongRootSet

theorem f4_root_card_48 : f4RootSet.card = 48 := by
  native_decide

/-- Main recognition theorem: the 24 nonzero folded weights coming from the E6
minuscule 27 are literally the F4 short-root orbit for the folded Cartan action. -/
theorem restricted_minuscule_nonzero_eq_f4_short_roots :
    foldedNonzeroLabelSet = f4ShortRootSet := by
  native_decide

/-- Consequently the restricted E6 minuscule weight pattern is exactly
24 short roots plus folded zero with multiplicity three at the E6-weight level. -/
theorem restricted_minuscule_distinct_weights_are_short_roots_plus_zero :
    foldedOmega5LabelSet = insert 0 f4ShortRootSet := by
  native_decide

inductive F4RootSystemRecognitionCreatesAlbertAutomorphismGroup : Prop

theorem finite_f4_roots_do_not_create_albert_automorphism_group :
    ¬ F4RootSystemRecognitionCreatesAlbertAutomorphismGroup := by
  intro h; cases h

structure Boundary where
  explicitF4CartanPaid : Bool
  foldedActionMatchesF4CartanOnMinusculePaid : Bool
  shortRootOrbit24Paid : Bool
  longRootOrbit24Paid : Bool
  fullFiniteRootSet48Paid : Bool
  minusculeNonzeroWeightsAreShortRootsPaid : Bool
  continuousAutJordanEqualsF4PaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  explicitF4CartanPaid := true
  foldedActionMatchesF4CartanOnMinusculePaid := true
  shortRootOrbit24Paid := true
  longRootOrbit24Paid := true
  fullFiniteRootSet48Paid := true
  minusculeNonzeroWeightsAreShortRootsPaid := true
  continuousAutJordanEqualsF4PaidHere := false

end Integration.E6F4ShortRootRecognition
