import Integration.E6Minuscule27SchlafliRecognition
import Mathlib

/-!
# Finite E6 -> F4 Weyl folding on the paid minuscule 27

The repository's E6 Dynkin diagram is

  0 -- 2 -- 3 -- 4 -- 5
             |
             1

with outer involution `0 <-> 5`, `2 <-> 4`, fixing `1,3`.  The canonical
folded reflection generators are therefore

  s1, s3, s0*s5, s2*s4.

This owner stays at the finite Weyl/action level.  It does not identify the
continuous Albert automorphism group with F4.  What it pays is the exact
folded Coxeter/action signature and the restriction of the E6 minuscule 27:
24 distinct nonzero folded weights plus three E6 weights restricting to zero.
That is the finite weight-multiplicity shadow of `27 | F4 = 26 + 1`; it does
not by itself choose the two-dimensional zero-weight space of the 26 or the
one-dimensional Albert unit.
-/

namespace Integration.E6F4WeylFold

open Integration.E6Minuscule27LiteralRecognition
open Integration.E6Minuscule27SchlafliRecognition

abbrev Mat6 := Fin 6 → Fin 6 → Int
abbrev FoldedLabel := Fin 4 → Int

/-- Standard basis in Dynkin-label coordinates. -/
def basis6 (j : Fin 6) : DynkinLabel := fun i => if i = j then 1 else 0

/-- Integer matrix action on Dynkin labels. -/
def matrixApply (M : Mat6) (x : DynkinLabel) : DynkinLabel :=
  fun i => ∑ j : Fin 6, M i j * x j

/-- Composition `A ∘ B`. -/
def matrixComp (A B : Mat6) : Mat6 :=
  fun i j => ∑ k : Fin 6, A i k * B k j

/-- Identity matrix. -/
def identityMatrix : Mat6 := fun i j => if i = j then 1 else 0

/-- Matrix of one E6 simple reflection on Dynkin labels. -/
def simpleMatrix (s : E6SimpleReflection) : Mat6 :=
  fun i j => reflectLabel s (basis6 j) i

/-- Four generators of the diagram-fixed folded reflection action. -/
inductive FoldGenerator
  | g1 | g3 | g05 | g24
  deriving DecidableEq, Repr, Fintype

/-- Folded action directly on Dynkin labels. -/
def foldReflect : FoldGenerator → DynkinLabel → DynkinLabel
  | .g1  => reflectLabel .s1
  | .g3  => reflectLabel .s3
  | .g05 => fun x => reflectLabel .s5 (reflectLabel .s0 x)
  | .g24 => fun x => reflectLabel .s4 (reflectLabel .s2 x)

/-- Matrix of a folded generator. -/
def foldedGeneratorMatrix : FoldGenerator → Mat6
  | .g1  => simpleMatrix .s1
  | .g3  => simpleMatrix .s3
  | .g05 => matrixComp (simpleMatrix .s5) (simpleMatrix .s0)
  | .g24 => matrixComp (simpleMatrix .s4) (simpleMatrix .s2)

theorem folded_generator_matrix_agrees :
    ∀ g x, matrixApply (foldedGeneratorMatrix g) x = foldReflect g x := by
  native_decide

/-- One closure step under the four folded generators. -/
def expandMatrices (S : Finset Mat6) : Finset Mat6 :=
  S ∪ S.image (matrixComp (foldedGeneratorMatrix .g1)) ∪
      S.image (matrixComp (foldedGeneratorMatrix .g3)) ∪
      S.image (matrixComp (foldedGeneratorMatrix .g05)) ∪
      S.image (matrixComp (foldedGeneratorMatrix .g24))

def matrixOrbitN : Nat → Finset Mat6
  | 0 => {identityMatrix}
  | n + 1 => expandMatrices (matrixOrbitN n)

/-- Local exact preflight found folded Cayley diameter 24. -/
def foldedGeneratedSet : Finset Mat6 := matrixOrbitN 24

/-- Exact order of the finite folded image. -/
theorem folded_generated_card_1152 : foldedGeneratedSet.card = 1152 := by
  native_decide

/-- Round 24 is already closed. -/
theorem folded_generated_stable : matrixOrbitN 25 = foldedGeneratedSet := by
  native_decide

/-- Matrix power used only for finite Coxeter-signature checks. -/
def matrixPow (M : Mat6) : Nat → Mat6
  | 0 => identityMatrix
  | n + 1 => matrixComp M (matrixPow M n)

/-- Every folded generator is an involution. -/
theorem folded_generators_square_one :
    ∀ g, matrixPow (foldedGeneratorMatrix g) 2 = identityMatrix := by
  native_decide

/-- Coxeter pair orders form the F4 chain
`g1 --3-- g3 --4-- g24 --3-- g05`; the omitted pairs commute. -/
theorem folded_pair_order_g1_g3 :
    matrixPow (matrixComp (foldedGeneratorMatrix .g1) (foldedGeneratorMatrix .g3)) 3 =
      identityMatrix := by native_decide

theorem folded_pair_order_g3_g24 :
    matrixPow (matrixComp (foldedGeneratorMatrix .g3) (foldedGeneratorMatrix .g24)) 4 =
      identityMatrix := by native_decide

theorem folded_pair_order_g24_g05 :
    matrixPow (matrixComp (foldedGeneratorMatrix .g24) (foldedGeneratorMatrix .g05)) 3 =
      identityMatrix := by native_decide

theorem folded_nonadjacent_commute :
    matrixComp (foldedGeneratorMatrix .g1) (foldedGeneratorMatrix .g24) =
        matrixComp (foldedGeneratorMatrix .g24) (foldedGeneratorMatrix .g1) ∧
    matrixComp (foldedGeneratorMatrix .g1) (foldedGeneratorMatrix .g05) =
        matrixComp (foldedGeneratorMatrix .g05) (foldedGeneratorMatrix .g1) ∧
    matrixComp (foldedGeneratorMatrix .g3) (foldedGeneratorMatrix .g05) =
        matrixComp (foldedGeneratorMatrix .g05) (foldedGeneratorMatrix .g3) := by
  native_decide

/-- Restriction of an E6 Dynkin weight to the four folded coroot directions.
The two paired coordinates enter as sums. -/
def foldedLabel (lambda : DynkinLabel) : FoldedLabel
  | 0 => lambda 1
  | 1 => lambda 3
  | 2 => lambda 0 + lambda 5
  | 3 => lambda 2 + lambda 4

/-- One orbit-expansion step on weights under the four folded generators. -/
def expandWeights (S : Finset DynkinLabel) : Finset DynkinLabel :=
  S ∪ S.image (foldReflect .g1) ∪ S.image (foldReflect .g3) ∪
      S.image (foldReflect .g05) ∪ S.image (foldReflect .g24)

def foldedWeightOrbitN (seed : DynkinLabel) : Nat → Finset DynkinLabel
  | 0 => {seed}
  | n + 1 => expandWeights (foldedWeightOrbitN seed n)

/-- The nonzero folded orbit through the E6 minuscule highest weight. -/
def foldedNonzero24 : Finset DynkinLabel := foldedWeightOrbitN fundamentalWeight5 15

/-- One of the three E6 weights restricting to folded weight zero. -/
def foldedZeroSeed : DynkinLabel := ![1, 0, 0, 0, 0, -1]

def foldedZero3 : Finset DynkinLabel := foldedWeightOrbitN foldedZeroSeed 2

theorem folded_nonzero_card_24 : foldedNonzero24.card = 24 := by
  native_decide

theorem folded_zero_card_3 : foldedZero3.card = 3 := by
  native_decide

/-- The paid omega5 minuscule set decomposes exactly into these two folded
orbits. -/
theorem omega5_eq_folded_24_union_3 :
    minusculeOmega5Set = foldedNonzero24 ∪ foldedZero3 := by
  native_decide

theorem folded_orbits_disjoint : Disjoint foldedNonzero24 foldedZero3 := by
  native_decide

/-- All three exceptional E6 weights in the small orbit restrict to zero. -/
theorem folded_zero3_restricts_to_zero :
    ∀ lambda ∈ foldedZero3, foldedLabel lambda = 0 := by
  native_decide

/-- The 24-orbit has 24 pairwise-distinct folded labels. -/
def foldedNonzeroLabelSet : Finset FoldedLabel := foldedNonzero24.image foldedLabel

theorem folded_nonzero_labels_card_24 : foldedNonzeroLabelSet.card = 24 := by
  native_decide

theorem folded_nonzero_labels_exclude_zero : (0 : FoldedLabel) ∉ foldedNonzeroLabelSet := by
  native_decide

/-- The full restricted minuscule weight multiset has 25 distinct folded labels:
24 nonzero labels plus zero with multiplicity three at the E6-weight level. -/
def foldedOmega5LabelSet : Finset FoldedLabel := minusculeOmega5Set.image foldedLabel

theorem folded_omega5_distinct_label_card_25 : foldedOmega5LabelSet.card = 25 := by
  native_decide

inductive FoldedWeightMultiplicityCreatesAlbertUnit : Prop
inductive FiniteWeylFoldCreatesContinuousF4 : Prop

theorem folded_weight_multiplicity_does_not_choose_albert_unit :
    ¬ FoldedWeightMultiplicityCreatesAlbertUnit := by
  intro h; cases h

theorem finite_weyl_fold_does_not_create_continuous_f4 :
    ¬ FiniteWeylFoldCreatesContinuousF4 := by
  intro h; cases h

structure Boundary where
  diagramFoldGeneratorsTyped : Bool
  foldedImageOrder1152Paid : Bool
  f4CoxeterSignaturePaid : Bool
  minusculeOrbitSplit24Plus3Paid : Bool
  threeWeightsRestrictToZeroPaid : Bool
  twentyFourDistinctNonzeroFoldedWeightsPaid : Bool
  continuousF4AutJordanPaidHere : Bool
  zeroWeightSpaceSplitTwoPlusOnePaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  diagramFoldGeneratorsTyped := true
  foldedImageOrder1152Paid := true
  f4CoxeterSignaturePaid := true
  minusculeOrbitSplit24Plus3Paid := true
  threeWeightsRestrictToZeroPaid := true
  twentyFourDistinctNonzeroFoldedWeightsPaid := true
  continuousF4AutJordanPaidHere := false
  zeroWeightSpaceSplitTwoPlusOnePaidHere := false

end Integration.E6F4WeylFold
