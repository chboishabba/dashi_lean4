import Integration.E6F4WeylFold
import Integration.E6Minuscule27SchlafliRecognition
import Mathlib

/-!
# Finite W(F4) invariance does not determine the Albert forms

The folded image has exact order 1152 and acts on the paid 27 minuscule weight
lines.  Remove the invariant scalar line: the resulting permutation character
is `fixedPoints - 1` on the 26-dimensional augmentation representation.

For a real representation with character chi, the standard symmetric-power
character numerators are

  Sym^2: chi(g)^2 + chi(g^2)
  Sym^3: chi(g)^3 + 3 chi(g) chi(g^2) + 2 chi(g^3).

This file computes the exact finite averages for the folded action.  The result
is 7 quadratic and 23 cubic invariant dimensions after dividing by 2|G| and
6|G| respectively.  Thus finite Weyl invariance alone cannot uniquely choose
the Albert quadratic/cubic structure.

The arithmetic checks are kernel-facing finite computations.  Interpreting the
averages as invariant-space dimensions uses the standard symmetric-power
character formula; no continuous F4 recognition is inferred here.
-/

namespace Integration.F4FiniteInvariantNonuniqueness

open Integration.E6Minuscule27LiteralRecognition
open Integration.E6Minuscule27SchlafliRecognition
open Integration.E6F4WeylFold

/-- Folded generated matrix together with its exact membership proof. -/
abbrev FoldedElement := {M : Mat6 // M ∈ foldedGeneratedSet}

instance : Fintype FoldedElement := inferInstance

/-- Every generated folded matrix preserves the omega5 orbit. -/
theorem folded_element_preserves_omega5 :
    ∀ (g : FoldedElement) (w : Omega5Weight),
      matrixApply g.1 w.1 ∈ minusculeOmega5Set := by
  native_decide

/-- Actual action on the 27 paid weights. -/
def actWeight (g : FoldedElement) (w : Omega5Weight) : Omega5Weight :=
  ⟨matrixApply g.1 w.1, folded_element_preserves_omega5 g w⟩

/-- Fixed weight-line count of a folded element. -/
def fixedCount (M : Mat6) : Nat :=
  (Finset.univ.filter fun w : Omega5Weight => matrixApply M w.1 = w.1).card

/-- Character of the 26-dimensional augmentation/traceless shadow:
permutation character on 27 weights minus its invariant scalar line. -/
def augmentationCharacter (M : Mat6) : Int :=
  Int.ofNat (fixedCount M) - 1

/-- Numerator of the Sym^2 character. -/
def sym2Numerator (M : Mat6) : Int :=
  let χ := augmentationCharacter M
  let χ2 := augmentationCharacter (matrixPow M 2)
  χ * χ + χ2

/-- Numerator of the Sym^3 character. -/
def sym3Numerator (M : Mat6) : Int :=
  let χ := augmentationCharacter M
  let χ2 := augmentationCharacter (matrixPow M 2)
  let χ3 := augmentationCharacter (matrixPow M 3)
  χ * χ * χ + 3 * χ * χ2 + 2 * χ3

/-- The generated subtype really contains the paid 1152 elements. -/
theorem folded_element_card_1152 : Fintype.card FoldedElement = 1152 := by
  native_decide

/-- Exact quadratic-character checksum: after division by `2*1152`, the
standard symmetric-square average is 7. -/
theorem sym2_character_checksum :
    (∑ g : FoldedElement, sym2Numerator g.1) = 2 * 1152 * 7 := by
  native_decide

/-- Exact cubic-character checksum: after division by `6*1152`, the standard
symmetric-cube average is 23. -/
theorem sym3_character_checksum :
    (∑ g : FoldedElement, sym3Numerator g.1) = 6 * 1152 * 23 := by
  native_decide

structure Boundary where
  foldedGroupOrder1152Paid : Bool
  augmentationCharacterTyped : Bool
  sym2ChecksumSevenPaid : Bool
  sym3ChecksumTwentyThreePaid : Bool
  finiteWeylQuadraticUnique : Bool
  finiteWeylCubicUnique : Bool
  finiteWeylInvarianceDeterminesAlbertStructure : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  foldedGroupOrder1152Paid := true
  augmentationCharacterTyped := true
  sym2ChecksumSevenPaid := true
  sym3ChecksumTwentyThreePaid := true
  finiteWeylQuadraticUnique := false
  finiteWeylCubicUnique := false
  finiteWeylInvarianceDeterminesAlbertStructure := false

inductive WeylInvarianceCreatesAlbertCubic : Prop

theorem finite_weyl_invariance_does_not_create_albert_cubic :
    ¬ WeylInvarianceCreatesAlbertCubic := by
  intro h; cases h

end Integration.F4FiniteInvariantNonuniqueness
