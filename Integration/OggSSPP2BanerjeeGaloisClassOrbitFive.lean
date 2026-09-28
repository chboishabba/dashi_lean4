import Mathlib
import Integration.OggSSPP2OrientedInertiaTenStateRecognition
import Integration.OggSSPP2BanerjeeF4UniversalDeformationSource

/-!
# Banerjee Galois action on G24 conjugacy classes

The binary-tetrahedral G24 carrier has seven conjugacy classes:
  1, -1, order-4, two order-3 classes, two order-6 classes.

For the characteristic-two supersingular deformation, the nontrivial
Gal(F4/F2) automorphism acts by the nontrivial outer automorphism of G24.  On
the seven-class presentation it fixes the first three classes and swaps the
two order-3 and two order-6 classes.

This is exactly the same class permutation as inversion.

Consequently the repository's five inversion-orbits are also the five
Galois-orbits of the seven conjugacy classes.  The Galois C2 therefore does NOT
supply an independent binary factor after this quotient.

The class-level permutation is a DASHI reconstruction from the sourced
Galois action and the sourced seven-class table; the source does not phrase
the result as the repository's five-element datatype.
-/

namespace Integration.OggSSPP2BanerjeeGaloisClassOrbitFive

namespace Five := Integration.OggSSPP2OrientedInertiaTenStateRecognition

inductive G24ConjugacyClass
  | identity
  | centralMinusOne
  | orderFour
  | orderThreePositive
  | orderThreeNegative
  | orderSixPositive
  | orderSixNegative
  deriving DecidableEq, Repr, Fintype

theorem seven_conjugacy_classes :
    Fintype.card G24ConjugacyClass = 7 := by decide

def inverseClass : G24ConjugacyClass → G24ConjugacyClass
  | .identity => .identity
  | .centralMinusOne => .centralMinusOne
  | .orderFour => .orderFour
  | .orderThreePositive => .orderThreeNegative
  | .orderThreeNegative => .orderThreePositive
  | .orderSixPositive => .orderSixNegative
  | .orderSixNegative => .orderSixPositive

def galoisClassAction : G24ConjugacyClass → G24ConjugacyClass
  | .identity => .identity
  | .centralMinusOne => .centralMinusOne
  | .orderFour => .orderFour
  | .orderThreePositive => .orderThreeNegative
  | .orderThreeNegative => .orderThreePositive
  | .orderSixPositive => .orderSixNegative
  | .orderSixNegative => .orderSixPositive

theorem galois_class_action_equals_inversion
    (c : G24ConjugacyClass) :
    galoisClassAction c = inverseClass c := by
  cases c <;> rfl

theorem galois_class_action_involutive
    (c : G24ConjugacyClass) :
    galoisClassAction (galoisClassAction c) = c := by
  cases c <;> rfl

def quotientToFive :
    G24ConjugacyClass → Five.BinaryTetrahedralInversionOrbit
  | .identity => .identity
  | .centralMinusOne => .centralMinusOne
  | .orderFour => .orderFour
  | .orderThreePositive => .orderThreePair
  | .orderThreeNegative => .orderThreePair
  | .orderSixPositive => .orderSixPair
  | .orderSixNegative => .orderSixPair

theorem quotient_galois_invariant
    (c : G24ConjugacyClass) :
    quotientToFive (galoisClassAction c) = quotientToFive c := by
  cases c <;> rfl

theorem quotient_inverse_invariant
    (c : G24ConjugacyClass) :
    quotientToFive (inverseClass c) = quotientToFive c := by
  cases c <;> rfl

theorem every_five_orbit_has_representative :
    ∀ q : Five.BinaryTetrahedralInversionOrbit,
      ∃ c : G24ConjugacyClass, quotientToFive c = q := by
  intro q
  cases q with
  | identity => exact ⟨.identity, rfl⟩
  | centralMinusOne => exact ⟨.centralMinusOne, rfl⟩
  | orderFour => exact ⟨.orderFour, rfl⟩
  | orderThreePair => exact ⟨.orderThreePositive, rfl⟩
  | orderSixPair => exact ⟨.orderSixPositive, rfl⟩

theorem five_orbit_cardinality :
    Fintype.card Five.BinaryTetrahedralInversionOrbit = 5 := by
  decide

/--
Retaining a separate Galois sheet after quotienting the conjugacy classes is
extra presentation data, not a second independent quotient coordinate.
-/
structure RetainedGaloisSheetPresentation where
  sheet : Integration.OggSSPP2BanerjeeF4UniversalDeformationSource.GaloisSheet
  orbit : Five.BinaryTetrahedralInversionOrbit
  deriving DecidableEq, Repr

theorem retained_sheet_presentation_cardinality :
    Fintype.card
      (Integration.OggSSPP2BanerjeeF4UniversalDeformationSource.GaloisSheet ×
        Five.BinaryTetrahedralInversionOrbit) = 10 := by
  decide

structure Boundary where
  sevenClassCarrierOwned : Bool
  galoisOuterClassActionOwned : Bool
  galoisActionEqualsInversionOnClasses : Bool
  galoisOrbitQuotientHasFiveClasses : Bool
  galoisSheetIndependentOfFiveOrbitQuotient : Bool
  retainedGaloisSheetTimesFiveStillHasTenPresentations : Bool
  retainedTenPresentationPromotedToSourceQuotient : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  sevenClassCarrierOwned := true
  galoisOuterClassActionOwned := true
  galoisActionEqualsInversionOnClasses := true
  galoisOrbitQuotientHasFiveClasses := true
  galoisSheetIndependentOfFiveOrbitQuotient := false
  retainedGaloisSheetTimesFiveStillHasTenPresentations := true
  retainedTenPresentationPromotedToSourceQuotient := false

end Integration.OggSSPP2BanerjeeGaloisClassOrbitFive
