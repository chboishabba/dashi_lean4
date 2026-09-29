import Mathlib
import Integration.OggSSPP2BanerjeeF4ZetaCoordinates

/-!
# Banerjee F4 special fibre: tangent flex identity

The existing finite field and classified affine points are consumed as source.
For E : y²+y=x³ in characteristic two, the tangent at an affine rational
point (x,y) is Y=y+x²(X+x).  Its intersection polynomial with E equals
(X+x)³, as an identity of functions of X over the genuine F4 field.

The result supplies the actual tangent/flex geometry required before a
group-law identification with (Z/3Z)^2.  This module does not construct
the elliptic group law, 3-torsion group scheme, or Gamma0(4) marking.
-/

namespace Integration.OggSSPP2F4CurveTangentFlex

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource

def tangentY (x y X : B.F4) : B.F4 :=
  y + x ^ 2 * (X + x)

theorem f4_fourth_power (x : B.F4) : x ^ 4 = x := by
  have h := FiniteField.pow_card x
  simpa [Integration.OggSSPP2BanerjeeF4ZetaCoordinates.f4_cardinality] using h

theorem tangent_meets_cubic_as_triple_root
    (x y : B.F4) (hcurve : y ^ 2 + y = x ^ 3)
    (X : B.F4) :
    (tangentY x y X) ^ 2 + tangentY x y X + X ^ 3 =
      (X + x) ^ 3 := by
  have htwo : (2 : B.F4) = 0 :=
    CharP.cast_eq_zero B.F4 2
  have hfour : x ^ 4 = x := f4_fourth_power x
  dsimp [tangentY]
  linear_combination hcurve
    + (X + x) ^ 2 * hfour
    + (y * x ^ 2 * (X + x) + x ^ 3 - x * X ^ 2) * htwo

theorem tangent_passes_through_curve_point
    (x y : B.F4) :
    tangentY x y x = y := by
  have htwo : (2 : B.F4) = 0 :=
    CharP.cast_eq_zero B.F4 2
  dsimp [tangentY]
  linear_combination x ^ 2 * x * htwo

theorem tangent_intersection_polynomial_at_point
    (x y : B.F4) (hcurve : y ^ 2 + y = x ^ 3) :
    (tangentY x y x) ^ 2 + tangentY x y x + x ^ 3 = 0 := by
  rw [tangent_meets_cubic_as_triple_root x y hcurve]
  have htwo : (2 : B.F4) = 0 :=
    CharP.cast_eq_zero B.F4 2
  rw [show x + x = (0 : B.F4) from by
    linear_combination x * htwo]
  norm_num

/-- Characteristic-two Weierstrass negation of an affine point. -/
def affineNegationY (y : B.F4) : B.F4 := y + 1

theorem negation_preserves_affine_curve
    (x y : B.F4) (hcurve : y ^ 2 + y = x ^ 3) :
    (affineNegationY y) ^ 2 + affineNegationY y = x ^ 3 := by
  have htwo : (2 : B.F4) = 0 :=
    CharP.cast_eq_zero B.F4 2
  dsimp [affineNegationY]
  linear_combination hcurve + (y + 1) * htwo

theorem affine_negation_involutive (y : B.F4) :
    affineNegationY (affineNegationY y) = y := by
  have htwo : (2 : B.F4) = 0 :=
    CharP.cast_eq_zero B.F4 2
  dsimp [affineNegationY]
  linear_combination htwo

/-- Frobenius commutes with the coordinate inverse y -> y+1. -/
theorem frobenius_commutes_with_negation (y : B.F4) :
    (affineNegationY y) ^ 2 = affineNegationY (y ^ 2) := by
  have htwo : (2 : B.F4) = 0 :=
    CharP.cast_eq_zero B.F4 2
  dsimp [affineNegationY]
  linear_combination y * htwo

structure Boundary where
  actualF4TangentGeometry : Bool
  allAffineCurvePointsHaveTripleTangentIntersection : Bool
  negationOnYPlusOnePreservesCurve : Bool
  frobeniusCommutesWithCoordinateNegation : Bool
  geometricFlexProved : Bool
  ellipticGroupLawConstructed : Bool
  fullThreeTorsionGroupIdentification : Bool
  levelFourFiniteFlatMarking : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  actualF4TangentGeometry := true
  allAffineCurvePointsHaveTripleTangentIntersection := true
  negationOnYPlusOnePreservesCurve := true
  frobeniusCommutesWithCoordinateNegation := true
  geometricFlexProved := true
  ellipticGroupLawConstructed := false
  fullThreeTorsionGroupIdentification := false
  levelFourFiniteFlatMarking := false

end Integration.OggSSPP2F4CurveTangentFlex
