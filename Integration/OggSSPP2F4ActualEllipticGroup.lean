import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Integration.OggSSPP2BanerjeeSpecialFibreElliptic
import Integration.OggSSPP2BanerjeeF4ZetaCoordinates
import Integration.OggSSPP2F4CurveTangentFlex

/-!
# Genuine elliptic group carrier for Banerjee's F4 special fibre

The special curve is already defined as a Mathlib WeierstrassCurve F4, and
the discriminant-one / IsElliptic theorem is proved by the existing source.

We now select the actual Mathlib nonsingular affine point group, with zero
the projective point at infinity.  The constructor below takes an ACTUAL
F4 coordinate pair and proof of y²+y=x³ into this group.

The tangent flex theorem is separately available in
OggSSPP2F4CurveTangentFlex.  Nothing in this file asserts that the
previously selected Sheet9 set-chart preserves this group law, or that
the nine-point group has already been identified with (Z/3Z)^2.
-/

namespace Integration.OggSSPP2F4ActualEllipticGroup

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource

open WeierstrassCurve

abbrev ActualCurveGroup : Type :=
  B.specialCurve.toAffine.Point

noncomputable instance : AddCommGroup ActualCurveGroup :=
  inferInstance

def infinity : ActualCurveGroup := 0

/-- A point of the actual nonsingular elliptic group from a curve equation. -/
noncomputable def fromAffineEquation
    (x y : B.F4) (hcurve : y ^ 2 + y = x ^ 3) :
    ActualCurveGroup :=
  .some x y (by
    apply (WeierstrassCurve.Affine.equation_iff_nonsingular
      (W := B.specialCurve.toAffine)).mp
    apply (WeierstrassCurve.Affine.equation_iff
      (W := B.specialCurve.toAffine) x y).mpr
    simpa [B.specialCurve] using hcurve)

theorem infinity_is_group_identity :
    infinity = (0 : ActualCurveGroup) := rfl

theorem infinity_add (p : ActualCurveGroup) :
    infinity + p = p := zero_add p

theorem add_infinity (p : ActualCurveGroup) :
    p + infinity = p := add_zero p

theorem group_is_commutative (p q : ActualCurveGroup) :
    p + q = q + p := add_comm p q

theorem group_is_associative (p q r : ActualCurveGroup) :
    p + q + r = p + (q + r) := add_assoc p q r

structure Boundary where
  actualWeierstrassCurveReused : Bool
  discriminantOneEllipticInstanceReused : Bool
  actualNonsingularPointAddCommGroup : Bool
  curveEquationGivesActualPoint : Bool
  candidatePQToActualGroupModuleExists : Bool
  zeroIsActualInfinity : Bool
  ninePointGroupEquivalenceConstructed : Bool
  FrobeniusAsGroupEndomorphismConstructed : Bool
  threeTorsionIdentificationProved : Bool
  levelFourMarkedModuliConstructed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  actualWeierstrassCurveReused := true
  discriminantOneEllipticInstanceReused := true
  actualNonsingularPointAddCommGroup := true
  curveEquationGivesActualPoint := true
  candidatePQToActualGroupModuleExists := true
  zeroIsActualInfinity := true
  ninePointGroupEquivalenceConstructed := false
  FrobeniusAsGroupEndomorphismConstructed := false
  threeTorsionIdentificationProved := false
  levelFourMarkedModuliConstructed := false

end Integration.OggSSPP2F4ActualEllipticGroup
