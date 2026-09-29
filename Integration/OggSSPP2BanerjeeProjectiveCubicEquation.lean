import Mathlib
import Integration.OggSSPP2BanerjeeAffineCurveScheme

/-!
# Banerjee universal cubic: exact homogenization and point at infinity

For R = W(F4)[[a1]], the affine equation is

  y² + a1*x*y + y - x³ = 0.

Its homogeneous cubic is

  Y²Z + a1*XYZ + YZ² - X³ = 0.

This file proves that restricting to Z=1 gives the original equation and that
(0:1:0) lies on the cubic.  These are ring-theoretic results.  They do not yet
construct Proj, identify a projective scheme with the affine chart, or prove
smoothness, properness, or the elliptic group law.
-/

namespace Integration.OggSSPP2BanerjeeProjectiveCubicEquation

namespace Aff := Integration.OggSSPP2BanerjeeAffineCurveScheme
namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource

abbrev R := Aff.R

def affineEquationAt (x y : R) : R :=
  y ^ 2 + B.universalParameter * x * y + y - x ^ 3

def homogeneousCubicAt (X Y Z : R) : R :=
  Y ^ 2 * Z + B.universalParameter * X * Y * Z +
    Y * Z ^ 2 - X ^ 3

theorem dehomogenize_at_one (x y : R) :
    homogeneousCubicAt x y 1 = affineEquationAt x y := by
  simp [homogeneousCubicAt, affineEquationAt]

theorem infinity_lies_on_cubic :
    homogeneousCubicAt 0 1 0 = 0 := by
  simp [homogeneousCubicAt]

theorem every_point_on_infinity_chart_has_X_zero
    (x y : R)
    (h : homogeneousCubicAt x y 0 = 0) :
    x ^ 3 = 0 := by
  simpa [homogeneousCubicAt] using h

structure Boundary where
  literalHomogeneousCubicOwned : Bool
  affineChartZOneRecoversBanerjeeEquation : Bool
  pointAtInfinityLiesOnCubic : Bool
  infinityChartCubicEquationImpliesXCubedZero : Bool
  projectiveSchemeConstructed : Bool
  formalCompletionComparedWithSpf : Bool
  ellipticGroupSchemeConstructed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  literalHomogeneousCubicOwned := true
  affineChartZOneRecoversBanerjeeEquation := true
  pointAtInfinityLiesOnCubic := true
  infinityChartCubicEquationImpliesXCubedZero := true
  projectiveSchemeConstructed := false
  formalCompletionComparedWithSpf := false
  ellipticGroupSchemeConstructed := false

end Integration.OggSSPP2BanerjeeProjectiveCubicEquation
