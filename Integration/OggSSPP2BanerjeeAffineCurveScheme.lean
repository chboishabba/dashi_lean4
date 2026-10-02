import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.MvPolynomial.Ideal
import Integration.OggSSPP2BanerjeeF4UniversalDeformationSource

/-!
# The actual affine scheme of Banerjee's universal Weierstrass equation

Let R = W(F₄)[[a₁]] and set
  A = R[x,y] / (y² + a₁*x*y + y - x³).

The affine chart is Spec A, with a literal structure map Spec A -> Spec R.
The closed immersion into affine 2-space is the Spec of the quotient map.

This is not yet the smooth proper elliptic scheme: its point at infinity,
group structure, and finite-flat Frobenius kernels remain open.
-/

namespace Integration.OggSSPP2BanerjeeAffineCurveScheme

open CategoryTheory
open AlgebraicGeometry

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource

abbrev R := B.F4DeformationBase
abbrev PolynomialRing := MvPolynomial (Fin 2) R

def x : PolynomialRing := MvPolynomial.X 0
def y : PolynomialRing := MvPolynomial.X 1
def parameter : PolynomialRing := MvPolynomial.C B.universalParameter

/-- Banerjee affine equation y² + a₁xy + y - x³. -/
def equation : PolynomialRing :=
  y ^ 2 + parameter * x * y + y - x ^ 3

def equationIdeal : Ideal PolynomialRing :=
  Ideal.span ({equation} : Set PolynomialRing)

abbrev CoordinateRing := PolynomialRing ⧸ equationIdeal

def xbar : CoordinateRing :=
  Ideal.Quotient.mk equationIdeal x

def ybar : CoordinateRing :=
  Ideal.Quotient.mk equationIdeal y

def coefficientMap : R →+* CoordinateRing :=
  (Ideal.Quotient.mk equationIdeal).comp MvPolynomial.C

def affineCurveScheme : Scheme :=
  Spec (CommRingCat.of CoordinateRing)

def deformationBaseScheme : Scheme :=
  Spec (CommRingCat.of R)

def affineCurveToBase : affineCurveScheme ⟶ deformationBaseScheme :=
  Spec.map (CommRingCat.ofHom coefficientMap)

def ambientAffinePlane : Scheme :=
  Spec (CommRingCat.of PolynomialRing)

def affineCurveClosedImmersion :
    affineCurveScheme ⟶ ambientAffinePlane :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk equationIdeal))

theorem affine_curve_is_closed_subscheme :
    IsClosedImmersion affineCurveClosedImmersion := by
  dsimp [affineCurveClosedImmersion]
  infer_instance

theorem equation_in_defining_ideal :
    equation ∈ equationIdeal := by
  apply Ideal.subset_span
  simp

/-- The defining Weierstrass equation holds in the actual coordinate ring. -/
theorem equation_vanishes_in_coordinate_ring :
    (Ideal.Quotient.mk equationIdeal) equation = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr equation_in_defining_ideal

/-- In the quotient, y² + a₁*x*y + y = x³ is an exact ring equality. -/
theorem affine_weierstrass_relation :
    ybar ^ 2 +
        (coefficientMap B.universalParameter) * xbar * ybar +
        ybar = xbar ^ 3 := by
  have h := equation_vanishes_in_coordinate_ring
  simp only [equation, map_sub, map_add, map_pow, map_mul,
    RingHom.comp_apply] at h
  dsimp [xbar, ybar, coefficientMap, parameter] at *
  exact sub_eq_zero.mp h

structure Boundary where
  actualPolynomialEquationOwned : Bool
  actualQuotientCoordinateRingOwned : Bool
  actualAffineSpecOwned : Bool
  actualMorphismToWittBaseOwned : Bool
  actualClosedImmersionIntoAffinePlaneOwned : Bool
  projectiveWeierstrassCompactificationOwned : Bool
  smoothProperEllipticGroupSchemeOwned : Bool
  finiteFlatFrobeniusKernelsOwned : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  actualPolynomialEquationOwned := true
  actualQuotientCoordinateRingOwned := true
  actualAffineSpecOwned := true
  actualMorphismToWittBaseOwned := true
  actualClosedImmersionIntoAffinePlaneOwned := true
  projectiveWeierstrassCompactificationOwned := false
  smoothProperEllipticGroupSchemeOwned := false
  finiteFlatFrobeniusKernelsOwned := false

end Integration.OggSSPP2BanerjeeAffineCurveScheme
