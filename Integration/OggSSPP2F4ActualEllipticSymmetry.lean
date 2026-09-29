import Integration.OggSSPP2F4ActualGroupGenerators
import Integration.OggSSPP2F4ActualEllipticGroup
import Integration.OggSSPP2BanerjeeF4ZetaCoordinates
import Mathlib

/-!
# Actual characteristic-two elliptic point carrier: Frobenius and order-three symmetry

This owner acts on the *real Mathlib nonsingular Weierstrass point type*, not
on a parallel nine-label table.  The functions are built from the actual
coordinates of E : y²+y=x³ over F₄ and preserve its equation.

F(x,y) = (x²,y²) and R(x,y) = (ζ*x,y), with infinity fixed, satisfy
F² = 1, R³ = 1, and F R F = R².  Inversion of the elliptic point group is
a different map; it has y-coordinate y+1.

The action relations are proved as permutations of the actual point carrier.
Group-homomorphism status for F and R, elliptic 3-torsion, and an equivariant
additive 369 chart are separate obligations.  Nothing here infers an
exceptional Monster exponent or a Γ₀(4) subgroup scheme.
-/

namespace Integration.OggSSPP2F4ActualEllipticSymmetry

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace Z := Integration.OggSSPP2BanerjeeF4ZetaCoordinates
namespace G := Integration.OggSSPP2F4ActualEllipticGroup

open WeierstrassCurve

private theorem equation_of_nonsingular
    {x y : B.F4}
    (h : B.specialCurve.toAffine.Nonsingular x y) :
    y ^ 2 + y = x ^ 3 := by
  have heq :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular
      (W := B.specialCurve.toAffine)).mpr h
  simpa [B.specialCurve] using
    (WeierstrassCurve.Affine.equation_iff
      (W := B.specialCurve.toAffine) x y).mp heq

theorem frobenius_preserves_curve
    (x y : B.F4) (h : y ^ 2 + y = x ^ 3) :
    (y ^ 2) ^ 2 + y ^ 2 = (x ^ 2) ^ 3 := by
  calc
    (y ^ 2) ^ 2 + y ^ 2 = (y ^ 2 + y) ^ 2 := by
      have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
      linear_combination -(y ^ 3 * htwo)
    _ = (x ^ 3) ^ 2 := congrArg (fun t : B.F4 => t ^ 2) h
    _ = (x ^ 2) ^ 3 := by ring

theorem shear_preserves_curve
    (x y : B.F4) (h : y ^ 2 + y = x ^ 3) :
    y ^ 2 + y = (Z.zeta * x) ^ 3 := by
  calc
    y ^ 2 + y = x ^ 3 := h
    _ = Z.zeta ^ 3 * x ^ 3 := by rw [Z.zeta_cube_is_one]; ring
    _ = (Z.zeta * x) ^ 3 := by ring

noncomputable def frobenius : G.ActualCurveGroup → G.ActualCurveGroup
  | .zero => 0
  | .some x y h =>
      G.fromAffineEquation (x ^ 2) (y ^ 2)
        (frobenius_preserves_curve x y (equation_of_nonsingular h))

noncomputable def shear : G.ActualCurveGroup → G.ActualCurveGroup
  | .zero => 0
  | .some x y h =>
      G.fromAffineEquation (Z.zeta * x) y
        (shear_preserves_curve x y (equation_of_nonsingular h))

theorem frobenius_zero : frobenius 0 = 0 := rfl
theorem shear_zero : shear 0 = 0 := rfl

theorem frobenius_square (p : G.ActualCurveGroup) :
    frobenius (frobenius p) = p := by
  cases p with
  | zero => rfl
  | some x y h =>
      have hx : (x ^ 2) ^ 2 = x := by
        simpa [pow_mul] using
          (Integration.OggSSPP2F4CurveTangentFlex.f4_fourth_power x)
      have hy : (y ^ 2) ^ 2 = y := by
        simpa [pow_mul] using
          (Integration.OggSSPP2F4CurveTangentFlex.f4_fourth_power y)
      simp only [frobenius, G.fromAffineEquation]
      rw [hx, hy]

theorem shear_cube (p : G.ActualCurveGroup) :
    shear (shear (shear p)) = p := by
  cases p with
  | zero => rfl
  | some x y h =>
      simp only [shear, G.fromAffineEquation]
      have hx : Z.zeta * (Z.zeta * (Z.zeta * x)) = x := by
        calc
          _ = Z.zeta ^ 3 * x := by ring
          _ = x := by rw [Z.zeta_cube_is_one]; ring
      rw [hx]

theorem frobenius_shear_frobenius (p : G.ActualCurveGroup) :
    frobenius (shear (frobenius p)) = shear (shear p) := by
  cases p with
  | zero => rfl
  | some x y h =>
      simp only [frobenius, shear, G.fromAffineEquation]
      have hx : (Z.zeta * x ^ 2) ^ 2 =
          Z.zeta * (Z.zeta * x) := by
        calc
          _ = Z.zeta ^ 2 * x ^ 4 := by ring
          _ = Z.zeta * (Z.zeta * x) := by
            rw [Integration.OggSSPP2F4CurveTangentFlex.f4_fourth_power x]
            ring
      have hy : (y ^ 2) ^ 2 = y := by
        simpa [pow_mul] using
          (Integration.OggSSPP2F4CurveTangentFlex.f4_fourth_power y)
      rw [hx, hy]

/-! ## Actual permutations, rather than merely functions on labelled points -/

noncomputable def frobeniusEquiv : G.ActualCurveGroup ≃ G.ActualCurveGroup where
  toFun := frobenius
  invFun := frobenius
  left_inv := frobenius_square
  right_inv := frobenius_square

noncomputable def shearEquiv : G.ActualCurveGroup ≃ G.ActualCurveGroup where
  toFun := shear
  invFun := fun p => shear (shear p)
  left_inv := by
    intro p
    exact shear_cube p
  right_inv := by
    intro p
    change shear (shear (shear p)) = p
    exact shear_cube p

theorem conjugation_relation_as_permutations :
    frobeniusEquiv.trans (shearEquiv.trans frobeniusEquiv)
      = shearEquiv.trans shearEquiv := by
  ext p
  exact frobenius_shear_frobenius p

/-! ## Actual generator-level relative-F₂-Frobenius reflection -/

namespace Gen := Integration.OggSSPP2F4ActualGroupGenerators

theorem frobenius_fixed_actual_P :
    frobenius Gen.P = Gen.P := by
  simp [frobenius, Gen.P, G.fromAffineEquation]

/-- The F₂-Frobenius of Q has precisely Q's genuine elliptic inverse
coordinate. This uses the SOURCE curve negY and the actual ζ polynomial,
not a ternary label reflection. -/
theorem frobenius_actual_Q_y_eq_negY :
    (Z.zeta ^ 2 : B.F4)
      =
    B.specialCurve.toAffine.negY 1 Z.zeta := by
  have h : (Z.zeta ^ 2 : B.F4) = -Z.zeta - 1 := by
    linear_combination Z.zeta_quadratic
  simpa [WeierstrassCurve.Affine.negY, B.specialCurve] using h

/-- The asserted matrix reflection on the proposed P,Q axes has now been
verified on Q as an equality of ACTUAL elliptic points.  To extend it to all
points by group linearity still requires a genuine additive chart. -/
theorem frobenius_actual_Q_eq_neg :
    frobenius Gen.Q = -Gen.Q := by
  simp only [Gen.Q, frobenius, G.fromAffineEquation,
    WeierstrassCurve.Affine.Point.neg_some]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨by norm_num, frobenius_actual_Q_y_eq_negY⟩

structure Boundary where
  actsOnActualMathlibEllipticPoints : Bool
  bothMapsPreserveSourceCurveEquation : Bool
  frobeniusSquareIdentity : Bool
  shearCubeIdentity : Bool
  conjugationInvertsShear : Bool
  actualFrobeniusAndShearAreEquivalences : Bool
  s3RelationAsActualPermutations : Bool
  actionPreservesEllipticAddition : Bool
  additive369EigenbasisConstructed : Bool
  levelFourModuliRecognized : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  actsOnActualMathlibEllipticPoints := true
  bothMapsPreserveSourceCurveEquation := true
  frobeniusSquareIdentity := true
  shearCubeIdentity := true
  conjugationInvertsShear := true
  actualFrobeniusAndShearAreEquivalences := true
  s3RelationAsActualPermutations := true
  actionPreservesEllipticAddition := false
  additive369EigenbasisConstructed := false
  levelFourModuliRecognized := false

end Integration.OggSSPP2F4ActualEllipticSymmetry
