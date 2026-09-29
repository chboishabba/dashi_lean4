import Integration.OggSSPP2F4ActualEllipticGroup
import Integration.OggSSPP2F4ActualGroupGenerators
import Integration.OggSSPP2F4CurveTangentFlex
import Mathlib

/-!
# Full 3-torsion of the genuine E(F4) point group

For E : y²+y=x³ over F4, every rational affine tangent has slope x²,
with tangent intersection x-coordinate x⁴=x and sum y-coordinate -y-1.
Consequently 2P=-P for EVERY genuine Mathlib group point and 3P=0.

This pays torsion on the actual curve, not on a nine-element label carrier.
A full pointed C3² additive equivalence and intrinsic Weil pairing
are separate source claims.
-/

namespace Integration.OggSSPP2F4ActualGroupExponentThree

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace G := Integration.OggSSPP2F4ActualEllipticGroup
namespace Gen := Integration.OggSSPP2F4ActualGroupGenerators

open WeierstrassCurve

private def W := B.specialCurve.toAffine

private theorem characteristic_two : (2 : B.F4) = 0 :=
  CharP.cast_eq_zero B.F4 2

private theorem characteristic_three : (3 : B.F4) = 1 := by
  have htwo := characteristic_two
  linear_combination htwo

private theorem negY_distinct (x y : B.F4) :
    y ≠ W.negY x y := by
  intro heq
  have htwo := characteristic_two
  have hone : (1 : B.F4) = 0 := by
    have h : y = -y - 1 := by
      simpa [W, WeierstrassCurve.Affine.negY, B.specialCurve] using heq
    linear_combination h + y*htwo
  exact one_ne_zero hone

private theorem tangent_slope (x y : B.F4) :
    W.slope x x y y = x^2 := by
  have hy := negY_distinct x y
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
  have htwo := characteristic_two
  have hthree := characteristic_three
  have hden : y - W.negY x y = 1 := by
    simp only [W, WeierstrassCurve.Affine.negY, B.specialCurve]
    linear_combination y*htwo
  rw [hden]
  simp [W, B.specialCurve, htwo, hthree]

private theorem tangent_sum_x (x y : B.F4) :
    W.addX x x (W.slope x x y y) = x := by
  rw [tangent_slope]
  have hx := Integration.OggSSPP2F4CurveTangentFlex.f4_fourth_power x
  have htwo := characteristic_two
  simp only [W, WeierstrassCurve.Affine.addX, B.specialCurve]
  calc
    (x^2)^2 + 0*x^2 - 0 - x - x = x^4 - 2*x := by ring
    _ = x := by rw [hx]; linear_combination x*htwo

private theorem tangent_sum_y (x y : B.F4) :
    W.addY x x y (W.slope x x y y) = W.negY x y := by
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
  rw [tangent_sum_x]
  simp

/-- Actual rational elliptic doubling equals inverse for every point. -/
theorem every_point_double_eq_neg
    (p : G.ActualCurveGroup) : p + p = -p := by
  cases p with
  | zero => simp
  | some x y h =>
    have hy := negY_distinct x y
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy,
        WeierstrassCurve.Affine.Point.neg_some]
    apply WeierstrassCurve.Affine.Point.some.injEq.mpr
    exact ⟨tangent_sum_x x y, tangent_sum_y x y⟩

theorem every_point_three_torsion
    (p : G.ActualCurveGroup) : (3 : ℕ) • p = 0 := by
  rw [three_nsmul, every_point_double_eq_neg]
  exact neg_add_cancel p

/-- The previously proposed P,Q candidate basis now has actual 3-torsion,
rather than a Bool-valued recognition promise. -/
theorem selected_generators_three_torsion :
    Gen.threeTorsionGoal := by
  exact ⟨every_point_three_torsion Gen.P,
    every_point_three_torsion Gen.Q⟩

end Integration.OggSSPP2F4ActualGroupExponentThree
