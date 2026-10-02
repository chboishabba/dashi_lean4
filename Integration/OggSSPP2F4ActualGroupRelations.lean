import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Integration.OggSSPP2F4ActualGroupGenerators

/-!
# Actual elliptic addition calculations for P=(0,0), Q=(1,zeta)

These lemmas compute Mathlib's genuine Weierstrass addition formula on the
Banerjee special fibre y²+y=x³.

The key point is that these are equalities in the ACTUAL elliptic point group,
not in the nine-label curve surrogate.
-/

namespace Integration.OggSSPP2F4ActualGroupRelations

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace Z := Integration.OggSSPP2BanerjeeF4ZetaCoordinates
namespace E := Integration.OggSSPP2F4ActualEllipticGroup
namespace G := Integration.OggSSPP2F4ActualGroupGenerators

open WeierstrassCurve

/-- The expected sum P+Q=(zeta,zeta). -/
noncomputable def R : E.ActualCurveGroup :=
  E.fromAffineEquation Z.zeta Z.zeta (by
    rw [Z.zeta_cube_is_one]
    exact Z.zeta_trace_one)

theorem slope_PQ :
    B.specialCurve.toAffine.slope 0 1 0 Z.zeta = Z.zeta := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (by norm_num)]
  simp

theorem addX_PQ :
    B.specialCurve.toAffine.addX 0 1
      (B.specialCurve.toAffine.slope 0 1 0 Z.zeta) = Z.zeta := by
  rw [slope_PQ]
  simp [WeierstrassCurve.Affine.addX, B.specialCurve]
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  linear_combination Z.zeta_trace_one + htwo

theorem negAddY_PQ :
    B.specialCurve.toAffine.negAddY 0 1 0
      (B.specialCurve.toAffine.slope 0 1 0 Z.zeta) = Z.zeta ^ 2 := by
  rw [slope_PQ, WeierstrassCurve.Affine.negAddY, addX_PQ]
  ring

theorem addY_PQ :
    B.specialCurve.toAffine.addY 0 1 0
      (B.specialCurve.toAffine.slope 0 1 0 Z.zeta) = Z.zeta := by
  rw [WeierstrassCurve.Affine.addY, negAddY_PQ]
  simp [WeierstrassCurve.Affine.negY, B.specialCurve]
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  linear_combination Z.zeta_trace_one + htwo

/--
The first actual secant calculation in the Mathlib elliptic group:
P + Q = (zeta,zeta).
-/
theorem P_add_Q_eq_R :
    G.P + G.Q = R := by
  unfold G.P G.Q R E.fromAffineEquation
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by norm_num)]
  rw [addX_PQ, addY_PQ]

/-- Doubling P=(0,0) gives its elliptic inverse (0,1). -/
noncomputable def negPPoint : E.ActualCurveGroup :=
  E.fromAffineEquation 0 1 (by norm_num)

theorem neg_P_eq_negPPoint :
    -G.P = negPPoint := by
  unfold G.P negPPoint E.fromAffineEquation
  simp [WeierstrassCurve.Affine.negY, B.specialCurve]

theorem slope_PP :
    B.specialCurve.toAffine.slope 0 0 0 0 = 0 := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne
    (hx := rfl)
    (hy := by
      simp [WeierstrassCurve.Affine.negY, B.specialCurve])]
  simp [B.specialCurve]

theorem P_add_P_eq_neg_P :
    G.P + G.P = -G.P := by
  unfold G.P E.fromAffineEquation
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (hy := by simp [WeierstrassCurve.Affine.negY, B.specialCurve])]
  rw [slope_PP]
  simp [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    B.specialCurve]

theorem three_nsmul_P :
    (3 : ℕ) • G.P = 0 := by
  rw [show (3 : ℕ) • G.P = G.P + G.P + G.P by simp [three_nsmul]]
  rw [P_add_P_eq_neg_P]
  exact neg_add_cancel G.P

/-- Doubling Q=(1,zeta) gives its elliptic inverse (1,zeta²). -/
theorem slope_QQ :
    B.specialCurve.toAffine.slope 1 1 Z.zeta Z.zeta = 1 := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne
    (hx := rfl)
    (hy := by
      simp [WeierstrassCurve.Affine.negY, B.specialCurve]
      exact Z.zeta_ne_one)]
  simp [B.specialCurve]
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  linear_combination htwo

theorem Q_add_Q_eq_neg_Q :
    G.Q + G.Q = -G.Q := by
  unfold G.Q E.fromAffineEquation
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (hy := by
      simp [WeierstrassCurve.Affine.negY, B.specialCurve]
      exact Z.zeta_ne_one)]
  rw [slope_QQ]
  simp [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    B.specialCurve]
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  linear_combination Z.zeta_trace_one + htwo

theorem three_nsmul_Q :
    (3 : ℕ) • G.Q = 0 := by
  rw [show (3 : ℕ) • G.Q = G.Q + G.Q + G.Q by simp [three_nsmul]]
  rw [Q_add_Q_eq_neg_Q]
  exact neg_add_cancel G.Q

theorem actual_three_torsion_goal :
    G.threeTorsionGoal := by
  exact ⟨three_nsmul_P, three_nsmul_Q⟩

structure Boundary where
  actualSecantPPlusQPaid : Bool
  actualDoublingPPaid : Bool
  actualDoublingQPaid : Bool
  actualPThreeTorsionPaid : Bool
  actualQThreeTorsionPaid : Bool
  basisIndependencePaid : Bool
  ninePointGroupEquivalencePaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  actualSecantPPlusQPaid := true
  actualDoublingPPaid := true
  actualDoublingQPaid := true
  actualPThreeTorsionPaid := true
  actualQThreeTorsionPaid := true
  basisIndependencePaid := false
  ninePointGroupEquivalencePaid := false

end Integration.OggSSPP2F4ActualGroupRelations
