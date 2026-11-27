import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Integration.OggSSPP2F4ActualGroupGenerators

/-!
# Actual three-torsion for the Banerjee F4 basis points

This file works only in Mathlib's genuine elliptic point group.

For P=(0,0), the tangent has slope 0 and 2P=-P.
For Q=(1,zeta), the tangent has slope 1 and 2Q=-Q.

Hence 3P=0 and 3Q=0.

No cardinality argument is used.
No finite nine-state surrogate is used.
-/

namespace Integration.OggSSPP2F4ActualThreeTorsion

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace Z := Integration.OggSSPP2BanerjeeF4ZetaCoordinates
namespace E := Integration.OggSSPP2F4ActualEllipticGroup
namespace G := Integration.OggSSPP2F4ActualGroupGenerators

open WeierstrassCurve
open WeierstrassCurve.Affine

abbrev W := B.specialCurve.toAffine

theorem negY_P :
    W.negY 0 0 = 1 := by
  simp [WeierstrassCurve.Affine.negY, B.specialCurve]

theorem tangentSlopeP :
    W.slope 0 0 0 0 = 0 := by
  have hy : (0 : B.F4) ≠ W.negY 0 0 := by
    rw [negY_P]
    norm_num
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
  simp [B.specialCurve]

theorem doubleXP :
    W.addX 0 0 (W.slope 0 0 0 0) = 0 := by
  rw [tangentSlopeP]
  simp [WeierstrassCurve.Affine.addX, B.specialCurve]

theorem doubleYP :
    W.addY 0 0 0 (W.slope 0 0 0 0) = 1 := by
  rw [tangentSlopeP]
  simp [WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.addX,
    B.specialCurve]

theorem P_add_P_eq_neg_P :
    G.P + G.P = -G.P := by
  unfold G.P E.fromAffineEquation
  have hy : (0 : B.F4) ≠ W.negY 0 0 := by
    rw [negY_P]
    norm_num
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨doubleXP, doubleYP⟩

theorem threeP_is_zero :
    (3 : ℕ) • G.P = 0 := by
  rw [show (3 : ℕ) • G.P = (G.P + G.P) + G.P by simp [three_nsmul]]
  rw [P_add_P_eq_neg_P, neg_add_cancel]

theorem negY_Q :
    W.negY 1 Z.zeta = Z.zeta ^ 2 := by
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  simp only [WeierstrassCurve.Affine.negY]
  simp [B.specialCurve]
  linear_combination Z.zeta_trace_one + htwo

theorem tangentSlopeQ :
    W.slope 1 1 Z.zeta Z.zeta = 1 := by
  have hy : Z.zeta ≠ W.negY 1 Z.zeta := by
    rw [negY_Q]
    intro h
    have : Z.zeta ^ 2 + Z.zeta = 0 := by rw [← h]; simp
    rw [Z.zeta_trace_one] at this
    norm_num at this
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
  simp [B.specialCurve, negY_Q]
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  have hthree : (3 : B.F4) = 1 := by
    linear_combination htwo
  rw [hthree]
  field_simp
  linear_combination Z.zeta_trace_one

theorem doubleXQ :
    W.addX 1 1 (W.slope 1 1 Z.zeta Z.zeta) = 1 := by
  rw [tangentSlopeQ]
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  simp [WeierstrassCurve.Affine.addX, B.specialCurve]
  linear_combination htwo

theorem doubleYQ :
    W.addY 1 1 Z.zeta (W.slope 1 1 Z.zeta Z.zeta) = Z.zeta ^ 2 := by
  rw [tangentSlopeQ]
  simp only [WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.addX]
  simp [B.specialCurve]
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  linear_combination Z.zeta_trace_one + htwo

theorem Q_add_Q_eq_neg_Q :
    G.Q + G.Q = -G.Q := by
  unfold G.Q E.fromAffineEquation
  have hy : Z.zeta ≠ W.negY 1 Z.zeta := by
    rw [negY_Q]
    intro h
    have : Z.zeta ^ 2 + Z.zeta = 0 := by rw [← h]; simp
    rw [Z.zeta_trace_one] at this
    norm_num at this
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨doubleXQ, doubleYQ⟩

theorem threeQ_is_zero :
    (3 : ℕ) • G.Q = 0 := by
  rw [show (3 : ℕ) • G.Q = (G.Q + G.Q) + G.Q by simp [three_nsmul]]
  rw [Q_add_Q_eq_neg_Q, neg_add_cancel]

theorem basis_three_torsion :
    G.threeTorsionGoal :=
  ⟨threeP_is_zero, threeQ_is_zero⟩

structure Boundary where
  PDoubleEqualsNegative : Bool
  QDoubleEqualsNegative : Bool
  PThreeTorsionPaid : Bool
  QThreeTorsionPaid : Bool
  independencePaid : Bool
  fullNinePointEquivalencePaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  PDoubleEqualsNegative := true
  QDoubleEqualsNegative := true
  PThreeTorsionPaid := true
  QThreeTorsionPaid := true
  independencePaid := false
  fullNinePointEquivalencePaid := false

end Integration.OggSSPP2F4ActualThreeTorsion
