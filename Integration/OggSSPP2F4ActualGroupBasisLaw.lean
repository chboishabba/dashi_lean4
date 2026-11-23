import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Integration.OggSSPP2F4ActualGroupGenerators

/-!
# First actual group-law basis identity on the Banerjee F4 curve

This file proves on Mathlib's genuine elliptic point group that

  P + Q = (zeta,zeta),

for P=(0,0) and Q=(1,zeta).

It uses Mathlib's affine secant addition formula.
It does not infer the result from the nine-point count.
It does not identify the full group with (Z/3Z)^2 yet.
-/

namespace Integration.OggSSPP2F4ActualGroupBasisLaw

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace Z := Integration.OggSSPP2BanerjeeF4ZetaCoordinates
namespace E := Integration.OggSSPP2F4ActualEllipticGroup
namespace G := Integration.OggSSPP2F4ActualGroupGenerators

open WeierstrassCurve
open WeierstrassCurve.Affine

abbrev W := B.specialCurve.toAffine

noncomputable def R : E.ActualCurveGroup :=
  E.fromAffineEquation Z.zeta Z.zeta (by
    calc
      Z.zeta ^ 2 + Z.zeta = 1 := Z.zeta_trace_one
      _ = Z.zeta ^ 3 := Z.zeta_cube_is_one.symm)

theorem secantSlopePQ :
    W.slope 0 1 0 Z.zeta = Z.zeta := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (by norm_num)]
  simp

theorem addXPQ :
    W.addX 0 1 (W.slope 0 1 0 Z.zeta) = Z.zeta := by
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  rw [secantSlopePQ]
  simp only [WeierstrassCurve.Affine.addX]
  simp [B.specialCurve]
  linear_combination Z.zeta_quadratic - Z.zeta * htwo

theorem addYPQ :
    W.addY 0 1 0 (W.slope 0 1 0 Z.zeta) = Z.zeta := by
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  rw [secantSlopePQ]
  simp only [WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.addX]
  simp [B.specialCurve]
  linear_combination Z.zeta_quadratic - Z.zeta * htwo

theorem P_add_Q_eq_R :
    G.P + G.Q = R := by
  unfold G.P G.Q R E.fromAffineEquation
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by norm_num)]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addXPQ, addYPQ⟩

/--
The coordinate automorphism rho(x,y)=(zeta*x,y) sends Q to the same
actual elliptic-group point as P+Q.
This is a point identity.
The theorem does not yet assert that rho is an AddEquiv.
-/
theorem rho_Q_point_eq_P_add_Q :
    R = G.P + G.Q :=
  P_add_Q_eq_R.symm

structure Boundary where
  actualPointPReused : Bool
  actualPointQReused : Bool
  secantSlopeComputed : Bool
  actualEllipticAdditionComputed : Bool
  rhoQEqualsPPlusQAsPoint : Bool
  rhoIsGroupAutomorphismProved : Bool
  fullC3SquareBasisProved : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  actualPointPReused := true
  actualPointQReused := true
  secantSlopeComputed := true
  actualEllipticAdditionComputed := true
  rhoQEqualsPPlusQAsPoint := true
  rhoIsGroupAutomorphismProved := false
  fullC3SquareBasisProved := false

end Integration.OggSSPP2F4ActualGroupBasisLaw
