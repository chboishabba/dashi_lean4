import Integration.OggSSPP2F4ActualEllipticSymmetry
import Integration.OggSSPP2F4ActualGroupGenerators

/-!
# First genuine addition check on the F4 elliptic group

The actual Weierstrass chord through P=(0,0) and Q=(1,zeta) has slope
zeta and group sum (zeta,zeta).  Thus the curve automorphism
shear(x,y)=(zeta*x,y) sends Q to the ACTUAL elliptic group sum P+Q.
This is more than an agreement of 9-state labels; it uses Mathlib's
nonsingular point group law.

It does not yet prove that P,Q generate E(F4), are 3-torsion, or that
the shear is an additive automorphism of all points.
-/

namespace Integration.OggSSPP2F4ActualChordShear

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace Z := Integration.OggSSPP2BanerjeeF4ZetaCoordinates
namespace G := Integration.OggSSPP2F4ActualEllipticGroup
namespace Gen := Integration.OggSSPP2F4ActualGroupGenerators
namespace Sym := Integration.OggSSPP2F4ActualEllipticSymmetry

open WeierstrassCurve

private def W := B.specialCurve.toAffine

theorem actualChordSlope :
    W.slope 0 1 0 Z.zeta = Z.zeta := by
  simp [W, WeierstrassCurve.Affine.slope, B.specialCurve]

theorem actualChordX :
    W.addX 0 1 (W.slope 0 1 0 Z.zeta) = Z.zeta := by
  have hchar : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  have hminus : -(Z.zeta : B.F4) = Z.zeta := by
    linear_combination Z.zeta * hchar
  have hx : (Z.zeta : B.F4)^2 - 1 = -Z.zeta := by
    linear_combination Z.zeta_trace_one
  rw [actualChordSlope]
  simp only [W, WeierstrassCurve.Affine.addX, B.specialCurve]
  simpa using hx.trans hminus

theorem actualChordY :
    W.addY 0 1 0 (W.slope 0 1 0 Z.zeta) = Z.zeta := by
  rw [actualChordSlope]
  simp only [W, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY]
  rw [show
      B.specialCurve.toAffine.addX 0 1 Z.zeta = Z.zeta
    from by simpa [actualChordSlope] using actualChordX]
  simp only [B.specialCurve]
  linear_combination Z.zeta_quadratic

noncomputable def chordPoint : G.ActualCurveGroup :=
  G.fromAffineEquation Z.zeta Z.zeta (by
    rw [Z.zeta_trace_one, Z.zeta_cube_is_one])

theorem actual_P_add_Q_eq_chordPoint :
    Gen.P + Gen.Q = chordPoint := by
  have hneq : (0 : B.F4) ≠ 1 := by norm_num
  simp only [Gen.P, Gen.Q, chordPoint, G.fromAffineEquation]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hneq]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨actualChordX, actualChordY⟩

theorem shear_actual_P_fixed :
    Sym.shear Gen.P = Gen.P := by
  simp [Sym.shear, Gen.P, G.fromAffineEquation]

theorem shear_actual_Q_eq_P_add_Q :
    Sym.shear Gen.Q = Gen.P + Gen.Q := by
  rw [actual_P_add_Q_eq_chordPoint]
  simp [Sym.shear, Gen.Q, chordPoint, G.fromAffineEquation]

end Integration.OggSSPP2F4ActualChordShear
