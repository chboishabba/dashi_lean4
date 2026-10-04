import Integration.OggSSPP2F4ActualEllipticGroup
import Integration.OggSSPP2BanerjeeF4ZetaCoordinates
import Mathlib

/-!
# Independent Mathlib elliptic addition: the first P + Q secant payment

P=(0,0), Q=(1,ζ), R=(ζ,ζ) lie on the actual nonsingular
Weierstrass curve y²+y=x³ over F₄.  Unlike the recentered ternary
candidate operation, this calculation invokes Mathlib's genuine
WeierstrassCurve.Affine.Point.add_of_X_ne theorem.

It proves one arithmetic addition witness, not the full nine-point
group-table comparison or the C₃² eigenbasis isomorphism.
-/

namespace Integration.OggSSPP2F4ActualEllipticFirstSum

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace Z := Integration.OggSSPP2BanerjeeF4ZetaCoordinates
namespace G := Integration.OggSSPP2F4ActualEllipticGroup
namespace W := WeierstrassCurve.Affine

noncomputable def P : G.ActualCurveGroup :=
  G.fromAffineEquation 0 0 (by norm_num)

noncomputable def Q : G.ActualCurveGroup :=
  G.fromAffineEquation 1 Z.zeta (by
    simpa using Z.zeta_trace_one)

noncomputable def PplusQCandidate : G.ActualCurveGroup :=
  G.fromAffineEquation Z.zeta Z.zeta (by
    simpa [Z.zeta_cube_is_one] using Z.zeta_trace_one)

private theorem slope_PQ :
    (B.specialCurve.toAffine).slope 0 1 0 Z.zeta = Z.zeta := by
  rw [W.slope_of_X_ne (show (0 : B.F4) ≠ 1 by norm_num)]
  norm_num

private theorem addX_PQ :
    (B.specialCurve.toAffine).addX 0 1
      ((B.specialCurve.toAffine).slope 0 1 0 Z.zeta) = Z.zeta := by
  rw [slope_PQ]
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  have hζ : Z.zeta ^ 2 = Z.zeta + 1 := by
    linear_combination Z.zeta_trace_one - Z.zeta * htwo
  simp only [W.addX]
  simp [B.specialCurve, hζ]
  ring

private theorem addY_PQ :
    (B.specialCurve.toAffine).addY 0 1 0
      ((B.specialCurve.toAffine).slope 0 1 0 Z.zeta) = Z.zeta := by
  rw [slope_PQ]
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  have hζ : Z.zeta ^ 2 = Z.zeta + 1 := by
    linear_combination Z.zeta_trace_one - Z.zeta * htwo
  simp [W.addY, W.negAddY, W.negY, W.addX,
    B.specialCurve, hζ]
  ring

theorem actual_P_plus_Q_is_zeta_zeta :
    P + Q = PplusQCandidate := by
  unfold P Q PplusQCandidate G.fromAffineEquation
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne
    (show (0 : B.F4) ≠ 1 by norm_num)]
  simp only [addX_PQ, addY_PQ]

structure Boundary where
  genuineMathlibGroupUsed : Bool
  twoIndependentCurvePointsConstructed : Bool
  slopeComputedFromMathlibFormula : Bool
  resultCoordinatesComputedFromMathlibFormula : Bool
  selectedPPlusQProvedInActualGroup : Bool
  completeNinePointGroupLawProved : Bool
  ellipticFrobeniusAsAddHomProved : Bool
  fullC3SquaredIsomorphismProved : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  genuineMathlibGroupUsed := true
  twoIndependentCurvePointsConstructed := true
  slopeComputedFromMathlibFormula := true
  resultCoordinatesComputedFromMathlibFormula := true
  selectedPPlusQProvedInActualGroup := true
  completeNinePointGroupLawProved := false
  ellipticFrobeniusAsAddHomProved := false
  fullC3SquaredIsomorphismProved := false

end Integration.OggSSPP2F4ActualEllipticFirstSum
