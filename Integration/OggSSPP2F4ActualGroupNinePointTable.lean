import Mathlib
import Integration.OggSSPP2F4ActualGroupBasis
import Integration.OggSSPP2F4ActualGroupRelations

/-!
# Exact nine-point table for the genuine Banerjee elliptic group

The established additive chart
  (ZMod 3 × ZMod 3) ≃+ E(F4)
is now tied to explicit affine coordinates.

The only new secant calculation is P-Q.  The other entries follow from
the already-proved P+Q relation and elliptic inversion.

This owner is intended as the finite same-object bridge used by the
coordinate Frobenius/shear recognition.  It does not introduce a new
nine-state carrier.
-/

namespace Integration.OggSSPP2F4ActualGroupNinePointTable

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace Z := Integration.OggSSPP2BanerjeeF4ZetaCoordinates
namespace E := Integration.OggSSPP2F4ActualEllipticGroup
namespace G := Integration.OggSSPP2F4ActualGroupGenerators
namespace R := Integration.OggSSPP2F4ActualGroupRelations
namespace Basis := Integration.OggSSPP2F4ActualGroupBasis

open WeierstrassCurve

abbrev W := B.specialCurve.toAffine

noncomputable def S : E.ActualCurveGroup :=
  E.fromAffineEquation (Z.zeta ^ 2) (Z.zeta ^ 2) (by
    calc
      (Z.zeta ^ 2) ^ 2 + Z.zeta ^ 2 = 1 :=
        Z.zeta_squared_trace_one
      _ = (Z.zeta ^ 2) ^ 3 := by
        symm
        exact (Z.cube_one_iff (Z.zeta ^ 2)).2
          (Or.inr (Or.inr rfl)))

theorem slope_P_negQ :
    W.slope 0 1 0 (Z.zeta ^ 2) = Z.zeta ^ 2 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (by norm_num)]
  simp

theorem addX_P_negQ :
    W.addX 0 1 (W.slope 0 1 0 (Z.zeta ^ 2)) =
      Z.zeta ^ 2 := by
  rw [slope_P_negQ]
  simp only [WeierstrassCurve.Affine.addX]
  simp [B.specialCurve]
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  have h4 : Z.zeta ^ 4 = Z.zeta := Z.zeta_fourth_is_zeta
  linear_combination h4 + Z.zeta_trace_one + Z.zeta * htwo

theorem negAddY_P_negQ :
    W.negAddY 0 1 0 (W.slope 0 1 0 (Z.zeta ^ 2)) =
      Z.zeta := by
  rw [slope_P_negQ, WeierstrassCurve.Affine.negAddY,
    addX_P_negQ]
  exact Z.zeta_fourth_is_zeta

theorem addY_P_negQ :
    W.addY 0 1 0 (W.slope 0 1 0 (Z.zeta ^ 2)) =
      Z.zeta ^ 2 := by
  rw [WeierstrassCurve.Affine.addY, negAddY_P_negQ]
  simp [WeierstrassCurve.Affine.negY, B.specialCurve]
  have htwo : (2 : B.F4) = 0 := CharP.cast_eq_zero B.F4 2
  linear_combination Z.zeta_trace_one + htwo

theorem P_sub_Q_eq_S :
    G.P - G.Q = S := by
  rw [sub_eq_add_neg]
  unfold G.P G.Q S E.fromAffineEquation
  rw [WeierstrassCurve.Affine.Point.neg_some]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by norm_num)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_P_negQ, addY_P_negQ⟩

theorem chart_00 :
    Basis.actualC3SquareAddEquiv (0,0) = 0 := by simp

theorem chart_10 :
    Basis.actualC3SquareAddEquiv (1,0) = G.P := by simp

theorem chart_20 :
    Basis.actualC3SquareAddEquiv (2,0) = -G.P := by
  simp [Basis.actualC3SquareAddEquiv_apply, G.candidateChart,
    R.P_add_P_eq_neg_P, two_nsmul]

theorem chart_01 :
    Basis.actualC3SquareAddEquiv (0,1) = G.Q := by simp

theorem chart_02 :
    Basis.actualC3SquareAddEquiv (0,2) = -G.Q := by
  simp [Basis.actualC3SquareAddEquiv_apply, G.candidateChart,
    R.Q_add_Q_eq_neg_Q, two_nsmul]

theorem chart_11 :
    Basis.actualC3SquareAddEquiv (1,1) = R.R := by
  simpa [Basis.actualC3SquareAddEquiv_apply, G.candidateChart]
    using R.P_add_Q_eq_R

theorem chart_12 :
    Basis.actualC3SquareAddEquiv (1,2) = S := by
  rw [Basis.actualC3SquareAddEquiv_apply]
  simp [G.candidateChart, two_nsmul, R.Q_add_Q_eq_neg_Q]
  simpa [sub_eq_add_neg] using P_sub_Q_eq_S

theorem chart_21 :
    Basis.actualC3SquareAddEquiv (2,1) = -S := by
  rw [Basis.actualC3SquareAddEquiv_apply]
  simp [G.candidateChart, two_nsmul, R.P_add_P_eq_neg_P]
  have h := congrArg Neg.neg P_sub_Q_eq_S
  simpa [sub_eq_add_neg, neg_add_rev] using h

theorem chart_22 :
    Basis.actualC3SquareAddEquiv (2,2) = -R.R := by
  rw [Basis.actualC3SquareAddEquiv_apply]
  simp [G.candidateChart, two_nsmul,
    R.P_add_P_eq_neg_P, R.Q_add_Q_eq_neg_Q]
  rw [← neg_add]
  exact congrArg Neg.neg R.P_add_Q_eq_R

structure Boundary where
  oneNewSecantCalculation : Bool
  allNineActualGroupCoordinatesPinned : Bool
  usesExistingAddEquiv : Bool
  createsParallelNineCarrier : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  oneNewSecantCalculation := true
  allNineActualGroupCoordinatesPinned := true
  usesExistingAddEquiv := true
  createsParallelNineCarrier := false

end Integration.OggSSPP2F4ActualGroupNinePointTable
