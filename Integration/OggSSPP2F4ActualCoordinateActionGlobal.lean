import Mathlib
import Integration.OggSSPP2F4ActualGroupNinePointTable
import Integration.OggSSPP2F4ActualEllipticSymmetry
import Integration.OggSSPP2F4ActualGroupShearReflection

/-!
# Global same-object recognition of the F4 coordinate actions

The coordinate maps are independently defined on the actual Mathlib curve:
  F(x,y)   = (x²,y²)
  rho(x,y) = (zeta*x,y).

The group-side maps are independently defined by transporting the matrices
  (a,b) |-> (a,-b)
  (a,b) |-> (a+b,b)
through the proved additive equivalence (ZMod 3)^2 ≃+ E(F4).

This file compares the two constructions on the exact nine-point basis table.
It then proves equality on every actual elliptic point.

No additivity of the coordinate maps is assumed.
Additivity is derived from equality with the already-additive models.
-/

namespace Integration.OggSSPP2F4ActualCoordinateActionGlobal

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace Z := Integration.OggSSPP2BanerjeeF4ZetaCoordinates
namespace E := Integration.OggSSPP2F4ActualEllipticGroup
namespace G := Integration.OggSSPP2F4ActualGroupGenerators
namespace R := Integration.OggSSPP2F4ActualGroupRelations
namespace Basis := Integration.OggSSPP2F4ActualGroupBasis
namespace Table := Integration.OggSSPP2F4ActualGroupNinePointTable
namespace Sym := Integration.OggSSPP2F4ActualEllipticSymmetry
namespace Model := Integration.OggSSPP2F4ActualGroupShearReflection

open WeierstrassCurve

theorem frobenius_Pbar :
    Sym.frobenius Table.Pbar = Table.Pbar := by
  unfold Sym.frobenius Table.Pbar E.fromAffineEquation
  rfl

theorem frobenius_Qbar :
    Sym.frobenius Table.Qbar = G.Q := by
  unfold Sym.frobenius Table.Qbar G.Q E.fromAffineEquation
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨by norm_num, Z.zeta_frobenius_conjugate⟩

theorem frobenius_R :
    Sym.frobenius R.R = Table.S := by
  unfold Sym.frobenius R.R Table.S E.fromAffineEquation
  rfl

theorem frobenius_S :
    Sym.frobenius Table.S = R.R := by
  unfold Sym.frobenius Table.S R.R E.fromAffineEquation
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨Z.zeta_frobenius_conjugate,
    Z.zeta_frobenius_conjugate⟩

theorem frobenius_T :
    Sym.frobenius Table.T = Table.U := by
  unfold Sym.frobenius Table.T Table.U E.fromAffineEquation
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨Z.zeta_frobenius_conjugate, rfl⟩

theorem frobenius_U :
    Sym.frobenius Table.U = Table.T := by
  unfold Sym.frobenius Table.U Table.T E.fromAffineEquation
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, Z.zeta_frobenius_conjugate⟩

theorem shear_P :
    Sym.shear G.P = G.P := by
  unfold Sym.shear G.P E.fromAffineEquation
  rfl

theorem shear_Pbar :
    Sym.shear Table.Pbar = Table.Pbar := by
  unfold Sym.shear Table.Pbar E.fromAffineEquation
  rfl

theorem shear_Q :
    Sym.shear G.Q = R.R := by
  unfold Sym.shear G.Q R.R E.fromAffineEquation
  rfl

theorem shear_Qbar :
    Sym.shear Table.Qbar = Table.U := by
  unfold Sym.shear Table.Qbar Table.U E.fromAffineEquation
  rfl

theorem shear_R :
    Sym.shear R.R = Table.T := by
  unfold Sym.shear R.R Table.T E.fromAffineEquation
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨by ring, rfl⟩

theorem shear_S :
    Sym.shear Table.S = Table.Qbar := by
  unfold Sym.shear Table.S Table.Qbar E.fromAffineEquation
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨Z.zeta_cube_is_one, rfl⟩

theorem shear_T :
    Sym.shear Table.T = G.Q := by
  unfold Sym.shear Table.T G.Q E.fromAffineEquation
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨Z.zeta_cube_is_one, rfl⟩

theorem shear_U :
    Sym.shear Table.U = Table.S := by
  unfold Sym.shear Table.U Table.S E.fromAffineEquation
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨by ring, rfl⟩

theorem coordinate_frobenius_on_basis
    (a b : ZMod 3) :
    Sym.frobenius (Basis.actualC3SquareAddEquiv (a,b)) =
      Basis.actualC3SquareAddEquiv (a,-b) := by
  fin_cases a <;> fin_cases b <;>
    simp [Table.chart_00, Table.chart_10, Table.chart_20,
      Table.chart_01, Table.chart_02, Table.chart_11,
      Table.chart_12, Table.chart_21, Table.chart_22,
      Sym.frobenius_zero, Sym.frobenius_fixed_actual_P,
      Sym.frobenius_actual_Q_eq_neg,
      Table.neg_Q_eq_Qbar, frobenius_Pbar, frobenius_Qbar,
      frobenius_R, frobenius_S, frobenius_T, frobenius_U]

theorem coordinate_shear_on_basis
    (a b : ZMod 3) :
    Sym.shear (Basis.actualC3SquareAddEquiv (a,b)) =
      Basis.actualC3SquareAddEquiv (a+b,b) := by
  fin_cases a <;> fin_cases b <;>
    simp [Table.chart_00, Table.chart_10, Table.chart_20,
      Table.chart_01, Table.chart_02, Table.chart_11,
      Table.chart_12, Table.chart_21, Table.chart_22,
      Sym.shear_zero, shear_P, shear_Pbar, shear_Q, shear_Qbar,
      shear_R, shear_S, shear_T, shear_U]

theorem model_frobenius_on_basis
    (a b : ZMod 3) :
    Model.actualFrobeniusModel
        (Basis.actualC3SquareAddEquiv (a,b)) =
      Basis.actualC3SquareAddEquiv (a,-b) := by
  change Basis.actualC3SquareAddEquiv
    (Model.frobeniusMatrix
      (Basis.actualC3SquareAddEquiv.symm
        (Basis.actualC3SquareAddEquiv (a,b)))) =
    Basis.actualC3SquareAddEquiv (a,-b)
  rw [Basis.actualC3SquareAddEquiv.symm_apply_apply]
  rfl

theorem model_shear_on_basis
    (a b : ZMod 3) :
    Model.actualShearModel
        (Basis.actualC3SquareAddEquiv (a,b)) =
      Basis.actualC3SquareAddEquiv (a+b,b) := by
  change Basis.actualC3SquareAddEquiv
    (Model.shearMatrix
      (Basis.actualC3SquareAddEquiv.symm
        (Basis.actualC3SquareAddEquiv (a,b)))) =
    Basis.actualC3SquareAddEquiv (a+b,b)
  rw [Basis.actualC3SquareAddEquiv.symm_apply_apply]
  rfl

theorem coordinate_frobenius_eq_model :
    Sym.frobenius = Model.actualFrobeniusModel := by
  funext p
  obtain ⟨⟨a,b⟩, rfl⟩ :=
    Basis.actualC3SquareAddEquiv.surjective p
  rw [coordinate_frobenius_on_basis,
    model_frobenius_on_basis]

theorem coordinate_shear_eq_model :
    Sym.shear = Model.actualShearModel := by
  funext p
  obtain ⟨⟨a,b⟩, rfl⟩ :=
    Basis.actualC3SquareAddEquiv.surjective p
  rw [coordinate_shear_on_basis,
    model_shear_on_basis]

theorem coordinate_frobenius_additive :
    ∀ p q : E.ActualCurveGroup,
      Sym.frobenius (p+q) =
        Sym.frobenius p + Sym.frobenius q := by
  intro p q
  rw [coordinate_frobenius_eq_model]
  exact Model.actualFrobeniusModel.map_add p q

theorem coordinate_shear_additive :
    ∀ p q : E.ActualCurveGroup,
      Sym.shear (p+q) =
        Sym.shear p + Sym.shear q := by
  intro p q
  rw [coordinate_shear_eq_model]
  exact Model.actualShearModel.map_add p q

theorem coordinate_frobenius_matrix_exact
    (a b : ZMod 3) :
    Sym.frobenius
      (Basis.actualC3SquareAddEquiv (a,b)) =
      Basis.actualC3SquareAddEquiv
        (Model.frobeniusMatrix (a,b)) := by
  exact coordinate_frobenius_on_basis a b

theorem coordinate_shear_matrix_exact
    (a b : ZMod 3) :
    Sym.shear
      (Basis.actualC3SquareAddEquiv (a,b)) =
      Basis.actualC3SquareAddEquiv
        (Model.shearMatrix (a,b)) := by
  exact coordinate_shear_on_basis a b

structure Boundary where
  ninePointSameObjectTableUsed : Bool
  coordinateFrobeniusEqualsAdditiveModel : Bool
  coordinateShearEqualsAdditiveModel : Bool
  coordinateFrobeniusAdditivityPaid : Bool
  coordinateShearAdditivityPaid : Bool
  exactMatrixIntertwinersPaid : Bool
  intrinsicWeilPairingIdentified : Bool
  gamma0FourMarkedSchemeIdentified : Bool
  monsterValuationIdentified : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  ninePointSameObjectTableUsed := true
  coordinateFrobeniusEqualsAdditiveModel := true
  coordinateShearEqualsAdditiveModel := true
  coordinateFrobeniusAdditivityPaid := true
  coordinateShearAdditivityPaid := true
  exactMatrixIntertwinersPaid := true
  intrinsicWeilPairingIdentified := false
  gamma0FourMarkedSchemeIdentified := false
  monsterValuationIdentified := false

end Integration.OggSSPP2F4ActualCoordinateActionGlobal
