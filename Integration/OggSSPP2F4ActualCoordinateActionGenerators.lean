import Mathlib
import Integration.OggSSPP2F4ActualEllipticSymmetry
import Integration.OggSSPP2F4ActualGroupShearReflection
import Integration.OggSSPP2F4ActualGroupRelations

/-!
# Coordinate symmetry recognition on actual elliptic generators

The elliptic (x,y)-maps are independently defined:
  Frobenius (x,y) = (x²,y²),
  rho       (x,y) = (zeta*x,y).

The group-side model maps are independently defined through the previously
proved actual E(F4) ≃+ (ZMod 3)².

Here we prove they agree on the two ACTUAL Mathlib elliptic generators,
without assuming global additivity of either coordinate map.

Upgrading agreement on generators to equality on *all* group elements is
equivalent to proving that the independently defined coordinate maps are
additive.  We do not promote generator agreement to that stronger claim.
-/

namespace Integration.OggSSPP2F4ActualCoordinateActionGenerators

namespace E := Integration.OggSSPP2F4ActualEllipticGroup
namespace G := Integration.OggSSPP2F4ActualGroupGenerators
namespace R := Integration.OggSSPP2F4ActualGroupRelations
namespace Z := Integration.OggSSPP2BanerjeeF4ZetaCoordinates
namespace Sym := Integration.OggSSPP2F4ActualEllipticSymmetry
namespace Model := Integration.OggSSPP2F4ActualGroupShearReflection

open WeierstrassCurve

theorem coordinate_frobenius_P :
    Sym.frobenius G.P = Model.actualFrobeniusModel G.P := by
  rw [Sym.frobenius_fixed_actual_P, Model.actualFrobeniusModel_P]

theorem coordinate_frobenius_Q :
    Sym.frobenius G.Q = Model.actualFrobeniusModel G.Q := by
  rw [Sym.frobenius_actual_Q_eq_neg, Model.actualFrobeniusModel_Q]

theorem coordinate_shear_P :
    Sym.shear G.P = Model.actualShearModel G.P := by
  rw [Model.actualShearModel_P]
  unfold G.P E.fromAffineEquation Sym.shear
  simp

/--
The actual coordinate map rho carries Q=(1,zeta) to
R=(zeta,zeta)=P+Q.  This is independent of the transported model.
-/
theorem coordinate_shear_Q_is_P_plus_Q :
    Sym.shear G.Q = G.P + G.Q := by
  rw [R.P_add_Q_eq_R]
  unfold G.Q R.R E.fromAffineEquation Sym.shear
  simp

theorem coordinate_shear_Q :
    Sym.shear G.Q = Model.actualShearModel G.Q := by
  rw [coordinate_shear_Q_is_P_plus_Q, Model.actualShearModel_Q]

/--
The coordinate F and rho are known to be permutations. Their agreement with
the ADDITIVE automorphisms on the generators is now established above.
The remaining global recognition is genuinely about their compatibility with
the curve's addition, not about the choice of basis.
-/
def coordinateFrobeniusAdditive : Prop :=
  ∀ p q : E.ActualCurveGroup,
    Sym.frobenius (p+q) = Sym.frobenius p + Sym.frobenius q

def coordinateShearAdditive : Prop :=
  ∀ p q : E.ActualCurveGroup,
    Sym.shear (p+q) = Sym.shear p + Sym.shear q

/-- A homomorphism out of a rank-two ternary group is determined by its two generators. -/
private theorem agree_on_basis_implies_equal
    (f : E.ActualCurveGroup → E.ActualCurveGroup)
    (hzero : f 0 = 0)
    (hadd : ∀ p q, f (p+q) = f p + f q)
    (model : E.ActualCurveGroup →+ E.ActualCurveGroup)
    (hP : f G.P = model G.P)
    (hQ : f G.Q = model G.Q) :
    f = model := by
  funext p
  obtain ⟨ab, rfl⟩ :=
    Integration.OggSSPP2F4ActualGroupBasis.chartHom_bijective.2 p
  rcases ab with ⟨a,b⟩
  change f (a.val • G.P + b.val • G.Q) =
    model (a.val • G.P + b.val • G.Q)
  have hnsmul (n : ℕ) (q : E.ActualCurveGroup) :
      f (n • q) = n • f q := by
    induction n with
    | zero => simpa using hzero
    | succ n ih =>
        rw [succ_nsmul, hadd, ih, succ_nsmul]
  rw [hadd, hnsmul, hnsmul, hP, hQ, map_add, map_nsmul, map_nsmul]

/-- Global Frobenius matrix identification reduces to coordinate additivity. -/
theorem frobenius_global_of_additive
    (hadd : coordinateFrobeniusAdditive) :
    Sym.frobenius = Model.actualFrobeniusModel := by
  apply agree_on_basis_implies_equal
    Sym.frobenius Sym.frobenius_zero hadd
    Model.actualFrobeniusModel.toAddMonoidHom
  · exact coordinate_frobenius_P
  · exact coordinate_frobenius_Q

/-- Global zeta-shear matrix identification reduces to coordinate additivity. -/
theorem shear_global_of_additive
    (hadd : coordinateShearAdditive) :
    Sym.shear = Model.actualShearModel := by
  apply agree_on_basis_implies_equal
    Sym.shear Sym.shear_zero hadd
    Model.actualShearModel.toAddMonoidHom
  · exact coordinate_shear_P
  · exact coordinate_shear_Q

structure Boundary where
  actualCoordinateFrobeniusMatchesPAndQ : Bool
  actualCoordinateZetaShearMatchesPAndQ : Bool
  genericTwoGeneratorHomExtAvailable : Bool
  globalCoordinateFrobeniusAdditivityProved : Bool
  globalCoordinateShearAdditivityProved : Bool
  intrinsicWeilPairingIdentified : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  actualCoordinateFrobeniusMatchesPAndQ := true
  actualCoordinateZetaShearMatchesPAndQ := true
  genericTwoGeneratorHomExtAvailable := true
  globalCoordinateFrobeniusAdditivityProved := false
  globalCoordinateShearAdditivityProved := false
  intrinsicWeilPairingIdentified := false

end Integration.OggSSPP2F4ActualCoordinateActionGenerators
