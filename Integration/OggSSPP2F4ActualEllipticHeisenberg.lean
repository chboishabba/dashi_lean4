import Integration.OggSSPP2F4ActualPairingNormalization
import Integration.OggSSPP2TernaryHeisenbergAction

/-!
# Exact actual-elliptic 27-state central extension and native Heisenberg chart

The base is the genuine Mathlib group E(F₄), with alternating cocycle from
its independently proved additive P,Q chart. The central coordinate is the
OPPOSITE of the native Schrödinger alternating gauge:

    z_ell = -(z_native + y*x).

This matches the prior Agda OggSSPP2WeilHeisenbergNativeBidiExact convention.
No intrinsic geometric Weil pairing, theta line bundle, or VOA identity is
inferred from this coordinate isomorphism.
-/

namespace Integration.OggSSPP2F4ActualEllipticHeisenberg

namespace E := Integration.OggSSPP2F4ActualEllipticGroup
namespace Basis := Integration.OggSSPP2F4ActualGroupBasis
namespace P := Integration.OggSSPP2F4ActualPairingNormalization
namespace Hei := Integration.Base369Heisenberg
namespace Act := Integration.OggSSPP2TernaryHeisenbergAction

abbrev F3 := ZMod 3
abbrev Plane := F3 × F3

structure ActualEllipticH27 where
  center : F3
  point : E.ActualCurveGroup

def product (g h : ActualEllipticH27) : ActualEllipticH27 :=
  ⟨g.center + h.center + 2 * P.ellipticOmega g.point h.point,
   g.point + h.point⟩

def identity : ActualEllipticH27 := ⟨0,0⟩

theorem product_assoc (g h k : ActualEllipticH27) :
    product (product g h) k = product g (product h k) := by
  cases g with | mk zg pg =>
  cases h with | mk zh ph =>
  cases k with | mk zk pk =>
  simp only [product, ActualEllipticH27.mk.injEq]
  constructor
  · rw [P.ellipticOmega_add_left,
      P.ellipticOmega_add_right]
    ring
  · exact add_assoc _ _ _

theorem identity_product (g : ActualEllipticH27) :
    product identity g = g := by
  cases g with | mk z p =>
  have hzero : P.ellipticOmega (0:E.ActualCurveGroup) p = 0 := by
    simp [P.ellipticOmega, P.planeOmega]
  simp [product, identity, hzero]

theorem product_identity (g : ActualEllipticH27) :
    product g identity = g := by
  cases g with | mk z p =>
  have hzero : P.ellipticOmega p (0:E.ActualCurveGroup) = 0 := by
    simp [P.ellipticOmega, P.planeOmega]
  simp [product, identity, hzero]

def nativePlane (g : Hei.H 1) : Plane :=
  (g.x 0, g.y 0)

def toActual (g : Hei.H 1) : ActualEllipticH27 :=
  ⟨-Act.alternatingCenterCoordinate g,
    Basis.actualC3SquareAddEquiv (nativePlane g)⟩

def fromActual (g : ActualEllipticH27) : Hei.H 1 :=
  let ab := Basis.actualC3SquareAddEquiv.symm g.point
  ⟨(fun _ => ab.1), (fun _ => ab.2),
    -g.center - ab.2 * ab.1⟩

private theorem rankOne_value (x : Hei.X 1) :
    (fun _ : Fin 1 => x 0) = x := by
  funext i
  fin_cases i
  rfl

theorem toActual_fromActual (g : ActualEllipticH27) :
    toActual (fromActual g) = g := by
  cases g with | mk z p =>
  simp only [toActual, fromActual, nativePlane,
    Act.alternatingCenterCoordinate]
  apply ActualEllipticH27.ext
  · simp [Hei.dot]
    ring
  · exact Basis.actualC3SquareAddEquiv.apply_symm_apply p

theorem fromActual_toActual (g : Hei.H 1) :
    fromActual (toActual g) = g := by
  apply Hei.H.ext'
  · simpa [fromActual, toActual, nativePlane,
      rankOne_value]
  · simpa [fromActual, toActual, nativePlane,
      rankOne_value]
  · simp [fromActual, toActual, nativePlane,
      Act.alternatingCenterCoordinate, Hei.dot]
    ring

theorem nativePlane_product (g h : Hei.H 1) :
    nativePlane (g*h) = nativePlane g + nativePlane h := by
  apply Prod.ext <;>
    simp [nativePlane, Hei.mul_x, Hei.mul_y]

theorem native_commutator_eq_neg_ellipticOmega
    (g h : Hei.H 1) :
    Hei.omega g h =
      -P.planeOmega (nativePlane g) (nativePlane h) := by
  simp [Hei.omega, Hei.dot, P.planeOmega, nativePlane]
  ring

/-- This is the genuinely arithmetic same-object group-law weld:
the existing Schrödinger-compatible H(1) law is transported to a central
extension of the ACTUAL elliptic group, with the required centre inversion. -/
theorem toActual_product (g h : Hei.H 1) :
    toActual (g*h) = product (toActual g) (toActual h) := by
  apply ActualEllipticH27.ext
  · change
      -Act.alternatingCenterCoordinate (g*h)
      =
      -Act.alternatingCenterCoordinate g
        + -Act.alternatingCenterCoordinate h
        + 2 * P.ellipticOmega
          (Basis.actualC3SquareAddEquiv (nativePlane g))
          (Basis.actualC3SquareAddEquiv (nativePlane h))
    rw [Act.alternatingCenterCoordinate_mul]
    have hcomm := native_commutator_eq_neg_ellipticOmega g h
    rw [hcomm]
    simp [P.ellipticOmega]
    ring
  · simp only [toActual, product]
    rw [nativePlane_product]
    exact Basis.actualC3SquareAddEquiv.map_add _ _

theorem fromActual_product (g h : ActualEllipticH27) :
    fromActual (product g h) =
      fromActual g * fromActual h := by
  apply toActual_injective
  rw [toActual_fromActual, toActual_product,
    toActual_fromActual, toActual_fromActual]

/-- The map is an equivalence of sets AND a multiplicative isomorphism.
The coefficient pairing on the base is an explicitly normalized alternating
form; identifying it with geometric e₃ still requires its own source. -/
def nativeEllipticH27Equiv : Hei.H 1 ≃ ActualEllipticH27 where
  toFun := toActual
  invFun := fromActual
  left_inv := fromActual_toActual
  right_inv := toActual_fromActual

theorem rankOne_center_sign (z : F3) :
    (toActual (Act.central (n:=1) z)).center = -z := by
  simp [toActual, Act.central, Act.alternatingCenterCoordinate, Hei.dot]

end Integration.OggSSPP2F4ActualEllipticHeisenberg
