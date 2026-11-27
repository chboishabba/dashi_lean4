import Integration.RationalCayleyDicksonOctonion
import Mathlib

/-!
# Native rational Albert algebra coordinates

Lean mirror of the repo-native Agda `RationalAlbertHermitianCubicExact` and
`RationalAlbertJordanProductExact` owners.

Carrier convention:

    [ a       z       conj(y) ]
    [ conj(z) b       x       ]
    [ y       conj(x) c       ]

with `x = off12`, `y = off20`, `z = off01`.
-/

namespace Integration.RationalAlbertNative

open Integration.RationalCayleyDicksonOctonion
open RationalOctonion

structure RationalAlbert where
  diagonal0 diagonal1 diagonal2 : ℚ
  off12 off20 off01 : RationalOctonion
  deriving DecidableEq, Repr

namespace RationalAlbert

instance : Zero RationalAlbert := ⟨⟨0,0,0,0,0,0⟩⟩
instance : Add RationalAlbert := ⟨fun x y =>
  ⟨x.diagonal0+y.diagonal0,x.diagonal1+y.diagonal1,x.diagonal2+y.diagonal2,
   x.off12+y.off12,x.off20+y.off20,x.off01+y.off01⟩⟩
instance : Neg RationalAlbert := ⟨fun x =>
  ⟨-x.diagonal0,-x.diagonal1,-x.diagonal2,-x.off12,-x.off20,-x.off01⟩⟩
instance : SMul ℚ RationalAlbert := ⟨fun r x =>
  ⟨r*x.diagonal0,r*x.diagonal1,r*x.diagonal2,r • x.off12,r • x.off20,r • x.off01⟩⟩

@[ext] theorem ext {x y : RationalAlbert}
    (h0 : x.diagonal0=y.diagonal0) (h1 : x.diagonal1=y.diagonal1)
    (h2 : x.diagonal2=y.diagonal2) (hx : x.off12=y.off12)
    (hy : x.off20=y.off20) (hz : x.off01=y.off01) : x=y := by
  cases x; cases y; simp_all

def unit : RationalAlbert := ⟨1,1,1,0,0,0⟩

def trace (x : RationalAlbert) : ℚ := x.diagonal0+x.diagonal1+x.diagonal2

/-- Standard rank-three cubic norm/determinant. -/
def cubic (u : RationalAlbert) : ℚ :=
  u.diagonal0*u.diagonal1*u.diagonal2
    - u.diagonal0 * RationalOctonion.normSq u.off12
    - u.diagonal1 * RationalOctonion.normSq u.off20
    - u.diagonal2 * RationalOctonion.normSq u.off01
    + 2 * RationalOctonion.realPart ((u.off12*u.off20)*u.off01)

@[simp] theorem trace_unit : trace unit = 3 := by norm_num [trace,unit]
@[simp] theorem cubic_unit : cubic unit = 1 := by norm_num [cubic,unit,RationalOctonion.normSq]
@[simp] theorem cubic_zero : cubic 0 = 0 := by norm_num [cubic,RationalOctonion.normSq]

/-- Polarized octonion inner product `Re(x conj y)`. -/
def innerO (x y : RationalOctonion) : ℚ :=
  RationalOctonion.realPart (x * RationalOctonion.conj y)

def halfO (x : RationalOctonion) : RationalOctonion := (1/2 : ℚ) • x

/-- Direct coordinate formula for `(XY+YX)/2`. -/
def jordanProduct (X Y : RationalAlbert) : RationalAlbert :=
  let a:=X.diagonal0; let b:=X.diagonal1; let c:=X.diagonal2
  let x:=X.off12; let y:=X.off20; let z:=X.off01
  let d:=Y.diagonal0; let e:=Y.diagonal1; let f:=Y.diagonal2
  let u:=Y.off12; let v:=Y.off20; let w:=Y.off01
  ⟨ a*d + innerO z w + innerO y v,
    b*e + innerO z w + innerO x u,
    c*f + innerO y v + innerO x u,
    halfO ((RationalOctonion.conj z * RationalOctonion.conj v) + b • u + f • x
      + (RationalOctonion.conj w * RationalOctonion.conj y) + e • x + c • u),
    halfO (d • y + (RationalOctonion.conj x * RationalOctonion.conj w) + c • v
      + a • v + (RationalOctonion.conj u * RationalOctonion.conj z) + f • y),
    halfO (a • w + e • z + (RationalOctonion.conj y * RationalOctonion.conj u)
      + d • z + b • w + (RationalOctonion.conj v * RationalOctonion.conj x)) ⟩

def square (x : RationalAlbert) : RationalAlbert := jordanProduct x x

/-- Source-level exact coordinate commutativity proof. -/
theorem jordan_comm (X Y : RationalAlbert) : jordanProduct X Y = jordanProduct Y X := by
  rcases X with ⟨a,b,c,x,y,z⟩; rcases Y with ⟨d,e,f,u,v,w⟩
  ext <;>
    rcases x with ⟨x1,x2⟩ <;> rcases y with ⟨y1,y2⟩ <;> rcases z with ⟨z1,z2⟩ <;>
    rcases u with ⟨u1,u2⟩ <;> rcases v with ⟨v1,v2⟩ <;> rcases w with ⟨w1,w2⟩ <;>
    try { apply RationalOctonion.ext <;> apply RationalQuaternion.ext } <;>
    simp [jordanProduct, innerO, halfO, RationalOctonion.mul, RationalOctonion.conj,
      RationalOctonion.realPart, RationalQuaternion.mul, RationalQuaternion.conj] <;> ring

/-- Exact right unit law. -/
theorem jordan_unit_right (X : RationalAlbert) : jordanProduct X unit = X := by
  rcases X with ⟨a,b,c,x,y,z⟩
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  ext <;> try { apply RationalOctonion.ext <;> apply RationalQuaternion.ext } <;>
    simp [jordanProduct, innerO, halfO, unit, RationalOctonion.mul, RationalOctonion.conj,
      RationalOctonion.realPart, RationalQuaternion.mul, RationalQuaternion.conj] <;> ring

theorem jordan_unit_left (X : RationalAlbert) : jordanProduct unit X = X := by
  rw [jordan_comm]
  exact jordan_unit_right X

/-- Exceptional Jordan identity on the explicit rational coordinate product.
This is intentionally a direct polynomial proof, not associative-matrix reasoning. -/
theorem jordan_identity (X Y : RationalAlbert) :
    jordanProduct (jordanProduct (square X) Y) X =
      jordanProduct (square X) (jordanProduct Y X) := by
  rcases X with ⟨a,b,c,x,y,z⟩; rcases Y with ⟨d,e,f,u,v,w⟩
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  rcases u with ⟨u1,u2⟩; rcases v with ⟨v1,v2⟩; rcases w with ⟨w1,w2⟩
  ext <;> try { apply RationalOctonion.ext <;> apply RationalQuaternion.ext } <;>
    simp [square, jordanProduct, innerO, halfO, RationalOctonion.mul,
      RationalOctonion.conj, RationalOctonion.realPart,
      RationalQuaternion.mul, RationalQuaternion.conj] <;> ring

end RationalAlbert

structure NativeBoundary where
  rationalOctonionCarrierPaid : Bool
  rationalAlbertCarrierPaid : Bool
  coordinateDimension3Plus3Times8 : Bool
  standardCubicPaid : Bool
  coordinateJordanProductPaid : Bool
  commutativitySourceWritten : Bool
  unitLawsSourceWritten : Bool
  jordanIdentitySourceWritten : Bool
  fullF4RecognitionPaid : Bool
  deriving Repr

def canonicalBoundary : NativeBoundary where
  rationalOctonionCarrierPaid := true
  rationalAlbertCarrierPaid := true
  coordinateDimension3Plus3Times8 := true
  standardCubicPaid := true
  coordinateJordanProductPaid := true
  commutativitySourceWritten := true
  unitLawsSourceWritten := true
  jordanIdentitySourceWritten := true
  fullF4RecognitionPaid := false

end Integration.RationalAlbertNative
