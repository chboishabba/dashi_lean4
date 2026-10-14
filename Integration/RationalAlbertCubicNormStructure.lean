import Integration.RationalAlbertNative
import Mathlib

/-!
# Native cubic-norm structure on the rational Albert algebra

This file strengthens the repository-native `H₃(O_Q)` surface from a Jordan
product plus cubic into the standard cubic-norm-structure data

    (J, N, #, T, 1).

All formulas use the same coordinate convention as `RationalAlbertNative`.
The Jordan product is recovered from the adjoint/cross product and trace data,
so later E6/F4 work can state the unit-stabilizer problem on the actual cubic
structure rather than by dimension or root-count matching.
-/

namespace Integration.RationalAlbertCubicNormStructure

open Integration.RationalCayleyDicksonOctonion
open Integration.RationalAlbertNative
open RationalQuaternion RationalOctonion RationalAlbertNative.RationalAlbert

abbrev A27 := RationalAlbertNative.RationalAlbert

/-- Bilinear trace form for `H₃(O_Q)`. -/
def tracePair (X Y : A27) : ℚ :=
  X.diagonal0 * Y.diagonal0 + X.diagonal1 * Y.diagonal1 + X.diagonal2 * Y.diagonal2
    + 2 * (innerO X.off12 Y.off12 + innerO X.off20 Y.off20 + innerO X.off01 Y.off01)

/-- Standard quadratic adjoint for the native Albert coordinate convention. -/
def adjoint (X : A27) : A27 :=
  ⟨ X.diagonal1 * X.diagonal2 - RationalOctonion.normSq X.off12,
    X.diagonal2 * X.diagonal0 - RationalOctonion.normSq X.off20,
    X.diagonal0 * X.diagonal1 - RationalOctonion.normSq X.off01,
    (RationalOctonion.conj X.off01 * RationalOctonion.conj X.off20) + ((-X.diagonal0) • X.off12),
    (RationalOctonion.conj X.off12 * RationalOctonion.conj X.off01) + ((-X.diagonal1) • X.off20),
    (RationalOctonion.conj X.off20 * RationalOctonion.conj X.off12) + ((-X.diagonal2) • X.off01) ⟩

/-- Bilinearized adjoint. -/
def cross (X Y : A27) : A27 :=
  adjoint (X + Y) + (-(adjoint X)) + (-(adjoint Y))

/-- Polarization scalar appearing in the product-recovery formula. -/
def sigma (X Y : A27) : ℚ :=
  trace X * trace Y - tracePair X Y

@[simp] theorem adjoint_unit : adjoint unit = unit := by
  ext <;>
    simp [adjoint, unit, RationalOctonion.normSq,
      RationalOctonion.mul, RationalOctonion.conj,
      RationalQuaternion.mul, RationalQuaternion.conj]

/-- Exact adjoint identity `(x#)# = N(x) x`. -/
theorem adjoint_adjoint (X : A27) :
    adjoint (adjoint X) = cubic X • X := by
  rcases X with ⟨a,b,c,x,y,z⟩
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  rcases x1 with ⟨x10,x11,x12,x13⟩; rcases x2 with ⟨x20,x21,x22,x23⟩
  rcases y1 with ⟨y10,y11,y12,y13⟩; rcases y2 with ⟨y20,y21,y22,y23⟩
  rcases z1 with ⟨z10,z11,z12,z13⟩; rcases z2 with ⟨z20,z21,z22,z23⟩
  ext <;>
    simp [adjoint, cubic, RationalOctonion.normSq, RationalOctonion.mul,
      RationalOctonion.conj, RationalOctonion.realPart,
      RationalQuaternion.mul, RationalQuaternion.conj] <;> ring

/-- Exact cubic polarization identity:
`N(X+tY)=N(X)+t T(X#,Y)+t² T(X,Y#)+t³ N(Y)`. -/
theorem cubic_expansion (X Y : A27) (t : ℚ) :
    cubic (X + t • Y) =
      cubic X + t * tracePair (adjoint X) Y +
        t^2 * tracePair X (adjoint Y) + t^3 * cubic Y := by
  rcases X with ⟨a,b,c,x,y,z⟩; rcases Y with ⟨d,e,f,u,v,w⟩
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  rcases u with ⟨u1,u2⟩; rcases v with ⟨v1,v2⟩; rcases w with ⟨w1,w2⟩
  rcases x1 with ⟨x10,x11,x12,x13⟩; rcases x2 with ⟨x20,x21,x22,x23⟩
  rcases y1 with ⟨y10,y11,y12,y13⟩; rcases y2 with ⟨y20,y21,y22,y23⟩
  rcases z1 with ⟨z10,z11,z12,z13⟩; rcases z2 with ⟨z20,z21,z22,z23⟩
  rcases u1 with ⟨u10,u11,u12,u13⟩; rcases u2 with ⟨u20,u21,u22,u23⟩
  rcases v1 with ⟨v10,v11,v12,v13⟩; rcases v2 with ⟨v20,v21,v22,v23⟩
  rcases w1 with ⟨w10,w11,w12,w13⟩; rcases w2 with ⟨w20,w21,w22,w23⟩
  simp [cubic, tracePair, adjoint, innerO, RationalOctonion.normSq,
    RationalOctonion.mul, RationalOctonion.conj, RationalOctonion.realPart,
    RationalQuaternion.mul, RationalQuaternion.conj] <;> ring

/-- Base-point cross identity `1 × x = T(x)1 - x`. -/
theorem unit_cross (X : A27) :
    cross unit X = (trace X) • unit + (-X) := by
  rcases X with ⟨a,b,c,x,y,z⟩
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  ext <;>
    try { apply RationalOctonion.ext <;> apply RationalQuaternion.ext } <;>
    simp [cross, adjoint, trace, unit, RationalOctonion.normSq,
      RationalOctonion.mul, RationalOctonion.conj,
      RationalQuaternion.mul, RationalQuaternion.conj] <;> ring

/-- The existing native Jordan product is recovered exactly from cubic-norm
structure data. -/
theorem jordan_recovered (X Y : A27) :
    jordanProduct X Y =
      (1/2 : ℚ) •
        (cross X Y + (trace X) • Y + (trace Y) • X +
          (-((sigma X Y) • unit))) := by
  rcases X with ⟨a,b,c,x,y,z⟩; rcases Y with ⟨d,e,f,u,v,w⟩
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  rcases u with ⟨u1,u2⟩; rcases v with ⟨v1,v2⟩; rcases w with ⟨w1,w2⟩
  ext <;>
    try { apply RationalOctonion.ext <;> apply RationalQuaternion.ext } <;>
    simp [jordanProduct, cross, adjoint, sigma, tracePair, trace, unit, innerO,
      halfO, RationalOctonion.normSq, RationalOctonion.mul,
      RationalOctonion.conj, RationalOctonion.realPart,
      RationalQuaternion.mul, RationalQuaternion.conj] <;> ring

structure Boundary where
  adjointTyped : Bool
  tracePairTyped : Bool
  adjointIdentitySourceWritten : Bool
  cubicExpansionSourceWritten : Bool
  unitCrossIdentitySourceWritten : Bool
  jordanRecoveredFromCubicData : Bool
  cubicSymmetryUnitStabilizerEqualsJordanAutPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  adjointTyped := true
  tracePairTyped := true
  adjointIdentitySourceWritten := true
  cubicExpansionSourceWritten := true
  unitCrossIdentitySourceWritten := true
  jordanRecoveredFromCubicData := true
  cubicSymmetryUnitStabilizerEqualsJordanAutPaid := false

end Integration.RationalAlbertCubicNormStructure
