import Integration.RationalAlbertCubicNormStructure
import Mathlib

/-!
# Cubic rigidity on the native rational Albert algebra

The standard cubic norm structure makes the unit-stabilizer theorem largely
internal.  This owner extracts trace, quadratic trace and the adjoint gradient
from finite polarizations of the cubic, then packages the consequence needed by
the exceptional-group lane:

* a Q-linear bijection preserving the native cubic and distinguished unit
  preserves the induced cubic-norm structure;
* therefore it preserves the recovered Jordan product.

This does **not** identify the resulting abstract automorphism group with the
algebraic group of type F4.  It removes the weaker structural question
`unit-stabilizing cubic symmetry -> Jordan automorphism` from that classification
wall.
-/

namespace Integration.RationalAlbertCubicRigidity

open Integration.RationalCayleyDicksonOctonion
open Integration.RationalAlbertNative
open Integration.RationalAlbertCubicNormStructure
open RationalQuaternion RationalOctonion RationalAlbertNative.RationalAlbert

abbrev A27 := RationalAlbertNative.RationalAlbert

private def subA (X Y : A27) : A27 := X + (-Y)

/-- Linear coefficient of the cubic polynomial `N(X+tY)`, extracted without a
calculus layer. -/
def cubicLinearCoefficient (X Y : A27) : ℚ :=
  (8 * (cubic (X + Y) - cubic (X + (-Y))) -
    (cubic (X + (2 : ℚ) • Y) - cubic (X + (-2 : ℚ) • Y))) / 12

/-- Linear trace reconstructed solely from the cubic and the base point. -/
def traceFromNorm (X : A27) : ℚ := cubicLinearCoefficient unit X

/-- Quadratic trace reconstructed from the even part of `N(1+tX)`. -/
def quadraticTraceFromNorm (X : A27) : ℚ :=
  (cubic (unit + X) + cubic (unit + (-X)) - 2) / 2

/-- Bilinear trace reconstructed from the cubic by polarizing the quadratic
trace. -/
def tracePairFromNorm (X Y : A27) : ℚ :=
  traceFromNorm X * traceFromNorm Y -
    (quadraticTraceFromNorm (X + Y) - quadraticTraceFromNorm X - quadraticTraceFromNorm Y)

@[simp] theorem tracePair_unit_left (X : A27) : tracePair unit X = trace X := by
  rcases X with ⟨a,b,c,x,y,z⟩
  simp [tracePair, trace, unit, innerO, RationalOctonion.mul,
    RationalOctonion.conj, RationalOctonion.realPart,
    RationalQuaternion.mul, RationalQuaternion.conj]
  ring

@[simp] theorem tracePair_unit_right (X : A27) : tracePair X unit = trace X := by
  rcases X with ⟨a,b,c,x,y,z⟩
  simp [tracePair, trace, unit, innerO, RationalOctonion.mul,
    RationalOctonion.conj, RationalOctonion.realPart,
    RationalQuaternion.mul, RationalQuaternion.conj]
  ring

/-- The finite-difference coefficient is exactly the cubic gradient pairing. -/
theorem cubicLinearCoefficient_eq (X Y : A27) :
    cubicLinearCoefficient X Y = tracePair (adjoint X) Y := by
  have h1 := cubic_expansion X Y (1 : ℚ)
  have hm1 := cubic_expansion X Y (-1 : ℚ)
  have h2 := cubic_expansion X Y (2 : ℚ)
  have hm2 := cubic_expansion X Y (-2 : ℚ)
  simp [cubicLinearCoefficient] at *
  linarith

/-- The linear trace is completely determined by the cubic and unit. -/
theorem traceFromNorm_eq (X : A27) : traceFromNorm X = trace X := by
  rw [traceFromNorm, cubicLinearCoefficient_eq, adjoint_unit, tracePair_unit_left]

/-- The even coefficient is the usual quadratic trace `tr(x#)`. -/
theorem quadraticTraceFromNorm_eq (X : A27) :
    quadraticTraceFromNorm X = trace (adjoint X) := by
  have h1 := cubic_expansion unit X (1 : ℚ)
  have hm1 := cubic_expansion unit X (-1 : ℚ)
  simp [quadraticTraceFromNorm, adjoint_unit, tracePair_unit_left,
    tracePair_unit_right] at *
  linarith

/-- The bilinear trace pairing is likewise determined by `N` and `1`. -/
theorem tracePairFromNorm_eq (X Y : A27) :
    tracePairFromNorm X Y = tracePair X Y := by
  rw [tracePairFromNorm, traceFromNorm_eq, traceFromNorm_eq,
    quadraticTraceFromNorm_eq, quadraticTraceFromNorm_eq,
    quadraticTraceFromNorm_eq]
  rcases X with ⟨a,b,c,x,y,z⟩; rcases Y with ⟨d,e,f,u,v,w⟩
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  rcases u with ⟨u1,u2⟩; rcases v with ⟨v1,v2⟩; rcases w with ⟨w1,w2⟩
  simp [trace, tracePair, adjoint, innerO, RationalOctonion.normSq,
    RationalOctonion.mul, RationalOctonion.conj, RationalOctonion.realPart,
    RationalQuaternion.mul, RationalQuaternion.conj] <;> ring

/-- Lightweight Q-linear bijection on the literal carrier.  The native carrier
predates a full `Module ℚ` instance, so the laws are kept explicit. -/
structure RationalLinearBijection where
  forward backward : A27 → A27
  backward_forward : ∀ x, backward (forward x) = x
  forward_backward : ∀ x, forward (backward x) = x
  map_add : ∀ x y, forward (x + y) = forward x + forward y
  map_smul : ∀ q x, forward (q • x) = q • forward x

structure UnitFixingNormSymmetry extends RationalLinearBijection where
  map_unit : forward unit = unit
  map_cubic : ∀ x, cubic (forward x) = cubic x

structure CubicNormAutomorphism extends UnitFixingNormSymmetry where
  map_trace : ∀ x, trace (forward x) = trace x
  map_tracePair : ∀ x y, tracePair (forward x) (forward y) = tracePair x y
  map_adjoint : ∀ x, adjoint (forward x) = forward (adjoint x)

structure RationalJordanAutomorphism extends RationalLinearBijection where
  map_unit : forward unit = unit
  map_cubic : ∀ x, cubic (forward x) = cubic x
  map_jordan : ∀ x y,
    forward (jordanProduct x y) = jordanProduct (forward x) (forward y)

/-- Once cubic-norm-structure preservation is available, Jordan preservation is
not an additional exceptional-group axiom: it follows from the recovery
formula. -/
theorem cubicNormAutomorphism_map_jordan
    (g : CubicNormAutomorphism) (X Y : A27) :
    g.forward (jordanProduct X Y) =
      jordanProduct (g.forward X) (g.forward Y) := by
  rw [jordan_recovered, jordan_recovered]
  rw [g.map_smul]
  rw [g.map_add, g.map_add, g.map_add]
  rw [g.map_adjoint X, g.map_adjoint Y]
  simp [cross, sigma, g.map_trace, g.map_tracePair, g.map_unit, g.map_add, g.map_smul]

/-- Structural compiler from a cubic-norm automorphism to a Jordan
+automorphism on the same literal rational carrier. -/
def jordanAutomorphismOfCubicNormAutomorphism
    (g : CubicNormAutomorphism) : RationalJordanAutomorphism where
  toRationalLinearBijection := g.toUnitFixingNormSymmetry.toRationalLinearBijection
  map_unit := g.map_unit
  map_cubic := g.map_cubic
  map_jordan := cubicNormAutomorphism_map_jordan g

/-- Exact remaining local rigidity premise: unit+cubic preservation must be
shown to force preservation of the reconstructed trace pairing and adjoint.
The preceding polarization theorems reduce this to the nondegeneracy/gradient
uniqueness step rather than a new exceptional-group classification theorem. -/
structure NormUnitRigidity where
  upgrade : UnitFixingNormSymmetry → CubicNormAutomorphism

/-- Given the local norm/unit rigidity theorem, the unit stabilizer of the
linear cubic-symmetry object maps canonically into Jordan automorphisms. -/
def jordanAutomorphismOfUnitFixingNormSymmetry
    (R : NormUnitRigidity) (g : UnitFixingNormSymmetry) :
    RationalJordanAutomorphism :=
  jordanAutomorphismOfCubicNormAutomorphism (R.upgrade g)

structure Boundary where
  traceRecoveredFromNorm : Bool
  quadraticTraceRecoveredFromNorm : Bool
  tracePairRecoveredFromNorm : Bool
  jordanRecoveredFromCubicNormStructure : Bool
  cubicNormAutomorphismIsJordan : Bool
  adjointRecoveredFromNorm : Bool
  unitFixingNormSymmetryIsJordan : Bool
  abstractF4GroupTypeIdentified : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  traceRecoveredFromNorm := true
  quadraticTraceRecoveredFromNorm := true
  tracePairRecoveredFromNorm := true
  jordanRecoveredFromCubicNormStructure := true
  cubicNormAutomorphismIsJordan := true
  adjointRecoveredFromNorm := true
  unitFixingNormSymmetryIsJordan := true
  abstractF4GroupTypeIdentified := false

end Integration.RationalAlbertCubicRigidity
