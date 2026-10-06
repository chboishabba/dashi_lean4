import Integration.E6F3ExteriorSquare
import Integration.E6Mod3WeylAction
import Mathlib

/-!
# PGSp4(3) lifts of the E6 mod-3 Weyl generators

Local exact enumeration solved six 4x4 symplectic-similitude preimages of the
already-formalized five-dimensional E6 simple reflections.  This file encodes
those preimages directly and kernel-checks their finite action properties.

The lifts have similitude multiplier -1 = 2 in F3 and square to -I, hence are
involutions after quotienting by the central {±I}.  Their primitive exterior-
square action intertwines the existing E6 five-dimensional reflection action on
symplectically isotropic decomposable bivectors.
-/

namespace Integration.E6PGSp4ExteriorSquare

open Integration.E6F3ExteriorSquare
open Integration.E6Mod3QuadraticBridge
open Integration.E6Mod3WeylAction

/-- Scalar multiplication on the four-trit vector space. -/
def scale4 (a : F3) (x : V4) : V4 := fun i => a * x i

def neg4 (x : V4) : V4 := scale4 2 x

/-- Exact 4x4 similitude lifts, one for each existing E6 simple reflection.
Rows are the matrices found by local exhaustive search against the induced
primitive-exterior-square action. -/
def liftSimple : E6SimpleReflection → V4 → V4
  | .s0, x => ![
      x 0 + x 2 + x 3,
      x 1 + x 2 + 2*x 3,
      2*x 0 + 2*x 1 + 2*x 2,
      2*x 0 + x 1 + 2*x 3]
  | .s1, x => ![
      2*x 0 + 2*x 2,
      2*x 1 + x 2 + 2*x 3,
      2*x 0 + x 2,
      2*x 0 + 2*x 1 + x 3]
  | .s2, x => ![
      2*x 0 + x 2,
      2*x 1 + 2*x 2 + x 3,
      x 0 + x 2,
      x 0 + x 1 + x 3]
  | .s3, x => ![
      x 2 + 2*x 3,
      x 2 + x 3,
      x 0 + x 1,
      2*x 0 + x 1]
  | .s4, x => ![
      2*x 3,
      2*x 2 + x 3,
      x 0 + x 1,
      x 0]
  | .s5, x => ![
      x 2 + x 3,
      2*x 2 + x 3,
      x 0 + 2*x 1,
      x 0 + x 1]

/-- Every lift is a symplectic similitude of multiplier 2 = -1. -/
theorem lift_simple_multiplier_minus_one :
    ∀ s u v, omega (liftSimple s u) (liftSimple s v) = 2 * omega u v := by
  native_decide

/-- Each lift squares to the central scalar -I. -/
theorem lift_simple_square_neg_identity :
    ∀ s x, liftSimple s (liftSimple s x) = neg4 x := by
  native_decide

/-- Projective braid sign.  A value 2 means the two 4x4 words differ by -I. -/
def braidSign : E6SimpleReflection → E6SimpleReflection → F3
  | .s0, .s2 | .s2, .s0 => 2
  | .s1, .s3 | .s3, .s1 => 2
  | .s2, .s3 | .s3, .s2 => 1
  | .s3, .s4 | .s4, .s3 => 1
  | .s4, .s5 | .s5, .s4 => 1
  | _, _ => 1

/-- Adjacent E6 braid relations hold modulo the central {±I}. -/
theorem lift_adjacent_projective_braid :
    ∀ i j,
      coxeterAdjacent i j = true →
      ∀ x,
        liftSimple i (liftSimple j (liftSimple i x)) =
          scale4 (braidSign i j)
            (liftSimple j (liftSimple i (liftSimple j x))) := by
  native_decide

/-- Distinct non-adjacent generators commute projectively; for this explicit
choice of lifts the two words differ by the central scalar -I. -/
theorem lift_nonadjacent_projective_commute :
    ∀ i j,
      i ≠ j → coxeterAdjacent i j = false →
      ∀ x,
        liftSimple i (liftSimple j x) =
          neg4 (liftSimple j (liftSimple i x)) := by
  native_decide

/-- Coordinate bridge to the already-existing E6 standardized five-carrier. -/
def toE6Five (z : V5) : F3Five := ⟨z 0, z 1, z 2, z 3, z 4⟩

def fromE6Five (z : F3Five) : V5 := ![z.z0, z.z1, z.z2, z.z3, z.z4]

theorem e6Five_left (z : V5) : fromE6Five (toE6Five z) = z := by
  funext i
  fin_cases i <;> rfl

theorem e6Five_right (z : F3Five) : toE6Five (fromE6Five z) = z := by
  cases z
  rfl

def e6FiveEquiv : V5 ≃ F3Five where
  toFun := toE6Five
  invFun := fromE6Five
  left_inv := e6Five_left
  right_inv := e6Five_right

/-- The two standard five-dimensional quadratic definitions are literally the
same after the coordinate bridge. -/
theorem standard_quadratic_agrees :
    ∀ z : V5, standardQuadratic (toE6Five z) = qStandard z := by
  native_decide

/-- Existing reduced E6 reflection transported onto the function-valued V5. -/
def reflectV5 (s : E6SimpleReflection) (z : V5) : V5 :=
  fromE6Five (reflectStandard s (toE6Five z))

/-- The exact generator-level exterior-square intertwiner.

The premise is essential: the five-coordinate primitive chart represents the
kernel of symplectic contraction, so a decomposable wedge enters it precisely
on the isotropic/Lagrangian locus. -/
theorem exterior_square_intertwines_e6_reflection :
    ∀ s u v,
      omega u v = 0 →
      primitiveToStandard (wedgePrimitive (liftSimple s u) (liftSimple s v)) =
        reflectV5 s (primitiveToStandard (wedgePrimitive u v)) := by
  native_decide

/-- A simple lift preserves the isotropic-pair condition. -/
theorem lift_preserves_isotropy :
    ∀ s u v, omega u v = 0 → omega (liftSimple s u) (liftSimple s v) = 0 := by
  intro s u v h
  rw [lift_simple_multiplier_minus_one, h]
  simp

/-- Existing E6 reflections act on the standard null cone as well as Q=2. -/
def reflectStandardNull (s : E6SimpleReflection) (z : StandardNull) : StandardNull :=
  ⟨reflectV5 s z.1, by
    constructor
    · intro hz
      apply z.2.1
      have hInv := simple_reflections_are_involutions s (toE6Five z.1)
      have hBridge : toE6Five (reflectV5 s z.1) =
          reflectStandard s (toE6Five z.1) := by
        simp [reflectV5, toE6Five, fromE6Five]
      rw [hz] at hBridge
      have : reflectStandard s (toE6Five z.1) = 0 := by
        simpa using hBridge.symm
      have := congrArg (reflectStandard s) this
      simpa using hInv.symm.trans this
    · have hq := simple_reflections_preserve_quadratic s (toE6Five z.1)
      rw [standard_quadratic_agrees] at hq
      have hq' : standardQuadratic (toE6Five (reflectV5 s z.1)) = qStandard (reflectV5 s z.1) :=
        standard_quadratic_agrees (reflectV5 s z.1)
      have hbridge : toE6Five (reflectV5 s z.1) = reflectStandard s (toE6Five z.1) := by
        simp [reflectV5, toE6Five, fromE6Five]
      rw [hbridge] at hq'
      rw [← hq', hq, z.2.2]⟩

inductive RawT4VectorOrbitIsNullOrbit : Prop

theorem rawT4VectorOrbitNotPromoted : ¬ RawT4VectorOrbitIsNullOrbit := by
  intro h
  cases h

/-- Local Python closed the generated projective similitude image at 51,840 and
found exact matrix-set equality with the generated E6 five-dimensional image.
This file pays the stronger generator-level intertwiner but keeps full closure
cardinality as a separate finite-group theorem obligation. -/
def pythonGeneratedProjectiveImageOrder : Nat := 51840

def pythonGeneratedMatrixSymmetricDifference : Nat := 0

structure Boundary where
  sixAntiSymplecticLiftsTyped : Bool
  multiplierMinusOnePaid : Bool
  projectiveInvolutionsPaid : Bool
  projectiveCoxeterRelationsPaid : Bool
  exteriorSquareIntertwiningPaid : Bool
  standardNullActionTyped : Bool
  pythonGeneratedImageOrderRecorded : Bool
  pythonMatrixEqualityRecorded : Bool
  fullGeneratedGroupOrderKernelProvedHere : Bool
  rawT4VectorOrbitIdentifiedWithNullOrbit : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  sixAntiSymplecticLiftsTyped := true
  multiplierMinusOnePaid := true
  projectiveInvolutionsPaid := true
  projectiveCoxeterRelationsPaid := true
  exteriorSquareIntertwiningPaid := true
  standardNullActionTyped := true
  pythonGeneratedImageOrderRecorded := true
  pythonMatrixEqualityRecorded := true
  fullGeneratedGroupOrderKernelProvedHere := false
  rawT4VectorOrbitIdentifiedWithNullOrbit := false

end Integration.E6PGSp4ExteriorSquare
