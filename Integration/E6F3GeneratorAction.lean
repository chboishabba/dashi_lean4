import Integration.E6F3ExteriorSquareRecognition
import Mathlib

/-!
# Generator-level PGSp4(3) / W(E6) bridge over F3

The six explicit four-dimensional lifts below are multiplier-minus-one
symplectic similitudes.  On isotropic pairs their exterior-square action agrees
with the primitive five-coordinate action, and the explicit diagonalizing map
intertwines that action with six reduced E6 simple-reflection matrices.

This pays the generator-level action square only.  Full 51,840-element closure
and the projective ±I kernel are kept as separate fail-closed receipts.
-/

namespace Integration.E6F3GeneratorAction

open Integration.E6F3ExteriorSquareRecognition

structure Matrix4 where
  r1 : F3Four
  r2 : F3Four
  r3 : F3Four
  r4 : F3Four
  deriving DecidableEq, Repr

structure Matrix5 where
  r1 : StandardFive
  r2 : StandardFive
  r3 : StandardFive
  r4 : StandardFive
  r5 : StandardFive
  deriving DecidableEq, Repr


def dot4 (a b : F3Four) : F3 :=
  a.x1*b.x1 + a.x2*b.x2 + a.x3*b.x3 + a.x4*b.x4

def dot5 (a b : StandardFive) : F3 :=
  a.z1*b.z1 + a.z2*b.z2 + a.z3*b.z3 + a.z4*b.z4 + a.z5*b.z5

def apply4 (m : Matrix4) (v : F3Four) : F3Four :=
  ⟨dot4 m.r1 v, dot4 m.r2 v, dot4 m.r3 v, dot4 m.r4 v⟩

def apply5 (m : Matrix5) (v : StandardFive) : StandardFive :=
  ⟨dot5 m.r1 v, dot5 m.r2 v, dot5 m.r3 v, dot5 m.r4 v, dot5 m.r5 v⟩

def primitiveAsFive (p : PrimitiveBivector5) : StandardFive :=
  ⟨p.p12,p.p13,p.p14,p.p23,p.p24⟩

def fiveAsPrimitive (z : StandardFive) : PrimitiveBivector5 :=
  ⟨z.z1,z.z2,z.z3,z.z4,z.z5⟩

def applyPrimitive5 (m : Matrix5) (p : PrimitiveBivector5) : PrimitiveBivector5 :=
  fiveAsPrimitive (apply5 m (primitiveAsFive p))

inductive SimpleE6Generator
  | s0 | s1 | s2 | s3 | s4 | s5
  deriving DecidableEq, Fintype, Repr

open SimpleE6Generator


def v4 (a b c d : F3) : F3Four := ⟨a,b,c,d⟩
def v5 (a b c d e : F3) : StandardFive := ⟨a,b,c,d,e⟩

/-- Explicit 4x4 similitude lifts. -/
def liftMatrix : SimpleE6Generator → Matrix4
  | s0 => ⟨v4 (-1) 0 (-1) (-1), v4 0 (-1) (-1) 1,
           v4 1 1 1 0, v4 1 (-1) 0 1⟩
  | s1 => ⟨v4 0 0 (-1) 0, v4 0 0 0 1,
           v4 1 0 0 0, v4 0 (-1) 0 0⟩
  | s2 => ⟨v4 0 0 1 1, v4 0 0 1 0,
           v4 0 (-1) 0 0, v4 (-1) 1 0 0⟩
  | s3 => ⟨v4 0 0 (-1) 1, v4 0 0 (-1) (-1),
           v4 (-1) (-1) 0 0, v4 1 (-1) 0 0⟩
  | s4 => ⟨v4 1 0 (-1) (-1), v4 0 1 0 (-1),
           v4 (-1) 1 (-1) 0, v4 0 (-1) 0 (-1)⟩
  | s5 => ⟨v4 0 0 1 1, v4 0 0 (-1) 1,
           v4 1 (-1) 0 0, v4 1 1 0 0⟩

/-- Exterior-square matrices in primitive Plücker coordinates. -/
def primitiveMatrix : SimpleE6Generator → Matrix5
  | s0 => ⟨v5 0 1 (-1) (-1) (-1), v5 1 0 1 1 1,
           v5 (-1) 1 0 (-1) (-1), v5 (-1) 1 (-1) 0 (-1),
           v5 (-1) 1 (-1) (-1) 0⟩
  | s1 => ⟨v5 1 0 0 0 0, v5 0 1 0 0 0,
           v5 0 0 0 (-1) 0, v5 0 0 (-1) 0 0, v5 0 0 0 0 1⟩
  | s2 => ⟨v5 1 0 0 0 0, v5 0 0 0 1 1,
           v5 0 1 1 (-1) (-1), v5 0 0 0 1 0, v5 0 1 0 (-1) 0⟩
  | s3 => ⟨v5 1 0 0 0 0, v5 0 (-1) 1 (-1) 1,
           v5 0 1 (-1) (-1) 1, v5 0 (-1) (-1) (-1) (-1),
           v5 0 1 1 (-1) (-1)⟩
  | s4 => ⟨v5 0 0 (-1) 1 1, v5 (-1) 1 (-1) 1 1,
           v5 1 0 (-1) (-1) (-1), v5 (-1) 0 (-1) (-1) 1,
           v5 0 0 0 0 1⟩
  | s5 => ⟨v5 1 0 0 0 0, v5 0 (-1) (-1) 1 1,
           v5 0 (-1) (-1) (-1) (-1), v5 0 1 (-1) (-1) 1,
           v5 0 1 (-1) 1 (-1)⟩

/-- Reduced E6 simple reflections in the standard five-coordinate model. -/
def weylMatrix : SimpleE6Generator → Matrix5
  | s0 => ⟨v5 1 0 0 0 0, v5 0 1 0 0 0, v5 0 0 1 0 0,
           v5 0 0 0 0 1, v5 0 0 0 1 0⟩
  | s1 => ⟨v5 1 0 0 0 0, v5 0 1 0 0 0, v5 0 0 0 1 0,
           v5 0 0 1 0 0, v5 0 0 0 0 1⟩
  | s2 => ⟨v5 0 0 (-1) 0 0, v5 0 1 0 0 0, v5 (-1) 0 0 0 0,
           v5 0 0 0 1 0, v5 0 0 0 0 1⟩
  | s3 => ⟨v5 0 (-1) 0 0 0, v5 (-1) 0 0 0 0, v5 0 0 1 0 0,
           v5 0 0 0 1 0, v5 0 0 0 0 1⟩
  | s4 => ⟨v5 0 (-1) 1 1 1, v5 (-1) 0 1 1 1,
           v5 1 1 0 (-1) (-1), v5 1 1 (-1) 0 (-1),
           v5 1 1 (-1) (-1) 0⟩
  | s5 => ⟨v5 0 1 0 0 0, v5 1 0 0 0 0, v5 0 0 1 0 0,
           v5 0 0 0 1 0, v5 0 0 0 0 1⟩


def liftAction (g : SimpleE6Generator) : F3Four → F3Four := apply4 (liftMatrix g)
def primitiveAction (g : SimpleE6Generator) : PrimitiveBivector5 → PrimitiveBivector5 :=
  applyPrimitive5 (primitiveMatrix g)
def weylAction (g : SimpleE6Generator) : StandardFive → StandardFive := apply5 (weylMatrix g)

/-- Every explicit lift has symplectic multiplier -1. -/
theorem multiplier_minus_one_all :
    ∀ g : SimpleE6Generator, ∀ u v : F3Four,
      symplectic4 (liftAction g u) (liftAction g v) = -(symplectic4 u v) := by
  native_decide

/-- The primitive exterior-square chart applies exactly on isotropic pairs. -/
theorem wedge_covariance_all :
    ∀ g : SimpleE6Generator, ∀ u v : F3Four,
      symplectic4 u v = 0 →
      wedgePrimitiveCoordinates (liftAction g u) (liftAction g v) =
        primitiveAction g (wedgePrimitiveCoordinates u v) := by
  native_decide

/-- The diagonalizing map intertwines every one of the six generator actions. -/
theorem standard_intertwining_all :
    ∀ g : SimpleE6Generator, ∀ p : PrimitiveBivector5,
      primitiveToStandard (primitiveAction g p) =
        weylAction g (primitiveToStandard p) := by
  native_decide

/-- The six reduced E6 generator matrices preserve the standard quadratic form. -/
theorem weyl_quadratic_preserved_all :
    ∀ g : SimpleE6Generator, ∀ z : StandardFive,
      standardQ (weylAction g z) = standardQ z := by
  native_decide

structure Boundary where
  sixExplicitSimilitudeLifts : Bool
  multiplierMinusOnePaid : Bool
  isotropicWedgeCovariancePaid : Bool
  standardWeylIntertwiningPaid : Bool
  standardQuadraticPreserved : Bool
  groupClosureOrder51840Paid : Bool
  projectiveKernelPlusMinusIPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  sixExplicitSimilitudeLifts := true
  multiplierMinusOnePaid := true
  isotropicWedgeCovariancePaid := true
  standardWeylIntertwiningPaid := true
  standardQuadraticPreserved := true
  groupClosureOrder51840Paid := false
  projectiveKernelPlusMinusIPaid := false

end Integration.E6F3GeneratorAction
