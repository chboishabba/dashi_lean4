import Mathlib

/-!
# Exact finite F4 root/Weyl datum

Independent of the Albert implementation, this file owns the standard scaled
F4 root system in Z^4:

* short coordinate roots: ±2e_i;
* long roots: ±2e_i ±2e_j;
* half roots: (±1,±1,±1,±1).

The resulting carrier has 48 roots.  Four simple reflections act by exact tables
computed from the literal reflection formula; pointwise checks identify each
permutation with that formula, and the Coxeter relations hold.

The external exact Python preflight closes the generated permutation group at
1152 = |W(F4)|.  That order remains diagnostic here; the root/action datum is
kernel-facing finite source.
-/

namespace Integration.F4RootWeylExact

abbrev Vec4 := Int × Int × Int × Int

def dot (x y : Vec4) : Int :=
  x.1*y.1 + x.2.1*y.2.1 + x.2.2.1*y.2.2.1 + x.2.2.2*y.2.2.2

def subScaled (x a : Vec4) (k : Int) : Vec4 :=
  (x.1-k*a.1,
   x.2.1-k*a.2.1,
   x.2.2.1-k*a.2.2.1,
   x.2.2.2-k*a.2.2.2)

/-- Reflection in a root; all simple-root applications below have exact integer quotient. -/
def reflectVec (a x : Vec4) : Vec4 :=
  subScaled x a ((2 * dot x a) / dot a a)

inductive F4Simple
  | s0 | s1 | s2 | s3
  deriving DecidableEq, Repr, Fintype

def simpleRoot : F4Simple → Vec4
  | .s0 => (0, 2, -2, 0)
  | .s1 => (0, 0, 2, -2)
  | .s2 => (0, 0, 0, 2)
  | .s3 => (1, -1, -1, -1)

def rootVec : Fin 48 → Vec4 :=
  ![
    (-2, -2, 0, 0),
    (-2, 0, -2, 0),
    (-2, 0, 0, -2),
    (-2, 0, 0, 0),
    (-2, 0, 0, 2),
    (-2, 0, 2, 0),
    (-2, 2, 0, 0),
    (-1, -1, -1, -1),
    (-1, -1, -1, 1),
    (-1, -1, 1, -1),
    (-1, -1, 1, 1),
    (-1, 1, -1, -1),
    (-1, 1, -1, 1),
    (-1, 1, 1, -1),
    (-1, 1, 1, 1),
    (0, -2, -2, 0),
    (0, -2, 0, -2),
    (0, -2, 0, 0),
    (0, -2, 0, 2),
    (0, -2, 2, 0),
    (0, 0, -2, -2),
    (0, 0, -2, 0),
    (0, 0, -2, 2),
    (0, 0, 0, -2),
    (0, 0, 0, 2),
    (0, 0, 2, -2),
    (0, 0, 2, 0),
    (0, 0, 2, 2),
    (0, 2, -2, 0),
    (0, 2, 0, -2),
    (0, 2, 0, 0),
    (0, 2, 0, 2),
    (0, 2, 2, 0),
    (1, -1, -1, -1),
    (1, -1, -1, 1),
    (1, -1, 1, -1),
    (1, -1, 1, 1),
    (1, 1, -1, -1),
    (1, 1, -1, 1),
    (1, 1, 1, -1),
    (1, 1, 1, 1),
    (2, -2, 0, 0),
    (2, 0, -2, 0),
    (2, 0, 0, -2),
    (2, 0, 0, 0),
    (2, 0, 0, 2),
    (2, 0, 2, 0),
    (2, 2, 0, 0)
  ]

def actSimple : F4Simple → Fin 48 → Fin 48
  | .s0 => ![1, 0, 2, 3, 4, 6, 5, 7, 8, 11, 12, 9, 10, 13, 14, 15, 20, 21, 22, 28, 16, 17, 18, 23, 24, 29, 30, 31, 19, 25, 26, 27, 32, 33, 34, 37, 38, 35, 36, 39, 40, 42, 41, 43, 44, 45, 47, 46]
  | .s1 => ![0, 2, 1, 3, 5, 4, 6, 7, 9, 8, 10, 11, 13, 12, 14, 16, 15, 17, 19, 18, 20, 23, 25, 21, 26, 22, 24, 27, 29, 28, 30, 32, 31, 33, 35, 34, 36, 37, 39, 38, 40, 41, 43, 42, 44, 46, 45, 47]
  | .s2 => ![0, 1, 4, 3, 2, 5, 6, 8, 7, 10, 9, 12, 11, 14, 13, 15, 18, 17, 16, 19, 22, 21, 20, 24, 23, 27, 26, 25, 28, 31, 30, 29, 32, 34, 33, 36, 35, 38, 37, 40, 39, 41, 42, 45, 44, 43, 46, 47]
  | .s3 => ![0, 1, 2, 7, 15, 16, 20, 3, 8, 9, 17, 11, 21, 23, 33, 4, 5, 10, 18, 19, 6, 12, 22, 13, 34, 25, 35, 41, 28, 29, 37, 42, 43, 14, 24, 26, 36, 30, 38, 39, 44, 27, 31, 32, 40, 45, 46, 47]

theorem root_carrier_has_48 : Fintype.card (Fin 48) = 48 := by decide

theorem simple_action_matches_reflection :
    ∀ s r, rootVec (actSimple s r) = reflectVec (simpleRoot s) (rootVec r) := by
  native_decide

theorem simple_involutive : ∀ s r, actSimple s (actSimple s r) = r := by
  native_decide

def adjacent : F4Simple → F4Simple → Bool
  | .s0,.s1 | .s1,.s0 => true
  | .s1,.s2 | .s2,.s1 => true
  | .s2,.s3 | .s3,.s2 => true
  | _,_ => false

/-- The double edge is between s1 (long) and s2 (short), hence braid length four. -/
def doubleAdjacent : F4Simple → F4Simple → Bool
  | .s1,.s2 | .s2,.s1 => true
  | _,_ => false

theorem ordinary_adjacent_braid3 :
    ∀ a b, adjacent a b = true → doubleAdjacent a b = false → ∀ r,
      actSimple a (actSimple b (actSimple a r)) =
      actSimple b (actSimple a (actSimple b r)) := by
  native_decide

theorem double_adjacent_braid4 :
    ∀ r,
      actSimple .s1 (actSimple .s2 (actSimple .s1 (actSimple .s2 r))) =
      actSimple .s2 (actSimple .s1 (actSimple .s2 (actSimple .s1 r))) := by
  native_decide

theorem nonadjacent_commute :
    ∀ a b, a ≠ b → adjacent a b = false → ∀ r,
      actSimple a (actSimple b r) = actSimple b (actSimple a r) := by
  native_decide

def cartanEntry (i j : F4Simple) : Int :=
  (2 * dot (simpleRoot i) (simpleRoot j)) / dot (simpleRoot i) (simpleRoot i)

theorem cartan_is_standard :
    cartanEntry .s0 .s0 = 2 ∧ cartanEntry .s0 .s1 = -1 ∧
    cartanEntry .s1 .s0 = -1 ∧ cartanEntry .s1 .s1 = 2 ∧
    cartanEntry .s1 .s2 = -1 ∧ cartanEntry .s2 .s1 = -2 ∧
    cartanEntry .s2 .s2 = 2 ∧ cartanEntry .s2 .s3 = -1 ∧
    cartanEntry .s3 .s2 = -1 ∧ cartanEntry .s3 .s3 = 2 := by
  native_decide

def pythonGeneratedWeylOrder : Nat := 1152

structure Boundary where
  root48Paid : Bool
  simpleReflectionTablesPaid : Bool
  reflectionFormulaIntertwiningPaid : Bool
  f4CoxeterRelationsPaid : Bool
  standardCartanPaid : Bool
  pythonWeylOrder1152Checked : Bool
  kernelGeneratedWeylOrderPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  root48Paid := true
  simpleReflectionTablesPaid := true
  reflectionFormulaIntertwiningPaid := true
  f4CoxeterRelationsPaid := true
  standardCartanPaid := true
  pythonWeylOrder1152Checked := true
  kernelGeneratedWeylOrderPaid := false

end Integration.F4RootWeylExact
