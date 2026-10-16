import Integration.E6Mod3QuadraticBridge
import Mathlib

/-!
# Prefix-depth versus quadratic-stratum interaction in F3^5

The balanced ternary prefix/depth filtration and the quadratic Q=0,1,2 strata
are not an independent Cartesian product.  This owner records the exact finite
intersection tensor for depths 1, 2 and 3 in the standardized five-dimensional
E6 mod-3 coordinate.

Profiles are ordered as:
  (zero point, nonzero Q=0, Q=1, Q=2).
-/

namespace DASHI.Integration.E6F3DepthQuadraticInteraction

open Integration.E6Mod3QuadraticBridge

inductive QuadraticStratum
  | zeroPoint
  | nonzeroQZero
  | qOne
  | qTwo
  deriving DecidableEq, Repr, Fintype

/-- Literal zero test on the five-coordinate carrier. -/
def isZeroFive (z : F3Five) : Prop :=
  z.z0 = 0 ∧ z.z1 = 0 ∧ z.z2 = 0 ∧ z.z3 = 0 ∧ z.z4 = 0

/-- Four-way affine stratum classifier. -/
def stratum (z : F3Five) : QuadraticStratum :=
  if isZeroFive z then .zeroPoint
  else if standardQuadratic z = 0 then .nonzeroQZero
  else if standardQuadratic z = 1 then .qOne
  else .qTwo

structure DepthProfile where
  zeroCount : Nat
  nonzeroQZeroCount : Nat
  qOneCount : Nat
  qTwoCount : Nat
  deriving DecidableEq, Repr

/-- Count one stratum inside a one-coordinate prefix cell. -/
def depth1Count (a : ZMod 3) (s : QuadraticStratum) : Nat :=
  (Finset.univ.filter fun z : F3Five => z.z0 = a ∧ stratum z = s).card

/-- Count one stratum inside a two-coordinate prefix cell. -/
def depth2Count (a b : ZMod 3) (s : QuadraticStratum) : Nat :=
  (Finset.univ.filter fun z : F3Five =>
    z.z0 = a ∧ z.z1 = b ∧ stratum z = s).card

/-- Count one stratum inside a three-coordinate prefix cell. -/
def depth3Count (a b c : ZMod 3) (s : QuadraticStratum) : Nat :=
  (Finset.univ.filter fun z : F3Five =>
    z.z0 = a ∧ z.z1 = b ∧ z.z2 = c ∧ stratum z = s).card

def depth1Profile (a : ZMod 3) : DepthProfile :=
  ⟨depth1Count a .zeroPoint,
   depth1Count a .nonzeroQZero,
   depth1Count a .qOne,
   depth1Count a .qTwo⟩

def depth2Profile (a b : ZMod 3) : DepthProfile :=
  ⟨depth2Count a b .zeroPoint,
   depth2Count a b .nonzeroQZero,
   depth2Count a b .qOne,
   depth2Count a b .qTwo⟩

def depth3Profile (a b c : ZMod 3) : DepthProfile :=
  ⟨depth3Count a b c .zeroPoint,
   depth3Count a b c .nonzeroQZero,
   depth3Count a b c .qOne,
   depth3Count a b c .qTwo⟩

/-! ## Depth 1: exactly two profile classes -/

theorem depth1_zero_profile :
    depth1Profile 0 = ⟨1,32,24,24⟩ := by
  native_decide

theorem depth1_one_profile :
    depth1Profile 1 = ⟨0,24,33,24⟩ := by
  native_decide

theorem depth1_two_profile :
    depth1Profile 2 = ⟨0,24,33,24⟩ := by
  native_decide

/-! ## Depth 2: exactly three profile classes -/

theorem depth2_zero_zero_profile :
    depth2Profile 0 0 = ⟨1,8,6,12⟩ := by
  native_decide

theorem depth2_exactly_one_nonzero_profile :
    ∀ a b : ZMod 3,
      ((a = 0 ∧ b ≠ 0) ∨ (a ≠ 0 ∧ b = 0)) →
      depth2Profile a b = ⟨0,12,9,6⟩ := by
  native_decide

theorem depth2_both_nonzero_profile :
    ∀ a b : ZMod 3,
      a ≠ 0 → b ≠ 0 →
      depth2Profile a b = ⟨0,6,12,9⟩ := by
  native_decide

/-! ## Depth 3: exactly four profile classes -/

theorem depth3_zero_zero_zero_profile :
    depth3Profile 0 0 0 = ⟨1,0,4,4⟩ := by
  native_decide

theorem depth3_exactly_one_nonzero_profile :
    ∀ a b c : ZMod 3,
      ((a ≠ 0 ∧ b = 0 ∧ c = 0) ∨
       (a = 0 ∧ b ≠ 0 ∧ c = 0) ∨
       (a = 0 ∧ b = 0 ∧ c ≠ 0)) →
      depth3Profile a b c = ⟨0,4,1,4⟩ := by
  native_decide

theorem depth3_exactly_two_nonzero_profile :
    ∀ a b c : ZMod 3,
      ((a = 0 ∧ b ≠ 0 ∧ c ≠ 0) ∨
       (a ≠ 0 ∧ b = 0 ∧ c ≠ 0) ∨
       (a ≠ 0 ∧ b ≠ 0 ∧ c = 0)) →
      depth3Profile a b c = ⟨0,4,4,1⟩ := by
  native_decide

theorem depth3_all_nonzero_profile :
    ∀ a b c : ZMod 3,
      a ≠ 0 → b ≠ 0 → c ≠ 0 →
      depth3Profile a b c = ⟨0,1,4,4⟩ := by
  native_decide

/-- Concrete non-product witness at fixed depth. -/
theorem depth_quadratic_not_cartesian_product :
    depth1Profile 0 ≠ depth1Profile 1 := by
  native_decide

/-- Named exact intersection tensors for downstream hyperfabric consumers. -/
def intersectionTensor1 : ZMod 3 → QuadraticStratum → Nat := depth1Count
def intersectionTensor2 : ZMod 3 → ZMod 3 → QuadraticStratum → Nat := depth2Count
def intersectionTensor3 : ZMod 3 → ZMod 3 → ZMod 3 → QuadraticStratum → Nat := depth3Count

structure InteractionBoundary where
  depth1IntersectionProfilesPaid : Bool
  depth2IntersectionProfilesPaid : Bool
  depth3IntersectionProfilesPaid : Bool
  exactIntersectionTensorNamed : Bool
  nonProductWitnessPaid : Bool
  depthAndQuadraticDeclaredIndependent : Bool
  deriving Repr

def interactionBoundary : InteractionBoundary where
  depth1IntersectionProfilesPaid := true
  depth2IntersectionProfilesPaid := true
  depth3IntersectionProfilesPaid := true
  exactIntersectionTensorNamed := true
  nonProductWitnessPaid := true
  depthAndQuadraticDeclaredIndependent := false

end DASHI.Integration.E6F3DepthQuadraticInteraction
