import Integration.E6F3ExteriorSquare
import Mathlib

/-!
# Prefix-depth versus quadratic-stratum interaction in F3^5

The balanced ternary depth filtration and the quadratic Q=0,1,2 strata are not
independent product coordinates.  This file records exact intersection counts
for the first three prefix depths, making the transverse interaction finite and
kernel-checkable rather than heuristic.
-/

namespace Integration.E6F3DepthQuadraticInteraction

open Integration.E6F3ExteriorSquare

/-- Four-way affine stratum index: zero point, nonzero null, Q=1, Q=2. -/
def stratumIndex (z : V5) : Fin 4 :=
  if z = 0 then 0
  else if qStandard z = 0 then 1
  else if qStandard z = 1 then 2
  else 3

/-- Count a stratum inside a fixed one-coordinate prefix cell. -/
def depth1Count (a : F3) (s : Fin 4) : Nat :=
  (Finset.univ.filter fun z : V5 => z 0 = a ∧ stratumIndex z = s).card

/-- Count a stratum inside a fixed two-coordinate prefix cell. -/
def depth2Count (a b : F3) (s : Fin 4) : Nat :=
  (Finset.univ.filter fun z : V5 =>
    z 0 = a ∧ z 1 = b ∧ stratumIndex z = s).card

/-- Count a stratum inside a fixed three-coordinate prefix cell. -/
def depth3Count (a b c : F3) (s : Fin 4) : Nat :=
  (Finset.univ.filter fun z : V5 =>
    z 0 = a ∧ z 1 = b ∧ z 2 = c ∧ stratumIndex z = s).card

abbrev Profile := Fin 4 → Nat

def depth1Profile (a : F3) : Profile := fun s => depth1Count a s
def depth2Profile (a b : F3) : Profile := fun s => depth2Count a b s
def depth3Profile (a b c : F3) : Profile := fun s => depth3Count a b c s

/-- Exact depth-1 profiles: zero prefix differs from either nonzero prefix. -/
theorem depth1_zero_profile :
    depth1Profile 0 = ![1,32,24,24] := by
  native_decide

theorem depth1_one_profile :
    depth1Profile 1 = ![0,24,33,24] := by
  native_decide

theorem depth1_two_profile :
    depth1Profile 2 = ![0,24,33,24] := by
  native_decide

/-- Exact depth-2 profile classes. -/
theorem depth2_zero_zero_profile :
    depth2Profile 0 0 = ![1,8,6,12] := by
  native_decide

theorem depth2_exactly_one_nonzero_profile :
    ∀ a b : F3,
      ((a = 0 ∧ b ≠ 0) ∨ (a ≠ 0 ∧ b = 0)) →
      depth2Profile a b = ![0,12,9,6] := by
  native_decide

theorem depth2_both_nonzero_profile :
    ∀ a b : F3,
      a ≠ 0 → b ≠ 0 →
      depth2Profile a b = ![0,6,12,9] := by
  native_decide

/-- Depth 3 has four distinct exact profile classes. -/
theorem depth3_zero_zero_zero_profile :
    depth3Profile 0 0 0 = ![1,0,4,4] := by
  native_decide

theorem depth3_exactly_one_nonzero_profile :
    ∀ a b c : F3,
      ((a ≠ 0 ∧ b = 0 ∧ c = 0) ∨
       (a = 0 ∧ b ≠ 0 ∧ c = 0) ∨
       (a = 0 ∧ b = 0 ∧ c ≠ 0)) →
      depth3Profile a b c = ![0,4,1,4] := by
  native_decide

theorem depth3_exactly_two_nonzero_profile :
    ∀ a b c : F3,
      ((a = 0 ∧ b ≠ 0 ∧ c ≠ 0) ∨
       (a ≠ 0 ∧ b = 0 ∧ c ≠ 0) ∨
       (a ≠ 0 ∧ b ≠ 0 ∧ c = 0)) →
      depth3Profile a b c = ![0,4,4,1] := by
  native_decide

theorem depth3_all_nonzero_profile :
    ∀ a b c : F3,
      a ≠ 0 → b ≠ 0 → c ≠ 0 →
      depth3Profile a b c = ![0,1,4,4] := by
  native_decide

/-- Concrete non-product witness: cells of the same depth have different
quadratic-stratum profiles. -/
theorem depth_and_quadratic_not_product :
    depth1Profile 0 ≠ depth1Profile 1 := by
  native_decide

/-- The exact finite intersection tensor requested by the hyperfabric analysis. -/
def intersectionTensor1 : F3 → Fin 4 → Nat := depth1Count
def intersectionTensor2 : F3 → F3 → Fin 4 → Nat := depth2Count
def intersectionTensor3 : F3 → F3 → F3 → Fin 4 → Nat := depth3Count

structure Boundary where
  depth1ProfilesPaid : Bool
  depth2ProfilesPaid : Bool
  depth3ProfilesPaid : Bool
  nonProductWitnessPaid : Bool
  depthAndQuadraticDeclaredIndependent : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  depth1ProfilesPaid := true
  depth2ProfilesPaid := true
  depth3ProfilesPaid := true
  nonProductWitnessPaid := true
  depthAndQuadraticDeclaredIndependent := false

end Integration.E6F3DepthQuadraticInteraction
