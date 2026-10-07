import Integration.F4MinusculeOnePlus26
import Integration.E6F4WeylFold
import Mathlib

/-!
# W(D4) triality anatomy inside the folded W(F4) minuscule 27

The folded W(F4) action already splits the E6 minuscule 27 into 24 nonzero
folded weights plus three folded-zero weight lines.  The pointwise stabilizer of
those three zero lines has order 192.  Its action on the remaining 24 weights
has exactly three orbits of size 8.  The quotient action permutes those three
8-orbits as S3.

This is the exact finite representation shadow of the Albert coordinate anatomy

  H_3(O) = 3 diagonal scalars + 3 octonionic slots of dimension 8,

and of the classical triality decomposition `8v + 8s + 8c`.  No Jordan product
or cubic compatibility is inferred from the matching action anatomy alone.
-/

namespace Integration.F4D4TrialityAlbertShape

open Integration.E6Minuscule27LiteralRecognition
open Integration.E6Minuscule27SchlafliRecognition
open Integration.E6F4WeylFold
open Integration.F4MinusculeOnePlus26

/-- A generated folded matrix fixes the three folded-zero weights pointwise. -/
def fixesFoldedZero3 (M : Mat6) : Bool :=
  decide (matrixApply M zeroWeight0.1 = zeroWeight0.1 ∧
          matrixApply M zeroWeight1.1 = zeroWeight1.1 ∧
          matrixApply M zeroWeight2.1 = zeroWeight2.1)

/-- Kernel of the S3 action on the three folded-zero lines. -/
def d4KernelSet : Finset Mat6 :=
  foldedGeneratedSet.filter fun M => fixesFoldedZero3 M

/-- Exact order of the pointwise-zero-line stabilizer. -/
theorem d4_kernel_card_192 : d4KernelSet.card = 192 := by
  native_decide

/-- Three representatives for the nonzero 24-weight sector. -/
def trialitySeed0 : DynkinLabel := ![-1,-1,0,1,0,0]
def trialitySeed1 : DynkinLabel := ![-1,0,1,0,0,-1]
def trialitySeed2 : DynkinLabel := ![0,-1,0,0,1,-1]

/-- Orbit under the 192-element pointwise stabilizer. -/
def d4Orbit (seed : DynkinLabel) : Finset DynkinLabel :=
  d4KernelSet.image fun M => matrixApply M seed

def trialityOrbit0 : Finset DynkinLabel := d4Orbit trialitySeed0
def trialityOrbit1 : Finset DynkinLabel := d4Orbit trialitySeed1
def trialityOrbit2 : Finset DynkinLabel := d4Orbit trialitySeed2

/-- The three triality sectors each have dimension/weight-count 8. -/
theorem triality_orbit0_card_8 : trialityOrbit0.card = 8 := by native_decide
theorem triality_orbit1_card_8 : trialityOrbit1.card = 8 := by native_decide
theorem triality_orbit2_card_8 : trialityOrbit2.card = 8 := by native_decide

/-- They are pairwise disjoint. -/
theorem triality_orbits_pairwise_disjoint :
    Disjoint trialityOrbit0 trialityOrbit1 ∧
    Disjoint trialityOrbit0 trialityOrbit2 ∧
    Disjoint trialityOrbit1 trialityOrbit2 := by
  native_decide

/-- The three D4 orbits exhaust the 24 nonzero folded weights. -/
theorem folded_nonzero24_eq_triality_union :
    foldedNonzero24 = trialityOrbit0 ∪ trialityOrbit1 ∪ trialityOrbit2 := by
  native_decide

/-- Two folded simple generators lie in the D4 kernel. -/
theorem g1_g3_preserve_each_triality_sector :
    (∀ x ∈ trialityOrbit0, foldReflect .g1 x ∈ trialityOrbit0) ∧
    (∀ x ∈ trialityOrbit1, foldReflect .g1 x ∈ trialityOrbit1) ∧
    (∀ x ∈ trialityOrbit2, foldReflect .g1 x ∈ trialityOrbit2) ∧
    (∀ x ∈ trialityOrbit0, foldReflect .g3 x ∈ trialityOrbit0) ∧
    (∀ x ∈ trialityOrbit1, foldReflect .g3 x ∈ trialityOrbit1) ∧
    (∀ x ∈ trialityOrbit2, foldReflect .g3 x ∈ trialityOrbit2) := by
  native_decide

/-- `g05` exchanges the first and third 8-dimensional sectors and fixes the
second. -/
theorem g05_triality_transposition :
    (trialityOrbit0.image (foldReflect .g05) = trialityOrbit2) ∧
    (trialityOrbit2.image (foldReflect .g05) = trialityOrbit0) ∧
    (trialityOrbit1.image (foldReflect .g05) = trialityOrbit1) := by
  native_decide

/-- `g24` exchanges the second and third sectors and fixes the first. -/
theorem g24_triality_transposition :
    (trialityOrbit1.image (foldReflect .g24) = trialityOrbit2) ∧
    (trialityOrbit2.image (foldReflect .g24) = trialityOrbit1) ∧
    (trialityOrbit0.image (foldReflect .g24) = trialityOrbit0) := by
  native_decide

/-- Exact finite coordinate ledger matching the linear anatomy of H3(O). -/
structure AlbertCoordinateShapeLedger where
  diagonalLines : Nat
  octonionSlots : Nat
  dimensionsPerOctonionSlot : Nat
  totalDimension : Nat
  diagonalLines_eq_3 : diagonalLines = 3
  octonionSlots_eq_3 : octonionSlots = 3
  dimensionsPerOctonionSlot_eq_8 : dimensionsPerOctonionSlot = 8
  totalDimension_eq_27 : totalDimension = 27

def canonicalAlbertCoordinateShape : AlbertCoordinateShapeLedger where
  diagonalLines := 3
  octonionSlots := 3
  dimensionsPerOctonionSlot := 8
  totalDimension := 27
  diagonalLines_eq_3 := rfl
  octonionSlots_eq_3 := rfl
  dimensionsPerOctonionSlot_eq_8 := rfl
  totalDimension_eq_27 := rfl

inductive TrialityShapeCreatesAlbertProduct : Prop

theorem triality_shape_does_not_create_albert_product :
    ¬ TrialityShapeCreatesAlbertProduct := by
  intro h; cases h

structure Boundary where
  d4KernelOrder192Paid : Bool
  threeEightOrbitsPaid : Bool
  orbitsExhaustNonzero24Paid : Bool
  quotientTrialityTranspositionsPaid : Bool
  threePlusThreeTimesEightMatchesAlbertShape : Bool
  jordanProductCompatibilityPaidHere : Bool
  cubicCompatibilityPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  d4KernelOrder192Paid := true
  threeEightOrbitsPaid := true
  orbitsExhaustNonzero24Paid := true
  quotientTrialityTranspositionsPaid := true
  threePlusThreeTimesEightMatchesAlbertShape := true
  jordanProductCompatibilityPaidHere := false
  cubicCompatibilityPaidHere := false

end Integration.F4D4TrialityAlbertShape
