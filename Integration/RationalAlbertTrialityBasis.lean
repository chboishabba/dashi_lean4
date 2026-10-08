import Integration.RationalAlbertS3Native
import Integration.F4D4TrialityAlbertShape
import Mathlib

/-!
# Literal native Albert 3 + 8 + 8 + 8 coordinate basis

This file turns the finite `3 + 8v + 8s + 8c` shadow into actual rational
Albert coordinate vectors.  It still does not identify the finite D4 orbit
action with octonion triality; that remaining intertwiner is isolated at the
end.
-/

namespace Integration.RationalAlbertTrialityBasis

open Integration.RationalCayleyDicksonOctonion
open Integration.RationalAlbertNative
open Integration.RationalAlbertS3Native
open Integration.F4D4TrialityAlbertShape
open RationalQuaternion RationalOctonion RationalAlbertNative.RationalAlbert

abbrev Q4 := RationalQuaternion
abbrev O8 := RationalOctonion
abbrev A27 := RationalAlbertNative.RationalAlbert

private def q0 : Q4 := ⟨1,0,0,0⟩
private def q1 : Q4 := ⟨0,1,0,0⟩
private def q2 : Q4 := ⟨0,0,1,0⟩
private def q3 : Q4 := ⟨0,0,0,1⟩

/-- Standard rational coordinate basis of the octonion carrier. -/
def octBasis : Fin 8 → O8 :=
  ![⟨q0,0⟩,⟨q1,0⟩,⟨q2,0⟩,⟨q3,0⟩,
    ⟨0,q0⟩,⟨0,q1⟩,⟨0,q2⟩,⟨0,q3⟩]

/-- Conjugation fixes the scalar basis vector and negates the seven imaginary
basis vectors. -/
def octConjSign : Fin 8 → ℚ := ![1,-1,-1,-1,-1,-1,-1,-1]

theorem conj_octBasis (i : Fin 8) :
    RationalOctonion.conj (octBasis i) = octConjSign i • octBasis i := by
  fin_cases i <;> rfl

/-- Three diagonal Albert basis vectors. -/
def diagBasis : Fin 3 → A27 :=
  ![⟨1,0,0,0,0,0⟩,⟨0,1,0,0,0,0⟩,⟨0,0,1,0,0,0⟩]

/-- Three octonion coordinate slots, each with its literal 8-coordinate basis. -/
def slotBasis : Fin 3 → Fin 8 → A27
  | 0, i => ⟨0,0,0,octBasis i,0,0⟩
  | 1, i => ⟨0,0,0,0,octBasis i,0⟩
  | 2, i => ⟨0,0,0,0,0,octBasis i⟩

abbrev AlbertBasisIndex := Fin 3 ⊕ (Fin 3 × Fin 8)

def basisVector : AlbertBasisIndex → A27
  | .inl i => diagBasis i
  | .inr si => slotBasis si.1 si.2

theorem basis_index_card_27 : Fintype.card AlbertBasisIndex = 27 := by native_decide

/-- The three diagonal basis vectors sum to the distinguished Albert unit. -/
theorem diagonal_sum_is_unit :
    diagBasis 0 + diagBasis 1 + diagBasis 2 = unit := by rfl

/-- Slot permutation used by the coordinate 3-cycle. -/
def cycleSlot : Fin 3 → Fin 3 := ![1,2,0]

theorem cycle_diag_basis (i : Fin 3) :
    cycleA (diagBasis i) = diagBasis (cycleSlot i) := by
  fin_cases i <;> rfl

theorem cycle_slot_basis (s : Fin 3) (i : Fin 8) :
    cycleA (slotBasis s i) = slotBasis (cycleSlot s) i := by
  fin_cases s <;> rfl

/-- Slot permutation of the 1<->2 transposition. -/
def swapSlot : Fin 3 → Fin 3 := ![0,2,1]

theorem swap_diag_basis (i : Fin 3) :
    swapA (diagBasis i) = diagBasis (swapSlot i) := by
  fin_cases i <;> rfl

/-- On each octonion coordinate line the transposition performs the expected
slot swap and octonion conjugation sign. -/
theorem swap_slot_basis (s : Fin 3) (i : Fin 8) :
    swapA (slotBasis s i) = octConjSign i • slotBasis (swapSlot s) i := by
  fin_cases s <;> fin_cases i <;> rfl

/-- The finite D4 triality anatomy and the native Albert carrier now have the
same literal coordinate ledger.  The missing theorem is an action intertwiner,
not another dimensional equality. -/
structure D4OctonionSectorIntertwiner where
  /-- One bijection from each finite eight-weight orbit to one octonion basis. -/
  orbit0ToBasis : {w // w ∈ trialityOrbit0} ≃ Fin 8
  orbit1ToBasis : {w // w ∈ trialityOrbit1} ≃ Fin 8
  orbit2ToBasis : {w // w ∈ trialityOrbit2} ≃ Fin 8

  /-- The 192-element D4 kernel acts on the three actual octonion coordinate
  spaces through linear maps. -/
  d4OnOct0 : Mat6 → O8 → O8
  d4OnOct1 : Mat6 → O8 → O8
  d4OnOct2 : Mat6 → O8 → O8

  /-- Only kernel elements are required to realize the three independent
  eight-dimensional actions. -/
  mapsBasis0 : ∀ M, M ∈ d4KernelSet → ∀ w : {w // w ∈ trialityOrbit0},
    d4OnOct0 M (octBasis (orbit0ToBasis w)) =
      octBasis (orbit0ToBasis ⟨matrixApply M w.1, by
        simpa [trialityOrbit0,d4Orbit] using Finset.mem_image_of_mem (fun N => matrixApply N w.1) ‹M ∈ d4KernelSet›⟩)
  mapsBasis1 : ∀ M, M ∈ d4KernelSet → ∀ w : {w // w ∈ trialityOrbit1},
    d4OnOct1 M (octBasis (orbit1ToBasis w)) =
      octBasis (orbit1ToBasis ⟨matrixApply M w.1, by
        simpa [trialityOrbit1,d4Orbit] using Finset.mem_image_of_mem (fun N => matrixApply N w.1) ‹M ∈ d4KernelSet›⟩)
  mapsBasis2 : ∀ M, M ∈ d4KernelSet → ∀ w : {w // w ∈ trialityOrbit2},
    d4OnOct2 M (octBasis (orbit2ToBasis w)) =
      octBasis (orbit2ToBasis ⟨matrixApply M w.1, by
        simpa [trialityOrbit2,d4Orbit] using Finset.mem_image_of_mem (fun N => matrixApply N w.1) ‹M ∈ d4KernelSet›⟩)

inductive ShapeCreatesTrialityIntertwiner : Prop

theorem shape_does_not_create_triality_intertwiner : ¬ ShapeCreatesTrialityIntertwiner := by
  intro h; cases h

structure Boundary where
  nativeOctonionBasis8Paid : Bool
  nativeDiagonalBasis3Paid : Bool
  nativeAlbertBasis27Paid : Bool
  s3CycleActsOnLiteralSlotsPaid : Bool
  s3SwapActsWithConjugationPaid : Bool
  finiteD4ThreeEightOrbitShapePaidUpstream : Bool
  actualD4OctonionIntertwinerPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  nativeOctonionBasis8Paid := true
  nativeDiagonalBasis3Paid := true
  nativeAlbertBasis27Paid := true
  s3CycleActsOnLiteralSlotsPaid := true
  s3SwapActsWithConjugationPaid := true
  finiteD4ThreeEightOrbitShapePaidUpstream := true
  actualD4OctonionIntertwinerPaidHere := false

end Integration.RationalAlbertTrialityBasis
