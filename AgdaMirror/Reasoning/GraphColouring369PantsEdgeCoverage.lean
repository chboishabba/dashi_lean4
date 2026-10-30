/-!
# Canonical 54-edge chart and adjacency classification — Lean mirror

Golden: DASHI.Combinatorics.GraphColouring369PantsEdgeCoverageExact

This downstream finite algorithm returns TRUE if an ordered native
grid adjacency matches one of the 54 canonical axis/step templates
in either orientation. It does not replace the native graph or
equate the 27-grid to the asymmetric three-vertex weighted matrix.
-/
import Mathlib
import AgdaMirror.Reasoning.GraphColouring369PantsGridAdjacency

namespace AgdaMirror.Reasoning.GraphColouring369PantsEdgeCoverage

open AgdaMirror.Reasoning.GraphColouring369PantsGridAdjacency
open AgdaMirror.Base369

inductive Axis where
  | x | y | z
  deriving DecidableEq, Repr

inductive UnitStep where
  | lowMid | midHigh
  deriving DecidableEq, Repr

structure EdgeSlot where
  axis : Axis
  first : TriTruth
  second : TriTruth
  step : UnitStep
  deriving DecidableEq, Repr

def canonicalEndpoints (slot : EdgeSlot) : Voxel × Voxel :=
  match slot.axis, slot.step with
  | .x, .lowMid => ((.low, slot.first, slot.second), (.mid, slot.first, slot.second))
  | .x, .midHigh => ((.mid, slot.first, slot.second), (.high, slot.first, slot.second))
  | .y, .lowMid => ((slot.first, .low, slot.second), (slot.first, .mid, slot.second))
  | .y, .midHigh => ((slot.first, .mid, slot.second), (slot.first, .high, slot.second))
  | .z, .lowMid => ((slot.first, slot.second, .low), (slot.first, slot.second, .mid))
  | .z, .midHigh => ((slot.first, slot.second, .mid), (slot.first, slot.second, .high))

def allTrits : List TriTruth := [.low, .mid, .high]
def allAxes : List Axis := [.x, .y, .z]
def allSteps : List UnitStep := [.lowMid, .midHigh]

def allCanonicalSlots : List EdgeSlot :=
  allAxes.flatMap fun ax =>
    allTrits.flatMap fun a =>
      allTrits.flatMap fun b =>
        allSteps.map fun s => ⟨ax, a, b, s⟩

theorem cardinality_54 : allCanonicalSlots.length = 54 := by decide

theorem distinct_54_slots : allCanonicalSlots.Nodup := by decide

def matchesEitherOrientation (slot : EdgeSlot) (u v : Voxel) : Bool :=
  decide (canonicalEndpoints slot = (u,v) ∨
          canonicalEndpoints slot = (v,u))

def covered (u v : Voxel) : Bool :=
  allCanonicalSlots.any fun slot => matchesEitherOrientation slot u v

/-- The algorithmic chart is complete for native one-step neighbours;
    its truth is decidable from the 27×27 closed carrier. -/
theorem all_actual_native_neighbours_covered
    (u v : Voxel) (h : VoxelAdjacent u v) :
    covered u v = true := by
  rcases u with ⟨a,b,c⟩
  rcases v with ⟨d,e,f⟩
  cases a <;> cases b <;> cases c <;>
    cases d <;> cases e <;> cases f <;>
    cases h <;> decide

/-- No template invents non-neighbour endpoints. -/

theorem every_canonical_template_is_native (slot : EdgeSlot) :
    VoxelAdjacent (canonicalEndpoints slot).1
                  (canonicalEndpoints slot).2 := by
  rcases slot with ⟨ax,a,b,s⟩
  cases ax with
  | x =>
    cases s with
    | lowMid => exact VoxelAdjacent.x TritGridStep.lowMid
    | midHigh => exact VoxelAdjacent.x TritGridStep.midHigh
  | y =>
    cases s with
    | lowMid => exact VoxelAdjacent.y TritGridStep.lowMid
    | midHigh => exact VoxelAdjacent.y TritGridStep.midHigh
  | z =>
    cases s with
    | lowMid => exact VoxelAdjacent.z TritGridStep.lowMid
    | midHigh => exact VoxelAdjacent.z TritGridStep.midHigh

end AgdaMirror.Reasoning.GraphColouring369PantsEdgeCoverage
