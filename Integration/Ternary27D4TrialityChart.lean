import Integration.Ternary27HyperformSchlafliRecognition
import Integration.F4D4TrialityAlbertShape
import Mathlib

/-!
# Change of chart on the same minuscule 27

The typed ternary/Schlaefli chart presents the 27 as `6 + 15 + 6`, while the
folded F4/D4 chart presents the same paid omega5 weight carrier as
`3 + 8 + 8 + 8`.  These are not blockwise-identical decompositions.

This owner computes their exact intersection table on the already-paid
`SchlafliLabel -> Omega5Weight` bijection.  It is a finite same-object chart
transition, not an Albert-product theorem.
-/

namespace Integration.Ternary27D4TrialityChart

open Integration.E6Minuscule27LiteralRecognition
open Integration.Ternary27HyperformSchlafliRecognition
open Integration.F4D4TrialityAlbertShape

inductive TrialitySector
  | diagonal | sector0 | sector1 | sector2
  deriving DecidableEq, Repr, Fintype

/-- Classify one paid minuscule weight by the exact folded decomposition. -/
def weightSector (w : DynkinLabel) : TrialitySector :=
  if w ∈ foldedZero3 then .diagonal
  else if w ∈ trialityOrbit0 then .sector0
  else if w ∈ trialityOrbit1 then .sector1
  else .sector2

def labelSector (l : SchlafliLabel) : TrialitySector :=
  weightSector (labelWeight l)

/-- Every omega5 weight lands in exactly the paid `3 + 8 + 8 + 8` partition. -/
theorem omega5_sector_partition :
    ∀ w ∈ minusculeOmega5Set,
      w ∈ foldedZero3 ∨ w ∈ trialityOrbit0 ∨ w ∈ trialityOrbit1 ∨ w ∈ trialityOrbit2 := by
  native_decide

/-- Global sector cardinalities on the 27 labels. -/
def sectorCount (s : TrialitySector) : Nat :=
  (Finset.univ.filter fun l : SchlafliLabel => labelSector l = s).card

theorem diagonal_count_3 : sectorCount .diagonal = 3 := by native_decide
theorem sector0_count_8 : sectorCount .sector0 = 8 := by native_decide
theorem sector1_count_8 : sectorCount .sector1 = 8 := by native_decide
theorem sector2_count_8 : sectorCount .sector2 = 8 := by native_decide

/-- Counts restricted to the left six of the Schlaefli chart. -/
def leftSectorCount (s : TrialitySector) : Nat :=
  (Finset.univ.filter fun f : Face6 => labelSector (.left f) = s).card

/-- Counts restricted to the middle fifteen. -/
def middleSectorCount (s : TrialitySector) : Nat :=
  (Finset.univ.filter fun p : Pair15 => labelSector (.middle p) = s).card

/-- Counts restricted to the right six. -/
def rightSectorCount (s : TrialitySector) : Nat :=
  (Finset.univ.filter fun f : Face6 => labelSector (.right f) = s).card

/-- Exact transverse change-of-chart matrix

        diag  8v  8s  8c
left      1   0   1   4
middle    1   4   6   4
right     1   4   1   0

where `sector0/1/2` use the repository's fixed three triality seeds. -/
theorem left_chart_row :
    leftSectorCount .diagonal = 1 ∧
    leftSectorCount .sector0 = 0 ∧
    leftSectorCount .sector1 = 1 ∧
    leftSectorCount .sector2 = 4 := by
  native_decide

theorem middle_chart_row :
    middleSectorCount .diagonal = 1 ∧
    middleSectorCount .sector0 = 4 ∧
    middleSectorCount .sector1 = 6 ∧
    middleSectorCount .sector2 = 4 := by
  native_decide

theorem right_chart_row :
    rightSectorCount .diagonal = 1 ∧
    rightSectorCount .sector0 = 4 ∧
    rightSectorCount .sector1 = 1 ∧
    rightSectorCount .sector2 = 0 := by
  native_decide

/-- Each Schlaefli stratum keeps its expected cardinality after refinement. -/
theorem row_sums :
    (leftSectorCount .diagonal + leftSectorCount .sector0 +
      leftSectorCount .sector1 + leftSectorCount .sector2 = 6) ∧
    (middleSectorCount .diagonal + middleSectorCount .sector0 +
      middleSectorCount .sector1 + middleSectorCount .sector2 = 15) ∧
    (rightSectorCount .diagonal + rightSectorCount .sector0 +
      rightSectorCount .sector1 + rightSectorCount .sector2 = 6) := by
  native_decide

inductive ChartIntersectionCreatesAlbertProduct : Prop

theorem chart_transition_does_not_create_albert_product :
    ¬ ChartIntersectionCreatesAlbertProduct := by
  intro h; cases h

structure Boundary where
  sameMinusculeCarrier : Bool
  schlaefliSixFifteenSixPaid : Bool
  d4ThreeEightEightEightPaid : Bool
  exactIntersectionTablePaid : Bool
  actualAlbertCoordinateIntertwinerPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  sameMinusculeCarrier := true
  schlaefliSixFifteenSixPaid := true
  d4ThreeEightEightEightPaid := true
  exactIntersectionTablePaid := true
  actualAlbertCoordinateIntertwinerPaid := false

end Integration.Ternary27D4TrialityChart
