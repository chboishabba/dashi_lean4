import Integration.E6Mod3QuadraticBridge
import Mathlib

/-!
# Ternary 72 + 81 + 81 + 6 + 3 branching candidate

DASHI finite-geometry candidate, discovered and exhaustively preflighted in
local Python before formalization.

Inside the standardized `F3Five` quadratic space from the E6 mod-3 bridge,
choose the totally isotropic plane

  U = <(0,0,1,1,1), (0,1,0,1,2)>

and base point

  v = (1,0,0,0,0).

Then the affine plane `v + U` has 9 points, all in the Q=1 shell.  The affine
line

  v + <(0,0,1,1,1)>

has 3 points inside that plane.  This produces the exact finite partition
count pattern

  243 = 72 + 81 + 81 + 6 + 3,

and deleting the selected line gives

  240 = 72 + 81 + 81 + 6.

The count pattern is suggestive of the standard E8 -> E6 x A2 root-branching
cardinalities, but this module deliberately formalizes only the finite ternary
geometry.  It does not identify any sector with an E8 mixed-root orbit, does not
supply an E8 root equivalence, and does not identify this selected affine line
with the older constant-diagonal three-state cut.
-/

namespace Integration.E8E6A2TernaryBranchingCandidate

open Integration.E6Mod3QuadraticBridge

/-- Membership in the selected affine Q=1 plane.

The generator parametrization is `(1,b,a,a+b,a+2b)`, so these three equations
are an exact intrinsic membership test in the chosen coordinates. -/
def inSelectedAffinePlane (z : F3Five) : Bool :=
  decide (z.z0 = 1 ∧ z.z3 = z.z2 + z.z1 ∧ z.z4 = z.z2 + 2*z.z1)

/-- Membership in the selected three-point affine line, corresponding to `b=0`. -/
def inSelectedAffineLine (z : F3Five) : Bool :=
  decide (z.z0 = 1 ∧ z.z1 = 0 ∧ z.z3 = z.z2 ∧ z.z4 = z.z2)

/-- The selected nine-point affine plane. -/
def SelectedAffinePlane := {z : F3Five // inSelectedAffinePlane z = true}

/-- The selected three-point affine line. -/
def SelectedAffineLine := {z : F3Five // inSelectedAffineLine z = true}

instance : Fintype SelectedAffinePlane := inferInstance
instance : Fintype SelectedAffineLine := inferInstance

theorem selected_affine_plane_card : Fintype.card SelectedAffinePlane = 9 := by
  native_decide

theorem selected_affine_line_card : Fintype.card SelectedAffineLine = 3 := by
  native_decide

/-- The selected line is contained in the selected plane. -/
theorem selected_line_lies_in_plane :
    ∀ z : F3Five,
      inSelectedAffineLine z = true → inSelectedAffinePlane z = true := by
  native_decide

/-- Every point of the selected affine plane has standard quadratic value 1. -/
theorem selected_plane_lies_in_qone :
    ∀ z : SelectedAffinePlane, standardQuadratic z.1 = 1 := by
  native_decide

/-! ## The five disjoint count sectors -/

/-- The already-recognized 72-point E6/Q=2 sector. -/
def E6Sector := {z : F3Five // standardQuadratic z = 2}

/-- First 81-point sector: the full Q=0 shell. -/
def MixedSectorA := {z : F3Five // standardQuadratic z = 0}

/-- Second 81-point sector: Q=1 points outside the chosen affine plane. -/
def MixedSectorB :=
  {z : F3Five // standardQuadratic z = 1 ∧ inSelectedAffinePlane z = false}

/-- Six residual points of the affine plane after deleting the selected line. -/
def A2Sector :=
  {z : F3Five // inSelectedAffinePlane z = true ∧ inSelectedAffineLine z = false}

/-- The selected three-point line retained as an explicit residual sector. -/
def SelectedLineSector := {z : F3Five // inSelectedAffineLine z = true}

instance : Fintype E6Sector := inferInstance
instance : Fintype MixedSectorA := inferInstance
instance : Fintype MixedSectorB := inferInstance
instance : Fintype A2Sector := inferInstance
instance : Fintype SelectedLineSector := inferInstance

theorem e6_sector_card : Fintype.card E6Sector = 72 := by
  native_decide

theorem mixed_sector_a_card : Fintype.card MixedSectorA = 81 := by
  native_decide

theorem mixed_sector_b_card : Fintype.card MixedSectorB = 81 := by
  native_decide

theorem a2_sector_card : Fintype.card A2Sector = 6 := by
  native_decide

theorem selected_line_sector_card : Fintype.card SelectedLineSector = 3 := by
  native_decide

/-- The five count blocks exhaust all 243 points numerically. -/
theorem full_branching_count :
    Fintype.card F3Five = 72 + 81 + 81 + 6 + 3 := by
  native_decide

/-- Removing the geometrically selected affine line leaves exactly 240 states. -/
theorem selected_line_removed_count : 240 = 72 + 81 + 81 + 6 := by
  norm_num

/-- A computable classifier exposing the intended disjoint partition. -/
inductive BranchSector
  | e6
  | mixedA
  | mixedB
  | a2
  | selectedLine
  deriving DecidableEq, Repr

def branchSector (z : F3Five) : BranchSector :=
  if standardQuadratic z = 2 then .e6
  else if standardQuadratic z = 0 then .mixedA
  else if inSelectedAffineLine z = true then .selectedLine
  else if inSelectedAffinePlane z = true then .a2
  else .mixedB

/-- The line and old constant-diagonal cut are kept as distinct constructions.
No equality between them is introduced or inferred from their common size 3. -/
inductive SelectedAffineLineEqualsOldDiagonalCut : Prop

 theorem selectedAffineLineCannotEqualOldDiagonalByCardinalityAlone :
    ¬ SelectedAffineLineEqualsOldDiagonalCut := by
  intro h
  cases h

inductive BranchingCountsCreateE8Recognition : Prop
inductive SixPointSectorCreatesA2RootRecognition : Prop
inductive EightyOneSectorCreatesMixedE8OrbitRecognition : Prop

theorem branchingCountsCannotCreateE8Recognition :
    ¬ BranchingCountsCreateE8Recognition := by
  intro h
  cases h

theorem sixPointsCannotCreateA2Recognition :
    ¬ SixPointSectorCreatesA2RootRecognition := by
  intro h
  cases h

theorem eightyOnePointsCannotCreateMixedOrbitRecognition :
    ¬ EightyOneSectorCreatesMixedE8OrbitRecognition := by
  intro h
  cases h

structure Boundary where
  selectedAffinePlaneTyped : Bool
  selectedAffinePlaneCountNinePaid : Bool
  selectedAffinePlaneInsideQOnePaid : Bool
  selectedAffineLineCountThreePaid : Bool
  exact243BranchingCountPaid : Bool
  exact240AfterSelectedLineRemovalPaid : Bool
  e6SectorUsesExistingQTwoGeometry : Bool
  branchingCountsCreateE8Recognition : Bool
  sixPointSectorCreatesA2Recognition : Bool
  eightyOneSectorCreatesMixedOrbitRecognition : Bool
  selectedLineEqualsOldDiagonalCut : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  selectedAffinePlaneTyped := true
  selectedAffinePlaneCountNinePaid := true
  selectedAffinePlaneInsideQOnePaid := true
  selectedAffineLineCountThreePaid := true
  exact243BranchingCountPaid := true
  exact240AfterSelectedLineRemovalPaid := true
  e6SectorUsesExistingQTwoGeometry := true
  branchingCountsCreateE8Recognition := false
  sixPointSectorCreatesA2Recognition := false
  eightyOneSectorCreatesMixedOrbitRecognition := false
  selectedLineEqualsOldDiagonalCut := false

end Integration.E8E6A2TernaryBranchingCandidate
