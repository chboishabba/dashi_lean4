import Mathlib
import AgdaMirror.AdK.CVProjection

/-!
# Constructive AdK three-CV non-factorability

This file contains DASHI-original bridge mathematics.  Li-Liu-Ji source-pay the
selection/domain roles and Prohaska et al. source-pay the adopted working-mass
convention; neither source is attributed with the collision/non-factorability
theorem proved here.

The concrete witness uses the DASHI `.backbone` dLN evaluator convention solely
to inhabit one explicit projection.  It does **not** resolve the source-level
dLN atom-subset ambiguity.
-/

namespace AgdaMirror.AdK.NonFactorability

open AgdaMirror.AdK.AtomisticConfiguration
open AgdaMirror.AdK.SourceSelections
open AgdaMirror.AdK.CanonicalSelectionContent
open AgdaMirror.AdK.CVProjection

/-- Generic evidence that a projection identifies two distinct source objects. -/
structure ProjectionCollision (X Y : Type*) (proj : X → Y) where
  left : X
  right : X
  distinct : left ≠ right
  sameProjection : proj left = proj right

/-- Full recovery of `X` through a projection `proj : X → Y`. -/
structure FactorsThrough (X Y : Type*) (proj : X → Y) where
  recover : Y → X
  leftInverse : Function.LeftInverse recover proj

/-- A witnessed projection collision rules out full recovery/factorisation. -/
theorem collision_not_factors_through
    {X Y : Type*}
    {proj : X → Y}
    (collision : ProjectionCollision X Y proj) :
    ¬ FactorsThrough X Y proj := by
  intro factorisation
  apply collision.distinct
  calc
    collision.left = factorisation.recover (proj collision.left) :=
      (factorisation.leftInverse collision.left).symm
    _ = factorisation.recover (proj collision.right) :=
      congrArg factorisation.recover collision.sameProjection
    _ = collision.right := factorisation.leftInverse collision.right

private def atomId
    (residue : Int)
    (serial : Nat) : AtomId :=
  { model := 1
    chain := "A"
    residue := residue
    residueName := "ALA"
    atomName := "CA"
    altloc := ""
    serial := serial
    element := "C" }

private def carbonAtom
    (residue : Int)
    (serial : Nat)
    (x y z : Int) : Atom :=
  { id := atomId residue serial
    mass := massC
    position := pdbMilliVec x y z }

/-- One CORE atom, one NMP atom, one LID atom, and one hinge atom make every
source-facing COM selection used by the witness non-empty. -/
private def coreAtom : Atom := carbonAtom 1 1 0 0 0
private def nmpAtom : Atom := carbonAtom 50 2 1000 0 0
private def lidAtom : Atom := carbonAtom 123 3 2000 0 0
private def hingeAtom : Atom := carbonAtom 161 4 3000 0 0

/-- Residue 1000 lies outside every source-facing AdK CV residue span. -/
private def residualLeft : Atom := carbonAtom 1000 5 0 1000 0
private def residualRight : Atom := carbonAtom 1000 5 0 2000 0

def collisionLeftConfiguration : Configuration :=
  [coreAtom, nmpAtom, lidAtom, hingeAtom, residualLeft]

def collisionRightConfiguration : Configuration :=
  [coreAtom, nmpAtom, lidAtom, hingeAtom, residualRight]

theorem collisionConfigurationsDistinct :
    collisionLeftConfiguration ≠ collisionRightConfiguration := by
  decide

/-- The residual perturbation is erased by each source-facing selection. -/
theorem collisionTheta1LidContent :
    canonicalContent collisionLeftConfiguration theta1Lid =
      canonicalContent collisionRightConfiguration theta1Lid := by
  decide

theorem collisionHingeContent :
    canonicalContent collisionLeftConfiguration hinge =
      canonicalContent collisionRightConfiguration hinge := by
  decide

theorem collisionCoreContent :
    canonicalContent collisionLeftConfiguration core =
      canonicalContent collisionRightConfiguration core := by
  decide

theorem collisionTheta2NmpContent :
    canonicalContent collisionLeftConfiguration theta2Nmp =
      canonicalContent collisionRightConfiguration theta2Nmp := by
  decide

theorem collisionDlnLidBackboneContent :
    canonicalContent collisionLeftConfiguration (dlnLid .backbone) =
      canonicalContent collisionRightConfiguration (dlnLid .backbone) := by
  decide

theorem collisionDlnNmpBackboneContent :
    canonicalContent collisionLeftConfiguration (dlnNmp .backbone) =
      canonicalContent collisionRightConfiguration (dlnNmp .backbone) := by
  decide

/-- Constructive equality of the complete exact three-CV input surface. -/
theorem collisionThreeCVInputEqual :
    threeCVInputSurface collisionLeftConfiguration .backbone =
      threeCVInputSurface collisionRightConfiguration .backbone :=
  threeCVInput_eq_of_content_eq
    collisionTheta1LidContent
    collisionHingeContent
    collisionCoreContent
    collisionTheta2NmpContent
    collisionDlnLidBackboneContent
    collisionDlnNmpBackboneContent

/-- The concrete same-CV/different-configuration collision. -/
def adkThreeCVInputCollision :
    ProjectionCollision
      Configuration
      ThreeCVInputSurface
      (fun configuration => threeCVInputSurface configuration .backbone) :=
  { left := collisionLeftConfiguration
    right := collisionRightConfiguration
    distinct := collisionConfigurationsDistinct
    sameProjection := collisionThreeCVInputEqual }

/-- Full atomistic configuration recovery cannot factor through this explicit
three-CV input projection. -/
theorem adkThreeCVInput_not_factors_through :
    ¬ FactorsThrough
      Configuration
      ThreeCVInputSurface
      (fun configuration => threeCVInputSurface configuration .backbone) :=
  collision_not_factors_through adkThreeCVInputCollision

/-- Scientific/source attribution does not create this DASHI theorem. -/
def sourceAttributionCreatesDASHINonFactorabilityTheorem : Bool := false

example : sourceAttributionCreatesDASHINonFactorabilityTheorem = false := rfl

end AgdaMirror.AdK.NonFactorability
