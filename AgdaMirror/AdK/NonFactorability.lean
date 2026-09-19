import Mathlib
import AgdaMirror.IntersectionalNonFactorability
import AgdaMirror.AdK.CVProjection

/-!
# Constructive AdK three-CV non-factorability

This file instantiates the repository-wide
`AgdaMirror.IntersectionalNonFactorability` spine rather than defining a
lane-local factorisation calculus.

Attribution:
- Li-Liu-Ji source-pay the selection/domain roles.
- Prohaska et al. source-pay the adopted working-mass convention.
- Crenshaw 1991 conceptually motivates the generic intersectional warning in the
  canonical source owner.
- The exact rational AdK reconstruction and the collision/non-factorability
  theorem instantiated here are DASHI mathematics.

The concrete witness uses the DASHI `.backbone` dLN evaluator convention solely
to inhabit one explicit projection. It does **not** resolve the source-level dLN
atom-subset ambiguity.
-/

namespace AgdaMirror.AdK.NonFactorability

open AgdaMirror.AdK.AtomisticConfiguration
open AgdaMirror.AdK.SourceSelections
open AgdaMirror.AdK.CanonicalSelectionContent
open AgdaMirror.AdK.CVProjection

namespace NF := AgdaMirror.IntersectionalNonFactorability

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

/-- Canonical repository-wide non-factorability witness:
same three-CV input surface, different full atomistic configuration. -/
def adkConfigurationNonFactorabilityWitness :
    NF.NonFactorabilityWitness
      (fun configuration =>
        threeCVInputSurface configuration .backbone)
      (fun configuration : Configuration => configuration) :=
  { left := collisionLeftConfiguration
    right := collisionRightConfiguration
    sameFlatProjection := collisionThreeCVInputEqual
    situatedOutcomesDiffer := collisionConfigurationsDistinct }

/-- Full atomistic identity cannot factor through this explicit three-CV input
projection. This is now an instance of the canonical repository-wide
`FactorsThrough` predicate. -/
theorem adkThreeCVInput_not_factors_through :
    ¬ NF.FactorsThrough
      (fun configuration =>
        threeCVInputSurface configuration .backbone)
      (fun configuration : Configuration => configuration) := by
  intro factor
  exact NF.witnessRulesOutEveryFlatFactorisation
    adkConfigurationNonFactorabilityWitness factor

/-- Any deterministic recharting of the already-collapsed three-CV surface also
cannot recover full atomistic identity for the witnessed pair. -/
theorem adkThreeCVRecharting_not_factors_through
    {Recharted : Type*}
    (rechart : ThreeCVInputSurface → Recharted) :
    ¬ NF.FactorsThrough
      (fun configuration =>
        rechart (threeCVInputSurface configuration .backbone))
      (fun configuration : Configuration => configuration) :=
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart adkConfigurationNonFactorabilityWitness

def sourceAttributionCreatesDASHINonFactorabilityTheorem : Bool := false

example : sourceAttributionCreatesDASHINonFactorabilityTheorem = false := rfl

end AgdaMirror.AdK.NonFactorability
