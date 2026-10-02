import Mathlib
import Integration.OggSSPP2BalancedTernaryPuncturedPlane

/-!
# p=2 bad-prime level-4 moduli boundary

External source context: Katz--Mazur level structures and modern
supersingular p-power torsion theory require finite-flat/group-scheme semantics
at primes dividing the level.

At p=2, level 4 has group-scheme order 2^4 = 16, while the current balanced
residual target has 10 components.  Therefore the exact 1+1+8 target normal
form is not identified with the full E[4] object by cardinality.

The missing arithmetic bridge must provide an explicit marked quotient/moduli
construction and its action/orbit/stabilizer semantics.
-/

namespace Integration.OggSSPP2BadPrimeLevelStructureBoundary

open Integration.OggSSPP2BalancedTernaryPuncturedPlane

def supersingularLevelFourGroupSchemeOrder : Nat := 16

theorem supersingular_level_four_order_is_two_power_four :
    supersingularLevelFourGroupSchemeOrder = 2 * 2 * 2 * 2 := by
  decide

def balancedResidualTargetCount : Nat :=
  Fintype.card DuplicatedCentreNineSheet

theorem balanced_residual_target_count_is_ten :
    balancedResidualTargetCount = 10 := by
  decide

theorem sixteen_does_not_equal_ten :
    supersingularLevelFourGroupSchemeOrder ≠ balancedResidualTargetCount := by
  decide

inductive LevelFourArithmeticModel
  | naiveGeometricPointSet
  | finiteFlatGroupScheme
  | drinfeldKatzMazurLevelStructure
  deriving DecidableEq, Repr

structure P2LevelFourMarkedModuliSource where
  FineModuliState : Type
  MarkedResidualState : Type
  sourceModel : LevelFourArithmeticModel
  sourceUsesBadPrimeLevelStructureSemantics : Prop
  markedQuotient : FineModuliState → MarkedResidualState
  targetComparisonMap :
    MarkedResidualState → DuplicatedCentreNineSheet
  arithmeticProvenanceReference : String

inductive ClaimOrigin
  | externalSourceContext
  | repositoryNewExtension
  | openArithmeticRecognition
  deriving DecidableEq, Repr

def levelStructureOrigin : ClaimOrigin := .externalSourceContext
def acquisitionContractOrigin : ClaimOrigin := .repositoryNewExtension
def recognitionOrigin : ClaimOrigin := .openArithmeticRecognition

structure Boundary where
  levelFourAtPrimeTwoIsBadPrimeSituation : Bool
  finiteFlatGroupSchemeSemanticsRequired : Bool
  naiveEtalePointSetModelSufficient : Bool
  levelFourGroupSchemeOrderSixteenRecorded : Bool
  balancedResidualTargetCountTenRecorded : Bool
  sixteenEqualsTen : Bool
  balancedOneOneEightIdentifiedWithFullE4ByCount : Bool
  markedModuliQuotientStillRequired : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  levelFourAtPrimeTwoIsBadPrimeSituation := true
  finiteFlatGroupSchemeSemanticsRequired := true
  naiveEtalePointSetModelSufficient := false
  levelFourGroupSchemeOrderSixteenRecorded := true
  balancedResidualTargetCountTenRecorded := true
  sixteenEqualsTen := false
  balancedOneOneEightIdentifiedWithFullE4ByCount := false
  markedModuliQuotientStillRequired := true

end Integration.OggSSPP2BadPrimeLevelStructureBoundary
