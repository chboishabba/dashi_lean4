import Mathlib
import Integration.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparation
import Integration.OggSSPP2UniqueGamma0FourMarkingBidi
import Integration.OggSSPP2ArithmeticBidiDualCodecTransport

/-!
# p=2 supersingular universal-deformation source

Source context:
N. Katz and B. Mazur, Arithmetic Moduli of Elliptic Curves,
Annals of Mathematics Studies 108, Princeton University Press, 1985.

The source-facing shape records:
* a one-parameter universal deformation of a supersingular elliptic curve over
  a complete local Witt-vector power-series base W(k)[[t]];
* level-4 marked states over finite local extensions of that deformation;
* specialization of every marked state to the unique raw ker(F^2) subgroup.

The open DASHI theorem is a single finite classification:
construct the existing ten-state arithmetic bidi.  Once that exists, both paid
dependent codecs follow automatically.
-/

namespace Integration.OggSSPP2SupersingularUniversalDeformationSource

namespace Unique :=
  Integration.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparation
namespace Bidi :=
  Integration.OggSSPP2UniqueGamma0FourMarkingBidi

structure SupersingularUniversalDeformationDatum where
  ResidueField : Type
  WittBase : Type
  FormalParameter : Type
  DeformationBase : Type
  EllipticFamilyState : Type

  characteristic : Nat
  characteristicIsTwo : characteristic = 2

  oneFormalParameter : Prop
  completeLocalWittPowerSeriesShape : Prop
  supersingularSpecialFibre : Prop
  universalPropertyImportedFromSource : Prop

  sourceReference : String

structure Gamma0FourUniversalDeformationMarking
    (datum : SupersingularUniversalDeformationDatum) where
  MarkedState : Type

  underlyingFamilyState :
    MarkedState → datum.EllipticFamilyState

  specializesToRawSubgroup :
    MarkedState → Unique.SupersingularRawGamma0FourSubgroup

  specializationIsUniqueKerFrobeniusSquared :
    ∀ state, specializesToRawSubgroup state =
      .kerFrobeniusSquared

  gamma0FourLevelStructurePresent :
    MarkedState → Prop

  gamma0FourLevelStructurePresentProof :
    ∀ state, gamma0FourLevelStructurePresent state

  deformationProvenanceRetained :
    MarkedState → Prop

  deformationProvenanceRetainedProof :
    ∀ state, deformationProvenanceRetained state

def toUniqueSubgroupMarking
    {datum : SupersingularUniversalDeformationDatum}
    (marking : Gamma0FourUniversalDeformationMarking datum) :
    Unique.MarkingOverUniqueGamma0FourSubgroup where
  MarkedState := marking.MarkedState
  rawSubgroup := marking.specializesToRawSubgroup
  everyStateLiesOverKerFrobeniusSquared :=
    marking.specializationIsUniqueKerFrobeniusSquared
  residualDatum := fun _ => .deformationMarking
  provenanceFromArithmeticModuli := True

structure UniversalDeformationTenStateRecognition
    (datum : SupersingularUniversalDeformationDatum)
    (marking : Gamma0FourUniversalDeformationMarking datum) where
  arithmeticBidi :
    Bidi.Bidi (toUniqueSubgroupMarking marking)

inductive Residual
  | missingFormalWittPowerSeriesBase
  | missingFormalUniversalEllipticFamily
  | missingGamma0FourMarkedDeformationStates
  | missingTenStateClassificationBidi
  deriving DecidableEq, Repr

structure Boundary where
  sourceBackedOneParameterShapeRecorded : Bool
  sourceBackedWittPowerSeriesShapeRecorded : Bool
  sourceBackedDrinfeldLevelStructureContextRecorded : Bool
  specializationToUniqueKerFrobeniusSquaredRequired : Bool
  tenStateClassificationSeparatedFromSourceShape : Bool
  oneParameterCountPromotedToTenStates : Bool
  universalDeformationImplementedInternally : Bool
  gamma0FourMarkedStatesConstructed : Bool
  tenStateRecognitionConstructed : Bool
  firstResidual : Residual
  deriving Repr

def canonicalBoundary : Boundary where
  sourceBackedOneParameterShapeRecorded := true
  sourceBackedWittPowerSeriesShapeRecorded := true
  sourceBackedDrinfeldLevelStructureContextRecorded := true
  specializationToUniqueKerFrobeniusSquaredRequired := true
  tenStateClassificationSeparatedFromSourceShape := true
  oneParameterCountPromotedToTenStates := false
  universalDeformationImplementedInternally := false
  gamma0FourMarkedStatesConstructed := false
  tenStateRecognitionConstructed := false
  firstResidual := .missingFormalWittPowerSeriesBase

end Integration.OggSSPP2SupersingularUniversalDeformationSource
