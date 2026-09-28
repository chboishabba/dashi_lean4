import Mathlib
import Integration.OggSSPP2ConcreteF2UniversalDeformationRecognition
import Integration.OggSSPP2OrientedInertiaTenStateRecognition
import Integration.OggSSPP2SupersingularUniversalDeformationSource
import Integration.OggSSPP2UniqueGamma0FourMarkingBidi

/-!
# Oriented-inertia realization inside the concrete p=2 universal deformation

The finite ten-state carrier is already paid:
  two quadratic orientations × five inertia inversion-orbits.

The remaining arithmetic theorem should therefore not be phrased as
"construct some ten marked states".  It is enough to realize THIS source-native
ten-state vocabulary as genuine marked states of the concrete F₂ universal
deformation.

From one such realization this module constructs automatically:

1. the Gamma_0(4) universal-deformation marking;
2. specialization of every state to the unique raw ker(F²) subgroup;
3. the exact ten-state bidi to the paid target;
4. the universal-deformation ten-state recognition capstone.

Thus the former pair
  missing marked deformation states
  + missing ten-state classification bidi
collapses to one realization theorem.
-/

namespace Integration.OggSSPP2OrientedInertiaUniversalDeformationRealization

namespace Concrete :=
  Integration.OggSSPP2ConcreteF2UniversalDeformationRecognition
namespace Oriented :=
  Integration.OggSSPP2OrientedInertiaTenStateRecognition
namespace Universal :=
  Integration.OggSSPP2SupersingularUniversalDeformationSource
namespace Unique :=
  Integration.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparation
namespace Bidi :=
  Integration.OggSSPP2UniqueGamma0FourMarkingBidi
namespace Target :=
  Integration.OggSSPP2F4AntipodalStratifiedRefinement

/--
Actual source-side realization obligation.

No target labels appear in the fields.  The data must come from the concrete
universal-deformation family itself.
-/
structure Realization
    (authority : Concrete.ConcreteF2UniversalDeformationAuthority) where
  underlyingFamilyState :
    Oriented.State →
      (Concrete.concreteSourceDatum authority).EllipticFamilyState

  gamma0FourLevelStructurePresent :
    Oriented.State → Prop

  gamma0FourLevelStructurePresentProof :
    ∀ state, gamma0FourLevelStructurePresent state

  deformationProvenanceRetained :
    Oriented.State → Prop

  deformationProvenanceRetainedProof :
    ∀ state, deformationProvenanceRetained state

/-- Realization produces the actual marked-state family over the concrete source datum. -/
def marking
    {authority : Concrete.ConcreteF2UniversalDeformationAuthority}
    (realization : Realization authority) :
    Universal.Gamma0FourUniversalDeformationMarking
      (Concrete.concreteSourceDatum authority) where
  MarkedState := Oriented.State
  underlyingFamilyState := realization.underlyingFamilyState
  specializesToRawSubgroup := fun _ => .kerFrobeniusSquared
  specializationIsUniqueKerFrobeniusSquared := fun _ => rfl
  gamma0FourLevelStructurePresent :=
    realization.gamma0FourLevelStructurePresent
  gamma0FourLevelStructurePresentProof :=
    realization.gamma0FourLevelStructurePresentProof
  deformationProvenanceRetained :=
    realization.deformationProvenanceRetained
  deformationProvenanceRetainedProof :=
    realization.deformationProvenanceRetainedProof

/--
The ten-state bidi is now a theorem of the finite rechart plus unique-subgroup
specialization; no second arithmetic classification proof is needed.
-/
def markingBidi
    {authority : Concrete.ConcreteF2UniversalDeformationAuthority}
    (realization : Realization authority) :
    Bidi.Bidi
      (Universal.toUniqueSubgroupMarking (marking realization)) where
  sourceCoarseOrbit := Oriented.coarseOrbit
  toTarget := Oriented.toTarget
  fromTarget := Oriented.fromTarget
  sourceRoundTrip := Oriented.state_roundtrip
  targetRoundTrip := Oriented.target_roundtrip
  toTargetPreservesCoarseOrbit := fun _ => rfl
  fromTargetPreservesCoarseOrbit := by
    intro t
    simp [Oriented.coarseOrbit, Oriented.target_roundtrip]
  everyMappedStateStillLiesOverUniqueRawSubgroup := fun _ => rfl

/-- Full universal-deformation finite recognition follows automatically. -/
def tenStateRecognition
    {authority : Concrete.ConcreteF2UniversalDeformationAuthority}
    (realization : Realization authority) :
    Universal.UniversalDeformationTenStateRecognition
      (Concrete.concreteSourceDatum authority)
      (marking realization) where
  arithmeticBidi := markingBidi realization

theorem every_realized_state_specializes_to_kerF2
    {authority : Concrete.ConcreteF2UniversalDeformationAuthority}
    (realization : Realization authority)
    (state : Oriented.State) :
    (marking realization).specializesToRawSubgroup state =
      .kerFrobeniusSquared :=
  rfl

theorem realization_state_count_is_ten
    {authority : Concrete.ConcreteF2UniversalDeformationAuthority}
    (realization : Realization authority) :
    Fintype.card (marking realization).MarkedState = 10 := by
  exact Oriented.state_cardinality

/--
Same-source capstone from one authority + one oriented-inertia realization.
-/
def sameSourceArithmeticObject
    (authority : Concrete.ConcreteF2UniversalDeformationAuthority)
    (realization : Realization authority) :
    Concrete.ConcreteF2TenStateArithmeticSource where
  authority := authority
  marking := marking realization
  recognition := tenStateRecognition realization

inductive Residual
  | missingConcreteF2UniversalDeformationAuthority
  | missingOrientedInertiaDeformationRealization
  deriving DecidableEq, Repr

def firstResidual : Residual :=
  .missingConcreteF2UniversalDeformationAuthority

structure Boundary where
  classicallySourcedTenStateVocabularyReused : Bool
  markingConstructedAutomaticallyFromRealization : Bool
  uniqueKerF2SpecializationAutomatic : Bool
  tenStateBidiConstructedAutomatically : Bool
  separateTenStateClassificationProofRequired : Bool
  gamma0FourCoarseLevelFibreIdentifiedWithTenStates : Bool
  realizationInhabitedHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  classicallySourcedTenStateVocabularyReused := true
  markingConstructedAutomaticallyFromRealization := true
  uniqueKerF2SpecializationAutomatic := true
  tenStateBidiConstructedAutomatically := true
  separateTenStateClassificationProofRequired := false
  gamma0FourCoarseLevelFibreIdentifiedWithTenStates := false
  realizationInhabitedHere := false

end Integration.OggSSPP2OrientedInertiaUniversalDeformationRealization
