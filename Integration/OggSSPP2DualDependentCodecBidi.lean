import Mathlib
import Integration.DependentRecoverableProjection
import Integration.OggSSPP2F4DependentMarkedCover
import Integration.OggSSPP2BalancedTernaryPuncturedPlane
import Integration.OggSSPP2TrialecticNineCentreResidualBidi

/-!
# Bidi equivalence of the two dependent p=2 codecs

The same ten-state fine target has two exact dependent decompositions:

* F4/Frobenius coarse language with fibre profile 1,1,8;
* trialectic PhaseNine coarse language with a two-branch centre residual and
  unit residual elsewhere.

The change of coarse language is decode -> fine rechart -> encode, with exact
round trips both ways.
-/

namespace Integration.OggSSPP2DualDependentCodecBidi

namespace F4 := Integration.OggSSPP2F4DependentMarkedCover
namespace Plane := Integration.OggSSPP2BalancedTernaryPuncturedPlane
namespace Phase := Integration.OggSSPP2TrialecticNineCentreResidualBidi
namespace D := Integration.DependentRecoverableProjection

abbrev F4DependentCode :=
  D.Code F4.p2F4DependentMarkedProjection

abbrev PhaseDependentCode :=
  D.Code Phase.centreResidualProjection

def f4CodeToPhaseCode (code : F4DependentCode) : PhaseDependentCode :=
  Phase.encode
    (Plane.stratifiedToDuplicatedCentre
      (F4.decodeMarked code))

def phaseCodeToF4Code (code : PhaseDependentCode) : F4DependentCode :=
  F4.encodeMarked
    (Plane.duplicatedCentreToStratified
      (Phase.decode code))

theorem f4_phase_roundtrip (code : F4DependentCode) :
    phaseCodeToF4Code (f4CodeToPhaseCode code) = code := by
  unfold phaseCodeToF4Code f4CodeToPhaseCode
  rw [Phase.decode_encode]
  rw [Plane.stratified_duplicated_centre_roundtrip]
  exact F4.encode_decode_marked code

theorem phase_f4_roundtrip (code : PhaseDependentCode) :
    f4CodeToPhaseCode (phaseCodeToF4Code code) = code := by
  unfold f4CodeToPhaseCode phaseCodeToF4Code
  rw [F4.decode_encode_marked]
  rw [Plane.duplicated_centre_stratified_roundtrip]
  exact Phase.encode_decode code

noncomputable def dualCodecEquiv :
    F4DependentCode ≃ PhaseDependentCode where
  toFun := f4CodeToPhaseCode
  invFun := phaseCodeToF4Code
  left_inv := f4_phase_roundtrip
  right_inv := phase_f4_roundtrip

def f4FineState (code : F4DependentCode) :
    Plane.DuplicatedCentreNineSheet :=
  Plane.stratifiedToDuplicatedCentre (F4.decodeMarked code)

def phaseFineState (code : PhaseDependentCode) :
    Plane.DuplicatedCentreNineSheet :=
  Phase.decode code

theorem f4_to_phase_preserves_fine_state (code : F4DependentCode) :
    phaseFineState (f4CodeToPhaseCode code) = f4FineState code := by
  unfold phaseFineState f4CodeToPhaseCode
  exact Phase.decode_encode _

theorem phase_to_f4_preserves_fine_state (code : PhaseDependentCode) :
    f4FineState (phaseCodeToF4Code code) = phaseFineState code := by
  unfold f4FineState phaseCodeToF4Code phaseFineState
  rw [F4.decode_encode_marked]
  exact Plane.duplicated_centre_stratified_roundtrip _

structure Boundary where
  f4OneOneEightCodecReused : Bool
  phaseNineCentreResidualCodecReused : Bool
  f4ToPhaseCodeConstructed : Bool
  phaseToF4CodeConstructed : Bool
  twoSidedRoundTripsPaid : Bool
  commonFineStatePreservedBothWays : Bool
  coarseSemanticsIdentified : Bool
  arithmeticTrialecticIdentityClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  f4OneOneEightCodecReused := true
  phaseNineCentreResidualCodecReused := true
  f4ToPhaseCodeConstructed := true
  phaseToF4CodeConstructed := true
  twoSidedRoundTripsPaid := true
  commonFineStatePreservedBothWays := true
  coarseSemanticsIdentified := false
  arithmeticTrialecticIdentityClaimed := false

end Integration.OggSSPP2DualDependentCodecBidi
