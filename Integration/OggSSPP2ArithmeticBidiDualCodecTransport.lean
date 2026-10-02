import Mathlib
import Integration.DependentRecoverableProjection
import Integration.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparation
import Integration.OggSSPP2UniqueGamma0FourMarkingBidi
import Integration.OggSSPP2F4DependentMarkedCover
import Integration.OggSSPP2BalancedTernaryPuncturedPlane
import Integration.OggSSPP2TrialecticNineCentreResidualBidi
import Integration.OggSSPP2DualDependentCodecBidi

/-!
# One arithmetic bidi transports through both exact p=2 codecs

If a future arithmetic source over the unique raw Gamma_0(4) subgroup is
equivalent to the paid ten-state target, then both dependent normal forms are
inherited automatically:

* F4/Frobenius coarse code with fibre profile 1,1,8;
* PhaseNine coarse code with centre-only branch residual.

The two induced source codes commute with the paid dual-codec equivalence.
-/

namespace Integration.OggSSPP2ArithmeticBidiDualCodecTransport

namespace Unique :=
  Integration.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparation
namespace Bidi :=
  Integration.OggSSPP2UniqueGamma0FourMarkingBidi
namespace F4 :=
  Integration.OggSSPP2F4DependentMarkedCover
namespace Plane :=
  Integration.OggSSPP2BalancedTernaryPuncturedPlane
namespace Phase :=
  Integration.OggSSPP2TrialecticNineCentreResidualBidi
namespace Dual :=
  Integration.OggSSPP2DualDependentCodecBidi
namespace D :=
  Integration.DependentRecoverableProjection

abbrev F4DependentCode :=
  D.Code F4.p2F4DependentMarkedProjection

abbrev PhaseDependentCode :=
  D.Code Phase.centreResidualProjection

def encodeArithmeticF4
    {source : Unique.MarkingOverUniqueGamma0FourSubgroup}
    (b : Bidi.Bidi source)
    (s : source.MarkedState) :
    F4DependentCode :=
  F4.encodeMarked (b.toTarget s)

def decodeArithmeticF4
    {source : Unique.MarkingOverUniqueGamma0FourSubgroup}
    (b : Bidi.Bidi source)
    (code : F4DependentCode) :
    source.MarkedState :=
  b.fromTarget (F4.decodeMarked code)

theorem arithmetic_f4_decode_encode
    {source : Unique.MarkingOverUniqueGamma0FourSubgroup}
    (b : Bidi.Bidi source)
    (s : source.MarkedState) :
    decodeArithmeticF4 b (encodeArithmeticF4 b s) = s := by
  simp [decodeArithmeticF4, encodeArithmeticF4,
    F4.decode_encode_marked, b.sourceRoundTrip]

theorem arithmetic_f4_encode_decode
    {source : Unique.MarkingOverUniqueGamma0FourSubgroup}
    (b : Bidi.Bidi source)
    (code : F4DependentCode) :
    encodeArithmeticF4 b (decodeArithmeticF4 b code) = code := by
  unfold encodeArithmeticF4 decodeArithmeticF4
  rw [b.targetRoundTrip]
  exact F4.encode_decode_marked code

def encodeArithmeticPhase
    {source : Unique.MarkingOverUniqueGamma0FourSubgroup}
    (b : Bidi.Bidi source)
    (s : source.MarkedState) :
    PhaseDependentCode :=
  Phase.encode
    (Plane.stratifiedToDuplicatedCentre (b.toTarget s))

def decodeArithmeticPhase
    {source : Unique.MarkingOverUniqueGamma0FourSubgroup}
    (b : Bidi.Bidi source)
    (code : PhaseDependentCode) :
    source.MarkedState :=
  b.fromTarget
    (Plane.duplicatedCentreToStratified (Phase.decode code))

theorem arithmetic_phase_decode_encode
    {source : Unique.MarkingOverUniqueGamma0FourSubgroup}
    (b : Bidi.Bidi source)
    (s : source.MarkedState) :
    decodeArithmeticPhase b (encodeArithmeticPhase b s) = s := by
  unfold decodeArithmeticPhase encodeArithmeticPhase
  rw [Phase.decode_encode]
  rw [Plane.stratified_duplicated_centre_roundtrip]
  exact b.sourceRoundTrip s

theorem arithmetic_phase_encode_decode
    {source : Unique.MarkingOverUniqueGamma0FourSubgroup}
    (b : Bidi.Bidi source)
    (code : PhaseDependentCode) :
    encodeArithmeticPhase b (decodeArithmeticPhase b code) = code := by
  unfold encodeArithmeticPhase decodeArithmeticPhase
  rw [b.targetRoundTrip]
  rw [Plane.duplicated_centre_stratified_roundtrip]
  exact Phase.encode_decode code

theorem arithmetic_f4_to_phase_commutes
    {source : Unique.MarkingOverUniqueGamma0FourSubgroup}
    (b : Bidi.Bidi source)
    (s : source.MarkedState) :
    Dual.f4CodeToPhaseCode (encodeArithmeticF4 b s) =
      encodeArithmeticPhase b s := by
  unfold Dual.f4CodeToPhaseCode encodeArithmeticF4 encodeArithmeticPhase
  rw [F4.decode_encode_marked]

theorem arithmetic_phase_to_f4_commutes
    {source : Unique.MarkingOverUniqueGamma0FourSubgroup}
    (b : Bidi.Bidi source)
    (s : source.MarkedState) :
    Dual.phaseCodeToF4Code (encodeArithmeticPhase b s) =
      encodeArithmeticF4 b s := by
  unfold Dual.phaseCodeToF4Code encodeArithmeticPhase encodeArithmeticF4
  rw [Phase.decode_encode]
  rw [Plane.stratified_duplicated_centre_roundtrip]

structure Boundary where
  arithmeticBidiSufficesForF4Codec : Bool
  arithmeticBidiSufficesForPhaseCodec : Bool
  f4SourceCodecBidiPaidConditionally : Bool
  phaseSourceCodecBidiPaidConditionally : Bool
  dualCodeChangeCommutes : Bool
  separateFiniteCodecRecognitionProofsRequiredAfterBidi : Bool
  arithmeticBidiInhabitedHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  arithmeticBidiSufficesForF4Codec := true
  arithmeticBidiSufficesForPhaseCodec := true
  f4SourceCodecBidiPaidConditionally := true
  phaseSourceCodecBidiPaidConditionally := true
  dualCodeChangeCommutes := true
  separateFiniteCodecRecognitionProofsRequiredAfterBidi := false
  arithmeticBidiInhabitedHere := false

end Integration.OggSSPP2ArithmeticBidiDualCodecTransport
