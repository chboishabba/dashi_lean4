import Integration.OggSSPSmallCharacteristicRecognition

namespace AgdaMirror.OggSSPSmallCharacteristicRecognition

open Integration.OggSSPSmallCharacteristicRecognition

structure ParityReceipt where
  agdaCodecOwner : String
  agdaCoarseJNoGoOwner : String
  agdaSourceSocketOwner : String
  agdaForwardRecognitionOwner : String
  leanOwner : String

  p2ResidualCodecMirrored : Bool
  p3ResidualCodecMirrored : Bool
  coarseJNoGoMirrored : Bool
  markedSourceSocketsMirrored : Bool
  arithmeticTo369DirectionMirrored : Bool
  actionOrbitStabilizerRecognitionMirrored : Bool
  sourceCapacityTheoremsMirrored : Bool

  actualP2ArithmeticSourceImported : Bool
  actualP3ArithmeticSourceImported : Bool
  actualP2RecognitionImported : Bool
  actualP3RecognitionImported : Bool
  deriving Repr

def canonicalParityReceipt : ParityReceipt where
  agdaCodecOwner :=
    "DASHI/Moonshine/OggSSPSmallCharacteristicResidualCodecExact.agda"
  agdaCoarseJNoGoOwner :=
    "DASHI/Moonshine/OggSSPCoarseSupersingularJRecognitionNoGoExact.agda"
  agdaSourceSocketOwner :=
    "DASHI/Moonshine/OggSSPSmallCharacteristicArithmeticSourceSocketExact.agda"
  agdaForwardRecognitionOwner :=
    "DASHI/Moonshine/OggSSPArithmeticTo369RecognitionExact.agda"
  leanOwner :=
    "Integration/OggSSPSmallCharacteristicRecognition.lean"

  p2ResidualCodecMirrored := true
  p3ResidualCodecMirrored := true
  coarseJNoGoMirrored := true
  markedSourceSocketsMirrored := true
  arithmeticTo369DirectionMirrored := true
  actionOrbitStabilizerRecognitionMirrored := true
  sourceCapacityTheoremsMirrored := true

  actualP2ArithmeticSourceImported := false
  actualP3ArithmeticSourceImported := false
  actualP2RecognitionImported := false
  actualP3RecognitionImported := false

theorem p2_codec_no_left_inverse_parity :
    ¬ ∃ recover : NineOrbit → P2State, Function.LeftInverse recover p2Project :=
  p2_coarse_projection_has_no_left_inverse

theorem p3_codec_no_left_inverse_parity :
    ¬ ∃ recover : P3Orbit → P3State, Function.LeftInverse recover p3Project :=
  p3_coarse_projection_has_no_left_inverse

theorem p2_coarse_j_no_go_parity :
    ¬ ∃ f : CoarseJ → P2State, Function.Surjective f :=
  no_surjection_coarse_j_to_p2_target

theorem p3_coarse_j_no_go_parity :
    ¬ ∃ f : CoarseJ → P3Orbit, Function.Surjective f :=
  no_surjection_coarse_j_to_p3_orbits

end AgdaMirror.OggSSPSmallCharacteristicRecognition
