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
  f9FrobeniusSixOrbitNoGoMirrored : Bool
  f9FullRecognitionNoGoMirrored : Bool
  f9ExtensionCoordinateQuotientMirrored : Bool
  f9ExtensionCoordinateFailsPi0EmbeddingMirrored : Bool
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
  f9FrobeniusSixOrbitNoGoMirrored := true
  f9FullRecognitionNoGoMirrored := true
  f9ExtensionCoordinateQuotientMirrored := true
  f9ExtensionCoordinateFailsPi0EmbeddingMirrored := true
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

theorem f9_six_orbit_no_go_parity :
    ¬ ∃ f : F9Orbit → P3Orbit, Function.Injective f :=
  no_injective_f9_orbits_to_p3_target

theorem f9_full_recognition_no_go_parity
    (F : Integration.ActionOrbitRecognition.ActionRecognitionFunctor
      f9FrobeniusAction p3Action) :
    ¬ Nonempty
      (Integration.ActionOrbitRecognition.FullRecognition
        F f9OrbitPresentation p3OrbitPresentation) :=
  no_full_f9_frobenius_recognition_to_p3 F

theorem f9_extension_coordinate_surjective_parity :
    Function.Surjective extensionCoordinate :=
  extensionCoordinate_surjective

theorem f9_extension_coordinate_not_pi0_embedding_parity :
    ¬ Nonempty
      (Integration.ActionOrbitRecognition.Pi0Embedding
        f9ExtensionCoordinateOrbitRecognition) :=
  f9_extension_coordinate_not_pi0_embedding

end AgdaMirror.OggSSPSmallCharacteristicRecognition
