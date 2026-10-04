import Integration.OggSSPIndependentBase369Recognition

namespace AgdaMirror.OggSSPIndependentBase369Recognition

open Integration.OggSSPIndependentBase369Recognition

structure ParityReceipt where
  agdaP3Owner : String
  agdaP2Owner : String
  agdaProvenanceOwner : String
  leanOwner : String
  p3ExactRechartMirrored : Bool
  p3FullRecognitionMirrored : Bool
  p3ProvenanceMirrored : Bool
  p2GaugeRecognitionMirrored : Bool
  p2RetainedRecognitionMirrored : Bool
  p2GaugeProvenanceMirrored : Bool
  p2RetainedProvenanceMirrored : Bool
  p2ArithmeticBranchDecisionMirroredAsOpen : Bool
  deriving Repr

def canonicalParityReceipt : ParityReceipt where
  agdaP3Owner :=
    "DASHI/Moonshine/OggSSPP3Base369RecognitionExact.agda"
  agdaP2Owner :=
    "DASHI/Moonshine/OggSSPP2Base369RecognitionForkExact.agda"
  agdaProvenanceOwner :=
    "DASHI/Core/ProvenancePreservingRecognitionFunctorExact.agda"
  leanOwner :=
    "Integration/OggSSPIndependentBase369Recognition.lean"
  p3ExactRechartMirrored := true
  p3FullRecognitionMirrored := true
  p3ProvenanceMirrored := true
  p2GaugeRecognitionMirrored := true
  p2RetainedRecognitionMirrored := true
  p2GaugeProvenanceMirrored := true
  p2RetainedProvenanceMirrored := true
  p2ArithmeticBranchDecisionMirroredAsOpen := true

theorem p3_kernel_ssp_roundtrip_parity (s : Integration.OggSSPSmallCharacteristicRecognition.P3State) :
    sspToKernel (kernelToSSP s) = s :=
  kernel_ssp_roundtrip s

theorem p2_source_target_roundtrip_parity
    (s : Integration.OggSSPSmallCharacteristicRecognition.P2State) :
    p2TargetToSource (p2SourceToTarget s) = s :=
  p2_source_target_roundtrip s

end AgdaMirror.OggSSPIndependentBase369Recognition
