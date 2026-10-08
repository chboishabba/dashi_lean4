import Integration.T5E8IntrinsicRecognitionGate

namespace Integration.T5E8IntrinsicRecognitionGateRegression

open Integration.T5E8IntrinsicRecognitionGate

example : ¬ NaiveOrthogonalityRecognition :=
  naive_orthogonality_recognition_impossible

example : canonicalBoundary.targetGeometryMustPreexistRecognition = true := rfl
example : canonicalBoundary.transportingGeometryThroughBijectionCountsAsIndependentEvidence = false := rfl
example : canonicalBoundary.naiveOrthogonalityCandidateRejected = true := rfl
example : canonicalBoundary.otherIntrinsicGeometriesRemainOpen = true := rfl

end Integration.T5E8IntrinsicRecognitionGateRegression
