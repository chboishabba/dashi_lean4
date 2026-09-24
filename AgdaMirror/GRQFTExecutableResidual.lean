import Integration.GRQFTExecutableResidual

/-!
# Agda mirror receipt: executable GR/QFT residual attempts

Cross-prover discovery surface for the Agda owners

* DASHI/Physics/Foundations/GRQFTStressWeldBidiAttemptExact.agda
* DASHI/Physics/Closure/EinsteinEquationBidiResidualExact.agda

The Lean theorems are statements about the Lean definitions below; path
correspondence does not claim definitional identity between proof assistants.
-/

namespace AgdaMirror.GRQFTExecutableResidual

open Integration.GRQFTExecutableResidual

def agdaRepository : String := "chboishabba/dashi_agda"

structure CrossProverReceipt where
  einsteinResidualAttemptMirrored : Bool
  wrongCouplingCounterexampleMirrored : Bool
  genericStressWeldAttemptMirrored : Bool
  recoveredVsTargetAttemptMirrored : Bool
  physicalCalibrationPromoted : Bool
  pathCorrespondenceIsProofEquivalence : Bool
  deriving Repr

def crossProverReceipt : CrossProverReceipt where
  einsteinResidualAttemptMirrored := true
  wrongCouplingCounterexampleMirrored := true
  genericStressWeldAttemptMirrored := true
  recoveredVsTargetAttemptMirrored := true
  physicalCalibrationPromoted := false
  pathCorrespondenceIsProofEquivalence := false

theorem normalized_attempt_parity :
    runEinsteinEquationAttempt .pos = .exactResidualZero :=
  normalized_attempt_passes

theorem zero_coupling_counterexample_parity :
    runEinsteinEquationAttempt .zero = .nonzeroResidualCounterexample :=
  zero_coupling_attempt_fails

theorem negative_coupling_counterexample_parity :
    runEinsteinEquationAttempt .neg = .nonzeroResidualCounterexample :=
  negative_coupling_attempt_fails

theorem recovery_attempt_without_promotion_parity :
    recoveryAttemptsDoNotRequirePromotionTokens = true :=
  recovery_attempts_do_not_require_promotion_tokens

theorem normalized_coupling_unique_parity
    (coupling : Coupling)
    (h : runEinsteinEquationAttempt coupling = .exactResidualZero) :
    coupling = .pos :=
  normalized_coupling_unique coupling h

theorem w4_hard_negative_parity :
    w4CalibrationBidiReceipt.outcome =
      .currentCandidateRejectedByResidual :=
  current_w4_candidate_rejected

theorem closure_matrix_w4_rejected_parity :
    executableClosureMatrix.currentW4DirtyCalibration =
      .locallyRejected :=
  current_w4_calibration_locally_rejected

theorem calibration_nonpromotion_parity :
    physicalCalibrationStillOpen = true :=
  physical_calibration_still_open

end AgdaMirror.GRQFTExecutableResidual
