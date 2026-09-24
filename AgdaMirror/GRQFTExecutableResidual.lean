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

theorem direct_gr_target_not_primitive_parity :
    directSelectedGRTargetEqualityPrimitive = false :=
  direct_gr_target_equality_not_primitive

theorem concrete_frontier_finite_einstein_closed_parity :
    concreteInstanceFrontier.finiteEinsteinEquationStillOpen = false :=
  finite_einstein_no_longer_open

theorem calibration_nonpromotion_parity :
    physicalCalibrationStillOpen = true :=
  physical_calibration_still_open

theorem gr_analytic_realization_frontier_parity :
    grAnalyticRealizationFrontier.finiteSourcedEquationClosed = true := rfl

theorem si_local_adapter_present_parity :
    siPhysicalCalibrationBridge.candidate256LocalAdapterPresent = true := rfl

theorem g_physical_coupling_not_promoted_parity :
    einsteinPhysicalCouplingCandidate.physicalCouplingPromoted = false := rfl

theorem pinned_qft_second_stress_theorem_not_required_parity :
    secondQFTStressTheoremRequired = false :=
  second_qft_stress_theorem_not_required

theorem w4_shape_replacement_required_parity :
    w4CalibrationFailureDiagnosis.replacementRequiresPhysicalShapeModel = true :=
  w4_failure_is_shape_not_scalar_unknown

end AgdaMirror.GRQFTExecutableResidual
