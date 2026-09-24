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
  physicalCalibrationPromoted : Bool
  pathCorrespondenceIsProofEquivalence : Bool
  deriving Repr

def crossProverReceipt : CrossProverReceipt where
  einsteinResidualAttemptMirrored := true
  wrongCouplingCounterexampleMirrored := true
  genericStressWeldAttemptMirrored := true
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

theorem calibration_nonpromotion_parity :
    physicalCalibrationStillOpen = true :=
  physical_calibration_still_open

end AgdaMirror.GRQFTExecutableResidual
