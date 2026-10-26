import Integration.OggSSP2BCompletionAcquisitionFrontier
import Integration.OggSSP2BBlockIdempotentNaturality
import Integration.OggSSP2BCentralizerNormEquivariance
import Integration.OggSSP2BSocleForcesUnique24
import Integration.OggSSP2BUniqueRangeNormWeld
import Integration.OggSSP2BPostBrauerFinalCompiler

/-!
# Post-socle canonical 2B max-cut

The target-side and formal-algebra search has collapsed.  The residual norm
image no longer requires independent discoveries of equivariance, block
preservation, rank, or a target 24-space:

* centralizer commutation compiles to equivariance of `1+a`;
* module linearity compiles central block naturality;
* equivariance compiles invariant range;
* the existing support/rank squeeze compiles residual rank 24;
* Frobenius-socle containment compiles unique invariant 24 range;
* the unique-range norm weld compiles the Tate cokernel to the exterior-square
  quotient.

Thus the remaining norm-weld scientific input is a single same-object action
instantiation: put the actual C_M(2B)/Co1 module (or group-algebra) action and
the runtime-selected residual block idempotent on the source-native norm
carrier.  This file records that reduction; it does not manufacture that
instantiation or the two remaining Mode5/2T provenance bits.
-/

namespace Integration.OggSSP2BPostSocleMaxCut

structure Status where
  brauerIngressPaid : Bool
  finiteTenAndOuterJ2x5Paid : Bool
  integralTateCokernelPaid : Bool
  frobeniusSocleRigidityPaid : Bool
  residualBlockSelectionPaid : Bool
  normEquivarianceCompilerPaid : Bool
  blockNaturalityCompilerPaid : Bool
  invariantRangeCompilerPaid : Bool
  rankTwentyFourCompilerPaid : Bool
  uniqueRangeCompilerPaid : Bool
  exteriorCokernelCompilerPaid : Bool
  actualCentralizerBlockActionOnNormCarrierPaid : Bool
  actualTateExteriorSquareWeldPaid : Bool
  actualStableQ10AndOuterActionPaid : Bool
  actualThreeFibreQ10TransportPaid : Bool
  remainingNormWeldSameObjectLeaves : Nat
  remainingDefectSourceBits : Nat
  downstream31Paid : Bool
  downstream279Paid : Bool

/-- Current theorem/runtime boundary.  The `true` entries are already-owned
source/runtime/compiler facts; the false entries remain same-object/provenance
obligations. -/
def canonicalStatus : Status where
  brauerIngressPaid := true
  finiteTenAndOuterJ2x5Paid := true
  integralTateCokernelPaid := true
  frobeniusSocleRigidityPaid := true
  residualBlockSelectionPaid := true
  normEquivarianceCompilerPaid := true
  blockNaturalityCompilerPaid := true
  invariantRangeCompilerPaid := true
  rankTwentyFourCompilerPaid := true
  uniqueRangeCompilerPaid := true
  exteriorCokernelCompilerPaid := true
  actualCentralizerBlockActionOnNormCarrierPaid := false
  actualTateExteriorSquareWeldPaid := false
  actualStableQ10AndOuterActionPaid := false
  actualThreeFibreQ10TransportPaid := false
  remainingNormWeldSameObjectLeaves := 1
  remainingDefectSourceBits := 2
  downstream31Paid := false
  downstream279Paid := false

theorem one_norm_weld_same_object_leaf :
    canonicalStatus.remainingNormWeldSameObjectLeaves = 1 := rfl

theorem two_defect_source_bits_remain :
    canonicalStatus.remainingDefectSourceBits = 2 := rfl

theorem actual_action_instantiation_still_open :
    canonicalStatus.actualCentralizerBlockActionOnNormCarrierPaid = false := rfl

theorem actual_tate_exterior_weld_still_open :
    canonicalStatus.actualTateExteriorSquareWeldPaid = false := rfl

end Integration.OggSSP2BPostSocleMaxCut
