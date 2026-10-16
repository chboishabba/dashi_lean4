import Integration.OggSSP2BPostSocleMaxCut
import Integration.OggSSP2BSourceActionToExteriorWeld

/-!
# Canonical source-action max-cut for the Monster 2B norm weld

The post-socle search is now complete at the representation-theory level.
Carnahan externally supplies a Monster-stable integral Moonshine form, hence a
mathematical action of the 2B centralizer by restriction.  The direct source-
action compiler proves that, once this externally sourced action is represented
on the formal mod-2 norm carrier, the already-paid rank-24 and Frobenius-socle
receipts force the Tate cokernel to the exterior-square/duad model.

Thus there are no remaining representation-discovery leaves in this part of
the programme.  One formal same-object implementation leaf remains: instantiate
the sourced centralizer action on the actual formal norm carrier.  This file
keeps that distinction explicit and does not claim the literal weld prematurely.

Attribution:
* Carnahan owns the Monster-stable self-dual integral form/external action.
* ATLAS/CTblLib and standard modular representation theory own the local group
  and block data used by the runtime receipts.
* DASHI owns the compiler/composition results in this namespace.
-/

namespace Integration.OggSSP2BSourceActionMaxCut

structure Status where
  externalMonsterStableIntegralActionSourced : Bool
  centralizerActionExistsMathematicallyByRestriction : Bool
  targetRankAndFrobeniusSoclePaid : Bool
  directSourceActionToExteriorCompilerPaid : Bool
  independentBlockProjectorDiscoveryNeeded : Bool

  formalSourceNativeCentralizerActionObjectInRepo : Bool
  literalTateExteriorSquareWeldPaid : Bool
  actualStableQ10AndOuterActionPaid : Bool
  actualThreeFibreQ10TransportPaid : Bool

  remainingRepresentationDiscoveryLeaves : Nat
  remainingFormalCarrierInstantiationLeaves : Nat
  remainingDefectSourceBits : Nat
  downstream31Paid : Bool
  downstream279Paid : Bool

/-- Current honest state after the direct invariant-range compiler. -/
def canonicalStatus : Status where
  externalMonsterStableIntegralActionSourced := true
  centralizerActionExistsMathematicallyByRestriction := true
  targetRankAndFrobeniusSoclePaid := true
  directSourceActionToExteriorCompilerPaid := true
  independentBlockProjectorDiscoveryNeeded := false
  formalSourceNativeCentralizerActionObjectInRepo := false
  literalTateExteriorSquareWeldPaid := false
  actualStableQ10AndOuterActionPaid := false
  actualThreeFibreQ10TransportPaid := false
  remainingRepresentationDiscoveryLeaves := 0
  remainingFormalCarrierInstantiationLeaves := 1
  remainingDefectSourceBits := 2
  downstream31Paid := false
  downstream279Paid := false

theorem no_representation_discovery_leaf_remains :
    canonicalStatus.remainingRepresentationDiscoveryLeaves = 0 := rfl

theorem one_formal_carrier_instantiation_leaf_remains :
    canonicalStatus.remainingFormalCarrierInstantiationLeaves = 1 := rfl

theorem block_projector_is_not_independent_discovery :
    canonicalStatus.independentBlockProjectorDiscoveryNeeded = false := rfl

theorem formal_source_action_still_open :
    canonicalStatus.formalSourceNativeCentralizerActionObjectInRepo = false := rfl

theorem literal_tate_exterior_weld_still_open :
    canonicalStatus.literalTateExteriorSquareWeldPaid = false := rfl

theorem defect_source_bits_remain_two :
    canonicalStatus.remainingDefectSourceBits = 2 := rfl

end Integration.OggSSP2BSourceActionMaxCut
