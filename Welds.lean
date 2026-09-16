/-
# Consumer welds — aggregate and axiom audit

Opt-in rollup of `Welds.*`.  Each weld attaches an existing domain-neutral Lean
carrier to an existing *real* consumer; nothing here introduces a new lane-local
encoding.  Building this module also prints the axiom receipt for every headline
weld theorem, so the status class "proved theorem" in the lineage ledger
(`Integration.LineageLedger`) has a checkable backing.

`Welds.NSRateBlockPiWeld` depends on the `NSCutset` library, which points at the
verbatim 2026-09-12 donor payload under `Provenance/ns-latest-20260912/`.  That
is why this rollup is not a default build target.
-/
import Welds.NSRateBlockPiWeld
import Welds.ReachabilityCarrierWeld
import Welds.YMVacuumGapBackwardBounds

#print axioms Welds.NSRateBlockPi.ns_herm_eq_euclidean_inner
#print axioms Welds.NSRateBlockPi.ns_nrm_eq_euclidean_norm
#print axioms Welds.NSRateBlockPi.gramOperatorBound_of_pair_estimate
#print axioms Welds.NSRateBlockPi.sum_resForm_le_blockMultiplicity_viaPi
#print axioms Welds.NSRateBlockPi.gramOperatorBound_viaPiCarrier
#print axioms Welds.NSRateBlockPi.spineAdapter_consumer_refactored
#print axioms Welds.NSRateBlockPi.gramOperatorBound_routes_agree

#print axioms Welds.ReachabilityCarrier.reachable_ofStep_iff_reflTransGen
#print axioms Welds.ReachabilityCarrier.reachable_ofStep_of_reachB
#print axioms Welds.ReachabilityCarrier.reachable_ofStep_iff_reachB_of_fixpoint
#print axioms Welds.ReachabilityCarrier.chemistry_barrier_of_invariant
#print axioms Welds.ReachabilityCarrier.reachB_false_of_invariant
#print axioms Welds.ReachabilityCarrier.chemistry_language_index_available
#print axioms Welds.ReachabilityCarrier.reachB_accept_not_language_free

#print axioms Welds.YMVacuumGapBackwardBounds.zeroShiftResolventBound
#print axioms Welds.YMVacuumGapBackwardBounds.weakenGapDatum
#print axioms Welds.YMVacuumGapBackwardBounds.zeroShiftResolventBoundOfGapLowerBound
#print axioms Welds.YMVacuumGapBackwardBounds.continuumZeroShiftResolventBound
