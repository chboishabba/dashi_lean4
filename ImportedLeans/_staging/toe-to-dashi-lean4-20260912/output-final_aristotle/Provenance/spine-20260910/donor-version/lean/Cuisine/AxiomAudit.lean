import Cuisine.EndToEnd

/-!
# Axiom audit for the cuisine lane

Building this module prints the axiom dependencies of the lane's headline
results.  Every one of them uses only the standard Lean/Mathlib axioms
(`propext`, `Classical.choice`, `Quot.sound`); none uses `sorry`, a project
axiom, or `Lean.ofReduceBool` (i.e. no `native_decide` anywhere in the lane).
-/

#print axioms Cuisine.EndToEnd.cuisineSpine
#print axioms Cuisine.EndToEnd.cuisine_end_to_end
#print axioms Cuisine.SensoryCore.UmamiBlend.not_additive
#print axioms Cuisine.SensoryCore.UmamiBlend.succ_combined_eq
#print axioms Cuisine.SensoryCore.no_stimulus_only_valence
#print axioms Cuisine.SensoryCore.no_cue_only_safety
#print axioms Cuisine.Surfaces.SurfaceDistinction.ne
#print axioms Cuisine.Surfaces.surfaceDistinction_incomplete
#print axioms Cuisine.Surfaces.no_surface_bijection
#print axioms Cuisine.Lineage.SaucePath.antisymm
#print axioms Cuisine.Lineage.saucePath_iff
#print axioms Cuisine.ProcessRoute.processRouteRel_total
#print axioms Cuisine.ProcessRoute.supplied_witness_does_not_separate_orders
#print axioms Cuisine.ProcessRoute.orders_are_unmergeable
#print axioms Cuisine.ProcessRoute.moleRoute_antisymm
#print axioms Cuisine.DataFlow.no_uniform_promoter
#print axioms Cuisine.DataFlow.isEmpty_promotedClaim_of_no_accepted_source
#print axioms Cuisine.Publication.decisionLevel_publicationDecision
#print axioms Cuisine.Publication.LooseAssessment.publish_with_all_components_high
#print axioms Cuisine.Publication.TightAssessment.abstains_of_any_component_high
#print axioms Cuisine.Publication.TightAssessment.publishes_iff_all_low
#print axioms Cuisine.Provenance.no_three_channel_rule
#print axioms Cuisine.LedgerPattern.cuisinePropositionBoundaryEquivUnit
#print axioms Cuisine.LedgerPattern.no_information_in_ledger
#print axioms Cuisine.ToneSeparation.no_order_three_monotone_selfmap
#print axioms Cuisine.ToneSeparation.severityMonotone_injective_eq_id
#print axioms Cuisine.CarryingCapacity.LooseCapacityProfile.within_while_exceeded
#print axioms Cuisine.CarryingCapacity.TightCapacityProfile.exceeded_iff
#print axioms Cuisine.CarryingCapacity.TightCapacityProfile.never_unknown
#print axioms Cuisine.CarryingCapacity.GuardedCapacityProfile.unknown_of_missing
#print axioms Cuisine.CarryingCapacity.GuardedCapacityProfile.measured_of_within
#print axioms Cuisine.SourceAtlas.sourceIds_nodup
#print axioms Cuisine.Witnesses.agda_regressions
#print axioms Cuisine.Witnesses.agda_route_regressions
#print axioms Cuisine.HyperfabricGuard.admissible_iff_candidate
#print axioms Cuisine.HyperfabricGuard.exists_unique_admissible
#print axioms Cuisine.HyperfabricGuard.surfaceName_injective
#print axioms Cuisine.HyperfabricGuard.no_injective_trit_labelling
#print axioms Cuisine.HyperfabricGuard.canonicalPowerAtlasAxes_nodup
#print axioms Cuisine.HyperfabricGuard.hyperfabric_edge_audit
