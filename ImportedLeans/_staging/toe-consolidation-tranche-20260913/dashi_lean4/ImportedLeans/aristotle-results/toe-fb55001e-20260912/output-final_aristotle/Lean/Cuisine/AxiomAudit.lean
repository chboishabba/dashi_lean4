import Cuisine.EndToEnd
import Cuisine.ToeBridge
import Cuisine.TransportKernel
import Cuisine.FourLevelLedger

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

-- The cross-domain transport (`Cuisine.ToeBridge` and the modules it collects).
#print axioms Cuisine.UmamiTransport.umamiFabric_compose
#print axioms Cuisine.UmamiTransport.umamiFabric_surjective
#print axioms Cuisine.UmamiTransport.umamiFabric_cube
#print axioms Cuisine.UmamiTransport.supportMask_umamiFabric_maskIntensity
#print axioms Cuisine.UmamiTransport.maskIntensity_injective
#print axioms Cuisine.UmamiTransport.repDim_eq_maskIntensity_succ
#print axioms Cuisine.UmamiTransport.umamiFabric_season
#print axioms Cuisine.UmamiTransport.dialectic_stage_is_seasoning
#print axioms Cuisine.NineSheet.card_supported
#print axioms Cuisine.NineSheet.card_taste_sheet
#print axioms Cuisine.NineSheet.moonshine_nine_sheet_bridge
#print axioms Cuisine.SafetyFabric.doubtMask_eq_supportMask
#print axioms Cuisine.SafetyFabric.doubtMask_worstField
#print axioms Cuisine.SafetyFabric.safety_projection_contractive
#print axioms Cuisine.SeveritySeam.severity_const_of_monotone_perm
#print axioms Cuisine.SeveritySeam.exists_severity_seam
#print axioms Cuisine.SeveritySeam.hexToSafety_rotate
#print axioms Cuisine.ToeBridge.cuisineToeBridge
#print axioms Cuisine.ToeBridge.cuisine_toe_bridge
#print axioms Cuisine.MdlPrimeModel.mdl_lower_bound
#print axioms Cuisine.MdlPrimeModel.mdl_optimal_iff
#print axioms Cuisine.MdlPrimeModel.mdl_optimal_of_maskIntensity
#print axioms Cuisine.SurfaceInterpretation.interpret_injective
#print axioms Cuisine.SurfaceInterpretation.carrierCard_eq
#print axioms Cuisine.UmamiTransport.fabricZMod_affineOp
#print axioms Cuisine.KnotWeave.observe_injective
#print axioms Cuisine.KnotWeave.knotWeaveEquivTrit_rotate
#print axioms Cuisine.KnotWeave.knotWeaveFabric_rotateField
#print axioms Cuisine.KnotWeave.knotWeave_rotation_is_seasoning
#print axioms Cuisine.KnotWeave.exists_intensity
#print axioms Cuisine.NineSheet.card_fabric_grid
#print axioms Cuisine.SweetgrassSpine.unreachedAnchors_eq
#print axioms Cuisine.SweetgrassSpine.heckeOperatorRole_unused
#print axioms Cuisine.SweetgrassSpine.projectionTarget_image
#print axioms Cuisine.SweetgrassSpine.carrierCard_eq
#print axioms Cuisine.SweetgrassSpine.realised_iff
#print axioms Cuisine.SweetgrassSpine.sweetgrass_spine_realised
#print axioms Cuisine.NonaryAction.fabricPull_fabricRot
#print axioms Cuisine.NonaryAction.nonary_faithful
#print axioms Cuisine.NonaryAction.card_baseInvariant
#print axioms Cuisine.NonaryAction.no_rot_invariant
#print axioms Cuisine.NonaryAction.base_rotation_moves_moonshine
#print axioms Cuisine.NonaryAction.moonshine_preserving_symmetry
#print axioms Cuisine.NonaryAction.card_moonshineInvariant
#print axioms Cuisine.NonaryAction.moonshine_nonary_faithful
#print axioms Cuisine.SpiralCarrier.hint_unique
#print axioms Cuisine.SpiralCarrier.no_injective_klueverForm_to_trit
#print axioms Cuisine.SurfaceInterpretation.spiral_matched
#print axioms Cuisine.SurfaceInterpretation.carrierCard_nodup_except_stage_spiral
#print axioms Cuisine.SupervoxelClopen.neutrality_refines_iff
#print axioms Cuisine.SupervoxelClopen.umamiFabric_eq_iff_ball
#print axioms Cuisine.SupervoxelClopen.no_atomic_ball
#print axioms Cuisine.SupervoxelClopen.cuisineNeutrality_not_atomic
#print axioms Cuisine.SupervoxelClopen.ternaryBallSystem
#print axioms Cuisine.SupervoxelClopen.card_neutralFabric
#print axioms Cuisine.CodecTransport.umamiCodec_compose
#print axioms Cuisine.CodecTransport.umamiCodec_selfBlend
#print axioms Cuisine.CodecTransport.fabricXor_self_ne_fabricInv
#print axioms Cuisine.CodecTransport.blendDoubleOrbits_value
#print axioms Cuisine.LoomBridge.rootOfBucket_bucketFor
#print axioms Cuisine.LoomBridge.loomBucket_refines_root
#print axioms Cuisine.LoomBridge.loomRoot_not_atomic
#print axioms Cuisine.LoomBridge.publicationDecision_not_atomic
#print axioms Cuisine.LoomBridge.no_free_order3_root_preserving
#print axioms Cuisine.FourLevelLedger.fourLevelLedger
#print axioms Cuisine.TransportKernel.umamiFabric_eq_iff
#print axioms Cuisine.TransportKernel.primePow_dvd_self
#print axioms Cuisine.TransportKernel.umamiFabric_eq_zero_iff
#print axioms Cuisine.CodecTransport.fabricShift_conjugates
#print axioms Cuisine.CodecTransport.blendDoubleOrbits_eq_fabricOrbits
