import Integration.Kernel.Instances.ParameterRegion
import Integration.Kernel.Instances.CollectiveAction
import Integration.Kernel.Instances.Distribution
import Integration.Kernel.Instances.Translation
import Integration.Kernel.Instances.Assay
import Integration.Kernel.Instances.ObservationalEquivalence
import Integration.Kernel.Instances.ModelSelection
import Integration.Kernel.Quotient
import Integration.Kernel.Instances.SSSP
import Integration.Kernel.Instances.TemporalFibre
import Integration.Kernel.Instances.Admission
import Integration.Kernel.Instances.SituatedValuation
import Integration.Kernel.Instances.SourceStage
import Integration.Kernel.EvidenceDependence
import Integration.Kernel.ConsumerPromotion
import Integration.Kernel.QueryResidual
import Integration.Kernel.PartialIdentification
import Integration.Kernel.BoundaryKind
import Integration.Kernel.Instances.ProjectionHierarchy
import Integration.Kernel.DeclaredRealised
import Integration.Kernel.AppendOnlyHistory
import Integration.Kernel.BraidedTrace
import Integration.Kernel.LineageEdge
import Integration.Kernel.PromotionTransport
import Integration.Kernel.Welds.RuntimeBraidedProvenance
import Integration.Kernel.Welds.AmplifiedObservationCount
import Integration.Kernel.Welds.RemedyRuntimeFeedback
import Integration.Kernel.Welds.SituatedMediationCarriers
import Integration.Kernel.Welds.ResidualSalienceScheduler
import Integration.Kernel.Welds.DeliberativeMoves
import Integration.Kernel.Welds.CommutingProvenanceSquare
import Integration.Kernel.Bridges.QuorumThreshold
import Integration.Kernel.Bridges.InformationLossLocus
import Integration.Kernel.Bridges.CorroborationPhase
import Integration.Kernel.Welds.LaneProjectionSquare
import Integration.Kernel.Welds.SalienceOverLineage

/-!
# Axiom audit for the shared inference kernel

`#print axioms` for every theorem of `Integration.Kernel.*` and of its
instances.  Each line must report only a subset of
`{propext, Classical.choice, Quot.sound}`; nothing here may depend on a project
axiom, `sorry`, or `Lean.ofReduceBool`.
-/

/-! ### Integration.Kernel.ResidualFibre -/

#print axioms Integration.Kernel.ResidualFibre.refines_iff_subset
#print axioms Integration.Kernel.ResidualFibre.refines_trans
#print axioms Integration.Kernel.ResidualFibre.refines_antisymm
#print axioms Integration.Kernel.ResidualFibre.refines_empty
#print axioms Integration.Kernel.ResidualFibre.refines_univ
#print axioms Integration.Kernel.ResidualFibre.mem_event
#print axioms Integration.Kernel.ResidualFibre.mem_refine
#print axioms Integration.Kernel.ResidualFibre.refineBy_refines
#print axioms Integration.Kernel.ResidualFibre.refine_refines
#print axioms Integration.Kernel.ResidualFibre.refine_mono
#print axioms Integration.Kernel.ResidualFibre.refine_idem
#print axioms Integration.Kernel.ResidualFibre.refine_comm
#print axioms Integration.Kernel.ResidualFibre.truth_survives
#print axioms Integration.Kernel.ResidualFibre.refine_nonempty_of_truth
#print axioms Integration.Kernel.ResidualFibre.refineAll_refines
#print axioms Integration.Kernel.ResidualFibre.refineAll_mono
#print axioms Integration.Kernel.ResidualFibre.refineAll_append
#print axioms Integration.Kernel.ResidualFibre.refineAll_append_refines
#print axioms Integration.Kernel.ResidualFibre.mem_refineAll_of_forall
#print axioms Integration.Kernel.ResidualFibre.determines_mono
#print axioms Integration.Kernel.ResidualFibre.determines_empty
#print axioms Integration.Kernel.ResidualFibre.determines_iff_not_collision
#print axioms Integration.Kernel.ResidualFibre.determines_of_factors
#print axioms Integration.Kernel.ResidualFibre.narrower_not_mechanism
#print axioms Integration.Kernel.ResidualFibre.decision_safe_not_mechanism
#print axioms Integration.Kernel.ResidualFibre.witness_coordinates_nonconstant

/-! ### Integration.Kernel.Probe -/

#print axioms Integration.Kernel.Probe.refine_eq_self_of_constant
#print axioms Integration.Kernel.Probe.unachievable_outcome_empties
#print axioms Integration.Kernel.Probe.strictly_refines_iff_discriminates
#print axioms Integration.Kernel.Probe.resolves_of_factors
#print axioms Integration.Kernel.Probe.resolving_probe_closes
#print axioms Integration.Kernel.Probe.collision_persists_of_constant
#print axioms Integration.Kernel.Probe.discriminating_probe_need_not_resolve
#print axioms Integration.Kernel.Probe.refineAll_readingEvents_refines
#print axioms Integration.Kernel.Probe.AndNode.contribution_refines
#print axioms Integration.Kernel.Probe.flatMap_targets_eq_nil
#print axioms Integration.Kernel.Probe.AndNode.contribution_eq_of_vacuous
#print axioms Integration.Kernel.Probe.vacuous_success_is_not_resolution
#print axioms Integration.Kernel.Probe.real_target_resolves

/-! ### Integration.Kernel.Merge -/

#print axioms Integration.Kernel.Merge.threeWay_refines_left
#print axioms Integration.Kernel.Merge.threeWay_refines_right
#print axioms Integration.Kernel.Merge.threeWay_refines_base
#print axioms Integration.Kernel.Merge.threeWay_comm
#print axioms Integration.Kernel.Merge.threeWay_assoc
#print axioms Integration.Kernel.Merge.fastForward_refines
#print axioms Integration.Kernel.Merge.provedJoin_refines_base
#print axioms Integration.Kernel.Merge.guarded_refines_base
#print axioms Integration.Kernel.Merge.guarded_never_weakens_base
#print axioms Integration.Kernel.Merge.merge_preserves_truth
#print axioms Integration.Kernel.Merge.merge_preserves_determination
#print axioms Integration.Kernel.Merge.fastForward_eq_threeWay_of_not_diverged
#print axioms Integration.Kernel.Merge.threeWay_can_refute
#print axioms Integration.Kernel.Merge.fastForward_ne_threeWay
#print axioms Integration.Kernel.Merge.provedJoin_ne_threeWay
#print axioms Integration.Kernel.Merge.guarded_ne_threeWay
#print axioms Integration.Kernel.Merge.guarded_ne_fastForward

/-! ### Integration.Kernel.Authority -/

#print axioms Integration.Kernel.Authority.telemetry_layers_separate
#print axioms Integration.Kernel.Authority.rational_wrt_report_not_rational_wrt_truth
#print axioms Integration.Kernel.Authority.faithful_credulous_transfers
#print axioms Integration.Kernel.Authority.report_cannot_certify_itself
#print axioms Integration.Kernel.Authority.strengthPreserving_not_weakens
#print axioms Integration.Kernel.Authority.weakening_manufactures_satisfaction
#print axioms Integration.Kernel.Authority.satisfies_of_strength_preserving
#print axioms Integration.Kernel.Authority.authorised_revision_composes
#print axioms Integration.Kernel.Authority.authorised_chain_not_weakening

/-! ### Integration.Kernel.Reopen -/

#print axioms Integration.Kernel.Reopen.mem_reopened_iff
#print axioms Integration.Kernel.Reopen.reopen_of_revised_edge
#print axioms Integration.Kernel.Reopen.stays_closed_of_disjoint
#print axioms Integration.Kernel.Reopen.reopened_mono
#print axioms Integration.Kernel.Reopen.reopened_union
#print axioms Integration.Kernel.Reopen.reopening_is_selective
#print axioms Integration.Kernel.Reopen.reopen_propagates
#print axioms Integration.Kernel.Reopen.closedAfter_subset
#print axioms Integration.Kernel.Reopen.unaffected_stays_closed
#print axioms Integration.Kernel.Reopen.closedAfter_antitone
#print axioms Integration.Kernel.Reopen.no_rule_recovers_origin
#print axioms Integration.Kernel.Reopen.value_agreement_is_not_lineage_agreement

/-! ### Integration.Kernel.Loop -/

#print axioms Integration.Kernel.Loop.step_refines
#print axioms Integration.Kernel.Loop.run_succ_refines
#print axioms Integration.Kernel.Loop.run_antitone
#print axioms Integration.Kernel.Loop.run_refines
#print axioms Integration.Kernel.Loop.truth_mem_run
#print axioms Integration.Kernel.Loop.run_nonempty
#print axioms Integration.Kernel.Loop.step_strict_of_discriminates
#print axioms Integration.Kernel.Loop.responsive_run_card
#print axioms Integration.Kernel.Loop.responsive_policy_closes
#print axioms Integration.Kernel.Loop.closure_is_consumer_relative
#print axioms Integration.Kernel.Loop.unresponsive_policy_never_closes
#print axioms Integration.Kernel.Loop.strategy_merges_iff
#print axioms Integration.Kernel.Loop.strategy_needs_both_coordinates
#print axioms Integration.Kernel.Loop.branches_merge_refines
#print axioms Integration.Kernel.Loop.merge_preserves_truth_of_runs

/-! ### Integration.Kernel.Instances.ParameterRegionBridge -/

#print axioms Integration.Kernel.Instances.ParameterRegionBridge.fitEvent_eq_preimage
#print axioms Integration.Kernel.Instances.ParameterRegionBridge.refineAll_fitEvents
#print axioms Integration.Kernel.Instances.ParameterRegionBridge.compatible_eq_refineAll
#print axioms Integration.Kernel.Instances.ParameterRegionBridge.compatible_refines_prior
#print axioms Integration.Kernel.Instances.ParameterRegionBridge.evidence_refines
#print axioms Integration.Kernel.Instances.ParameterRegionBridge.truth_survives_kernel
#print axioms Integration.Kernel.Instances.ParameterRegionBridge.envelope_subsingleton_of_determines
#print axioms Integration.Kernel.Instances.ParameterRegionBridge.determines_of_envelope_subsingleton
#print axioms Integration.Kernel.Instances.ParameterRegionBridge.region_narrowing_is_not_identification

/-! ### Integration.Kernel.Instances.CollectiveAction -/

#print axioms Integration.Kernel.Instances.CollectiveAction.modes_pairwise_independent
#print axioms Integration.Kernel.Instances.CollectiveAction.organisation_without_expansion
#print axioms Integration.Kernel.Instances.CollectiveAction.effectiveOrganisation_expands
#print axioms Integration.Kernel.Instances.CollectiveAction.effective_organisation_exists
#print axioms Integration.Kernel.Instances.CollectiveAction.expansion_is_not_refinement
#print axioms Integration.Kernel.Instances.CollectiveAction.join_preserves_inputs
#print axioms Integration.Kernel.Instances.CollectiveAction.join_irreducible
#print axioms Integration.Kernel.Instances.CollectiveAction.opposition_is_not_synthesis
#print axioms Integration.Kernel.Instances.CollectiveAction.productive_join_exists

/-! ### Integration.Kernel.Instances.Distribution -/

#print axioms Integration.Kernel.Instances.Distribution.aggregate_hides_distribution
#print axioms Integration.Kernel.Instances.Distribution.equal_cost_not_equal_burden
#print axioms Integration.Kernel.Instances.Distribution.equal_cost_not_equal_benefit
#print axioms Integration.Kernel.Instances.Distribution.equal_cost_not_equal_voice
#print axioms Integration.Kernel.Instances.Distribution.cheapest_is_not_least_burdensome
#print axioms Integration.Kernel.Instances.Distribution.cost_is_not_a_function_of_burden
#print axioms Integration.Kernel.Instances.Distribution.burden_is_not_a_function_of_cost

/-! ### Integration.Kernel.Instances.Translation -/

#print axioms Integration.Kernel.Instances.Translation.translation_preserves_clinical
#print axioms Integration.Kernel.Instances.Translation.translation_erases_subject
#print axioms Integration.Kernel.Instances.Translation.erased_coordinate_is_unrecoverable
#print axioms Integration.Kernel.Instances.Translation.reintroduction_is_not_restoration
#print axioms Integration.Kernel.Instances.Translation.reinterpret_institutionalise_noncommute
#print axioms Integration.Kernel.Instances.Translation.same_present_vocabulary_not_same_history
#print axioms Integration.Kernel.Instances.Translation.same_future_cone_not_same_transport_history
#print axioms Integration.Kernel.Instances.Translation.coarse_code_is_not_a_history_certificate

/-! ### Integration.Kernel.Instances.Assay -/

#print axioms Integration.Kernel.Instances.Assay.documented_contribution
#print axioms Integration.Kernel.Instances.Assay.assay_narrows_but_does_not_resolve
#print axioms Integration.Kernel.Instances.Assay.assay_vacuously_succeeds
#print axioms Integration.Kernel.Instances.Assay.assay_collision_survives_vacuous_success
#print axioms Integration.Kernel.Instances.Assay.new_measurement_separates
#print axioms Integration.Kernel.Instances.Assay.reinterpretation_does_not_separate

/-! ### Integration.Kernel.Instances.ObservationalEquivalenceBridge -/

#print axioms Integration.Kernel.Instances.ObservationalEquivalenceBridge.refineAll_agreesEvents
#print axioms Integration.Kernel.Instances.ObservationalEquivalenceBridge.obsClass_eq_refineAll
#print axioms Integration.Kernel.Instances.ObservationalEquivalenceBridge.obsClass_append_eq_refineAll
#print axioms Integration.Kernel.Instances.ObservationalEquivalenceBridge.obsClass_append_refines
#print axioms Integration.Kernel.Instances.ObservationalEquivalenceBridge.separates_iff_discriminates
#print axioms Integration.Kernel.Instances.ObservationalEquivalenceBridge.strictly_refines_iff_separates
#print axioms Integration.Kernel.Instances.ObservationalEquivalenceBridge.redundant_experiment_does_not_refine
#print axioms Integration.Kernel.Instances.ObservationalEquivalenceBridge.class_narrowing_is_not_theory_identification

/-! ### Integration.Kernel.Instances.ModelSelectionBridge -/

#print axioms Integration.Kernel.Instances.ModelSelectionBridge.traceAgree_exact_iff
#print axioms Integration.Kernel.Instances.ModelSelectionBridge.exact_agreeEvent_eq_event
#print axioms Integration.Kernel.Instances.ModelSelectionBridge.refined_admissibleSet_eq_refineBy
#print axioms Integration.Kernel.Instances.ModelSelectionBridge.refineAll_agreeEvents
#print axioms Integration.Kernel.Instances.ModelSelectionBridge.refineAll_observations
#print axioms Integration.Kernel.Instances.ModelSelectionBridge.refined_refines_prior
#print axioms Integration.Kernel.Instances.ModelSelectionBridge.truth_survives_kernel
#print axioms Integration.Kernel.Instances.ModelSelectionBridge.identical_traces_are_a_persistent_collision
#print axioms Integration.Kernel.Instances.ModelSelectionBridge.coarser_instrument_refines_less
#print axioms Integration.Kernel.Instances.ModelSelectionBridge.refutation_empties_the_fibre

/-! ### Integration.Kernel.Quotient -/

#print axioms Integration.Kernel.Quotient.obsEq_iff
#print axioms Integration.Kernel.Quotient.obsEq_equivalence
#print axioms Integration.Kernel.Quotient.self_mem_fibre
#print axioms Integration.Kernel.Quotient.fibre_eq_refine_univ
#print axioms Integration.Kernel.Quotient.refinedBy_trans
#print axioms Integration.Kernel.Quotient.refinedBy_of_descends
#print axioms Integration.Kernel.Quotient.descendsThrough_iff_refinedBy
#print axioms Integration.Kernel.Quotient.no_descent_to_empty_consumer
#print axioms Integration.Kernel.Quotient.not_descendsThrough_of_collision
#print axioms Integration.Kernel.Quotient.determines_of_descends
#print axioms Integration.Kernel.Quotient.descends_of_determines_all
#print axioms Integration.Kernel.Quotient.descent_is_consumer_relative
#print axioms Integration.Kernel.Quotient.refinedBy_pair_left
#print axioms Integration.Kernel.Quotient.refinedBy_pair_right
#print axioms Integration.Kernel.Quotient.refinement_is_not_refutation
#print axioms Integration.Kernel.Quotient.strictlyRefines_pair_of_separates
#print axioms Integration.Kernel.Quotient.fibre_pair_subset
#print axioms Integration.Kernel.Quotient.fibre_pair_ssubset
#print axioms Integration.Kernel.Quotient.residual_does_not_descend
#print axioms Integration.Kernel.Quotient.mapDescends_iff_classPreserving
#print axioms Integration.Kernel.Quotient.dynamics_need_not_descend
#print axioms Integration.Kernel.Quotient.invertsFor_of_inverts
#print axioms Integration.Kernel.Quotient.invertsFor_not_inverts
#print axioms Integration.Kernel.Quotient.invertsFor_of_descends
#print axioms Integration.Kernel.Quotient.Reopening.pair_injective
#print axioms Integration.Kernel.Quotient.Reopening.relativeFine_separates_inside_coarse_class
#print axioms Integration.Kernel.Quotient.Reopening.fibre_pair_eq_singleton
#print axioms Integration.Kernel.Quotient.exists_reopening_of_injective

/-! ### Integration.Kernel.Instances.SSSP -/

#print axioms Integration.Kernel.Instances.SSSP.card_order3
#print axioms Integration.Kernel.Instances.SSSP.orderEquiv_apply
#print axioms Integration.Kernel.Instances.SSSP.pair_bijective
#print axioms Integration.Kernel.Instances.SSSP.abc_ne_acb
#print axioms Integration.Kernel.Instances.SSSP.min_collides
#print axioms Integration.Kernel.Instances.SSSP.tail_separates
#print axioms Integration.Kernel.Instances.SSSP.sheet_ne
#print axioms Integration.Kernel.Instances.SSSP.sheet_injective
#print axioms Integration.Kernel.Instances.SSSP.tail_does_not_descend
#print axioms Integration.Kernel.Instances.SSSP.minVertex_descends_through_sheet
#print axioms Integration.Kernel.Instances.SSSP.fibre_card
#print axioms Integration.Kernel.Instances.SSSP.tail_refines_strictly
#print axioms Integration.Kernel.Instances.SSSP.min_still_correct_after_refinement
#print axioms Integration.Kernel.Instances.SSSP.refined_observation_separates

/-! ### Integration.Kernel.Instances.TemporalFibre -/

#print axioms Integration.Kernel.Instances.TemporalFibre.lawfulTransport_refl
#print axioms Integration.Kernel.Instances.TemporalFibre.lawfulTransport_trans
#print axioms Integration.Kernel.Instances.TemporalFibre.no_backward_transport
#print axioms Integration.Kernel.Instances.TemporalFibre.static_universe_is_pit_iff_constant
#print axioms Integration.Kernel.Instances.TemporalFibre.membership_changes
#print axioms Integration.Kernel.Instances.TemporalFibre.static_universe_misclassifies
#print axioms Integration.Kernel.Instances.TemporalFibre.static_entrant_not_pit
#print axioms Integration.Kernel.Instances.TemporalFibre.feature_collides
#print axioms Integration.Kernel.Instances.TemporalFibre.dependence_separates
#print axioms Integration.Kernel.Instances.TemporalFibre.universe_dependence_does_not_descend
#print axioms Integration.Kernel.Instances.TemporalFibre.dependence_strictly_refines
#print axioms Integration.Kernel.Instances.TemporalFibre.features_still_correct
#print axioms Integration.Kernel.Instances.TemporalFibre.feature_pit_does_not_give_universe_pit

/-! ### Integration.Kernel.Instances.Admission -/

#print axioms Integration.Kernel.Instances.Admission.admits_iff_hasValidReceipt
#print axioms Integration.Kernel.Instances.Admission.parser_receipt_never_valid
#print axioms Integration.Kernel.Instances.Admission.receipt_for_other_candidate_never_valid
#print axioms Integration.Kernel.Instances.Admission.resolve_is_lossless
#print axioms Integration.Kernel.Instances.Admission.resolve_failure
#print axioms Integration.Kernel.Instances.Admission.resolve_admitted_iff
#print axioms Integration.Kernel.Instances.Admission.common_admissible
#print axioms Integration.Kernel.Instances.Admission.rival_not_admissible
#print axioms Integration.Kernel.Instances.Admission.frequencies_agree
#print axioms Integration.Kernel.Instances.Admission.scores_agree
#print axioms Integration.Kernel.Instances.Admission.admission_does_not_descend_through_frequency
#print axioms Integration.Kernel.Instances.Admission.admission_does_not_descend_through_score
#print axioms Integration.Kernel.Instances.Admission.admission_monotone_in_receipts
#print axioms Integration.Kernel.Instances.Admission.admission_is_not_monotone_in_candidates

/-! ### Integration.Kernel.Instances.SituatedValuation -/

#print axioms Integration.Kernel.Instances.SituatedValuation.code_pos
#print axioms Integration.Kernel.Instances.SituatedValuation.code_ne_zero
#print axioms Integration.Kernel.Instances.SituatedValuation.valuation_ne_zero
#print axioms Integration.Kernel.Instances.SituatedValuation.lexical_collides
#print axioms Integration.Kernel.Instances.SituatedValuation.valuation_separates
#print axioms Integration.Kernel.Instances.SituatedValuation.no_static_lexicon
#print axioms Integration.Kernel.Instances.SituatedValuation.situated_descends_through_full_context
#print axioms Integration.Kernel.Instances.SituatedValuation.world_strictly_refines_lexicon
#print axioms Integration.Kernel.Instances.SituatedValuation.lexicon_still_correct
#print axioms Integration.Kernel.Instances.SituatedValuation.flip_is_an_ambient_inverse
#print axioms Integration.Kernel.Instances.SituatedValuation.flip_involutive
#print axioms Integration.Kernel.Instances.SituatedValuation.lawfulFlip_is_ambient
#print axioms Integration.Kernel.Instances.SituatedValuation.lawful_flip_exists
#print axioms Integration.Kernel.Instances.SituatedValuation.ambient_inverse_is_not_lawful
#print axioms Integration.Kernel.Instances.SituatedValuation.gate_does_not_descend_through_valuation

/-! ### Integration.Kernel.Instances.SourceStage -/

#print axioms Integration.Kernel.Instances.SourceStage.announcement_collides
#print axioms Integration.Kernel.Instances.SourceStage.stages_differ
#print axioms Integration.Kernel.Instances.SourceStage.announcement_does_not_descend
#print axioms Integration.Kernel.Instances.SourceStage.announcement_only_constants
#print axioms Integration.Kernel.Instances.SourceStage.stage_refines_announcement
#print axioms Integration.Kernel.Instances.SourceStage.stage_strictly_refines
#print axioms Integration.Kernel.Instances.SourceStage.inhabits_iff_proofTerm
#print axioms Integration.Kernel.Instances.SourceStage.receipt_does_not_inhabit
#print axioms Integration.Kernel.Instances.SourceStage.certificate_does_not_inhabit
#print axioms Integration.Kernel.Instances.SourceStage.correspondence_does_not_inhabit
#print axioms Integration.Kernel.Instances.SourceStage.every_non_proof_carrier_fails_to_inhabit
#print axioms Integration.Kernel.Instances.SourceStage.bundleInhabits_iff_mem
#print axioms Integration.Kernel.Instances.SourceStage.bundleInhabits_iff_exists_member
#print axioms Integration.Kernel.Instances.SourceStage.bundle_without_proof_term_does_not_inhabit
#print axioms Integration.Kernel.Instances.SourceStage.no_combination_of_non_proof_carriers
#print axioms Integration.Kernel.Instances.SourceStage.bundleInhabits_insert_of_ne
#print axioms Integration.Kernel.Instances.SourceStage.flag_true_without_witness
#print axioms Integration.Kernel.Instances.SourceStage.flags_collide
#print axioms Integration.Kernel.Instances.SourceStage.witnesses_differ
#print axioms Integration.Kernel.Instances.SourceStage.flag_does_not_determine_witness
#print axioms Integration.Kernel.Instances.SourceStage.inhabited_refines_witness
#print axioms Integration.Kernel.Instances.SourceStage.inhabited_does_not_descend_through_flag
#print axioms Integration.Kernel.Instances.SourceStage.recovery_is_refinement_not_refutation
#print axioms Integration.Kernel.Instances.SourceStage.recovery_strictly_narrows
#print axioms Integration.Kernel.Instances.SourceStage.same_announcement_different_provenance

/-! ### Integration.Kernel.EvidenceDependence -/

#print axioms Integration.Kernel.EvidenceDependence.independent_iff_disjoint_roots
#print axioms Integration.Kernel.EvidenceDependence.sharesRoot_iff_exists_common_root
#print axioms Integration.Kernel.EvidenceDependence.not_independent_iff_sharesRoot
#print axioms Integration.Kernel.EvidenceDependence.shared_root_blocks_independent_replication
#print axioms Integration.Kernel.EvidenceDependence.independent_symm
#print axioms Integration.Kernel.EvidenceDependence.sharesRoot_symm
#print axioms Integration.Kernel.EvidenceDependence.not_independent_self
#print axioms Integration.Kernel.EvidenceDependence.independent_of_subset
#print axioms Integration.Kernel.EvidenceDependence.sharesRoot_not_transitive
#print axioms Integration.Kernel.EvidenceDependence.rootSupport_nil
#print axioms Integration.Kernel.EvidenceDependence.rootSupport_cons
#print axioms Integration.Kernel.EvidenceDependence.roots_subset_rootSupport
#print axioms Integration.Kernel.EvidenceDependence.card_roots_union_of_independent
#print axioms Integration.Kernel.EvidenceDependence.card_roots_union_lt_of_shared
#print axioms Integration.Kernel.EvidenceDependence.amplification_is_not_generation
#print axioms Integration.Kernel.EvidenceDependence.count_does_not_determine_root_support
#print axioms Integration.Kernel.EvidenceDependence.independent_of_different_class
#print axioms Integration.Kernel.EvidenceDependence.class_agreement_is_not_dependence
#print axioms Integration.Kernel.EvidenceDependence.class_descends_of_roots_determine

/-! ### Integration.Kernel.ConsumerPromotion -/

#print axioms Integration.Kernel.ConsumerPromotion.adequateFor_iff
#print axioms Integration.Kernel.ConsumerPromotion.adequateFor_mono
#print axioms Integration.Kernel.ConsumerPromotion.adequateFor_required
#print axioms Integration.Kernel.ConsumerPromotion.bridge_refl
#print axioms Integration.Kernel.ConsumerPromotion.bridge_trans
#print axioms Integration.Kernel.ConsumerPromotion.adequate_transfer
#print axioms Integration.Kernel.ConsumerPromotion.bridge_iff_transfers
#print axioms Integration.Kernel.ConsumerPromotion.adequacy_is_consumer_relative
#print axioms Integration.Kernel.ConsumerPromotion.no_silent_transfer
#print axioms Integration.Kernel.ConsumerPromotion.adequacy_does_not_descend_through_bundle
#print axioms Integration.Kernel.ConsumerPromotion.no_receipt_without_adequacy
#print axioms Integration.Kernel.ConsumerPromotion.Receipt.transfer_bundle
#print axioms Integration.Kernel.ConsumerPromotion.receipt_does_not_transfer_without_bridge
#print axioms Integration.Kernel.ConsumerPromotion.independence_required_is_a_separate_gate

/-! ### Integration.Kernel.QueryResidual -/

#print axioms Integration.Kernel.QueryResidual.firstResidual_mem_cutset
#print axioms Integration.Kernel.QueryResidual.firstResidual_isOpen
#print axioms Integration.Kernel.QueryResidual.closed_iff_all_closed
#print axioms Integration.Kernel.QueryResidual.no_work_when_closed
#print axioms Integration.Kernel.QueryResidual.work_isSome_of_residual
#print axioms Integration.Kernel.QueryResidual.work_factors_through_first_residual
#print axioms Integration.Kernel.QueryResidual.same_residual_same_work
#print axioms Integration.Kernel.QueryResidual.resolve_self
#print axioms Integration.Kernel.QueryResidual.resolve_of_ne
#print axioms Integration.Kernel.QueryResidual.resolve_preserves_closed
#print axioms Integration.Kernel.QueryResidual.resolve_removes_residual
#print axioms Integration.Kernel.QueryResidual.closed_of_closed_resolve
#print axioms Integration.Kernel.QueryResidual.residual_is_query_relative
#print axioms Integration.Kernel.QueryResidual.residual_does_not_descend_through_state
#print axioms Integration.Kernel.QueryResidual.residual_does_not_descend_through_query
#print axioms Integration.Kernel.QueryResidual.residual_descends_through_pair

/-! ### Integration.Kernel.PartialIdentification -/

#print axioms Integration.Kernel.PartialIdentification.compatible_eq_fibre
#print axioms Integration.Kernel.PartialIdentification.mem_compatible
#print axioms Integration.Kernel.PartialIdentification.truth_is_never_excluded
#print axioms Integration.Kernel.PartialIdentification.compatible_nonempty
#print axioms Integration.Kernel.PartialIdentification.pointIdentified_iff_compatible_singleton
#print axioms Integration.Kernel.PartialIdentification.not_pointIdentified_of_collision
#print axioms Integration.Kernel.PartialIdentification.explanation_does_not_descend
#print axioms Integration.Kernel.PartialIdentification.fibre_answer_descends
#print axioms Integration.Kernel.PartialIdentification.compatible_injOn_range
#print axioms Integration.Kernel.PartialIdentification.fibre_closes_while_point_stays_open
#print axioms Integration.Kernel.PartialIdentification.compatible_pair_subset
#print axioms Integration.Kernel.PartialIdentification.compatible_pair_ssubset
#print axioms Integration.Kernel.PartialIdentification.reopening_gives_point_identification
#print axioms Integration.Kernel.PartialIdentification.no_point_identification_without_separation

/-! ### Integration.Kernel.BoundaryKind -/

#print axioms Integration.Kernel.BoundaryKind.kind_does_not_descend_through_transition
#print axioms Integration.Kernel.BoundaryKind.transition_does_not_descend_through_kind
#print axioms Integration.Kernel.BoundaryKind.only_constants_descend_through_transition
#print axioms Integration.Kernel.BoundaryKind.pair_refines_transition
#print axioms Integration.Kernel.BoundaryKind.pair_refines_kind
#print axioms Integration.Kernel.BoundaryKind.pair_strictly_refines_transition
#print axioms Integration.Kernel.BoundaryKind.pooling_by_transition_merges_mechanisms
#print axioms Integration.Kernel.BoundaryKind.kinds_are_pairwise_distinct
#print axioms Integration.Kernel.BoundaryKind.patent_publication_is_not_declassification
#print axioms Integration.Kernel.BoundaryKind.proprietary_period_is_not_classification
#print axioms Integration.Kernel.BoundaryKind.export_control_is_not_classification
#print axioms Integration.Kernel.BoundaryKind.every_mechanism_shares_the_transition
#print axioms Integration.Kernel.BoundaryKind.released_publicly_does_not_determine_mechanism
#print axioms Integration.Kernel.BoundaryKind.no_transition_level_test_separates_mechanisms
#print axioms Integration.Kernel.BoundaryKind.like_for_like_requires_the_kind_coordinate
#print axioms Integration.Kernel.BoundaryKind.mechanism_refines_the_release_record

/-! ### Integration.Kernel.Instances.ProjectionHierarchy -/

#print axioms Integration.Kernel.Instances.ProjectionHierarchy.oneWay_refined_by_pairwise
#print axioms Integration.Kernel.Instances.ProjectionHierarchy.oneWay_descends_through_pairwise
#print axioms Integration.Kernel.Instances.ProjectionHierarchy.pairwise_descends_through_cube
#print axioms Integration.Kernel.Instances.ProjectionHierarchy.contrast_cubes_agree_on_every_margin
#print axioms Integration.Kernel.Instances.ProjectionHierarchy.contrast_cubes_differ_on_pairwise
#print axioms Integration.Kernel.Instances.ProjectionHierarchy.pairwise_does_not_descend_through_oneWay
#print axioms Integration.Kernel.Instances.ProjectionHierarchy.parity_cubes_agree_on_every_pairwise_table
#print axioms Integration.Kernel.Instances.ProjectionHierarchy.parity_cubes_agree_on_every_margin
#print axioms Integration.Kernel.Instances.ProjectionHierarchy.parity_cubes_differ
#print axioms Integration.Kernel.Instances.ProjectionHierarchy.cube_does_not_descend_through_pairwise
#print axioms Integration.Kernel.Instances.ProjectionHierarchy.hierarchy_is_strict
#print axioms Integration.Kernel.Instances.ProjectionHierarchy.pairwise_fibre_is_not_a_singleton

/-! ### Integration.Kernel.DeclaredRealised -/

#print axioms Integration.Kernel.DeclaredRealised.authorised_does_not_descend_through_declared
#print axioms Integration.Kernel.DeclaredRealised.acknowledged_does_not_descend_through_authorised
#print axioms Integration.Kernel.DeclaredRealised.realised_does_not_descend_through_acknowledged
#print axioms Integration.Kernel.DeclaredRealised.declared_does_not_descend_through_realised
#print axioms Integration.Kernel.DeclaredRealised.no_link_of_the_chain_is_automatic
#print axioms Integration.Kernel.DeclaredRealised.episode_is_the_join
#print axioms Integration.Kernel.DeclaredRealised.Receipt.determines_realised
#print axioms Integration.Kernel.DeclaredRealised.acknowledgement_alone_is_not_a_receipt
#print axioms Integration.Kernel.DeclaredRealised.receipt_exists_iff
#print axioms Integration.Kernel.DeclaredRealised.success_is_not_a_function_of_the_world
#print axioms Integration.Kernel.DeclaredRealised.success_does_not_descend_through_episode
#print axioms Integration.Kernel.DeclaredRealised.success_descends_through_pair

/-! ### Integration.Kernel.AppendOnlyHistory -/

#print axioms Integration.Kernel.AppendOnlyHistory.extends_refl
#print axioms Integration.Kernel.AppendOnlyHistory.extends_trans
#print axioms Integration.Kernel.AppendOnlyHistory.extends_antisymm
#print axioms Integration.Kernel.AppendOnlyHistory.append_extends
#print axioms Integration.Kernel.AppendOnlyHistory.extends_nil
#print axioms Integration.Kernel.AppendOnlyHistory.earlier_entries_unchanged
#print axioms Integration.Kernel.AppendOnlyHistory.correction_does_not_erase
#print axioms Integration.Kernel.AppendOnlyHistory.append_length
#print axioms Integration.Kernel.AppendOnlyHistory.rewriting_is_not_an_extension
#print axioms Integration.Kernel.AppendOnlyHistory.replay_nil
#print axioms Integration.Kernel.AppendOnlyHistory.replay_cons
#print axioms Integration.Kernel.AppendOnlyHistory.replay_append_list
#print axioms Integration.Kernel.AppendOnlyHistory.replay_append
#print axioms Integration.Kernel.AppendOnlyHistory.state_does_not_determine_history
#print axioms Integration.Kernel.AppendOnlyHistory.state_descends_through_history
#print axioms Integration.Kernel.AppendOnlyHistory.history_strictly_refines_state

/-! ### Integration.Kernel.BraidedTrace -/

#print axioms Integration.Kernel.BraidedTrace.pools_agree
#print axioms Integration.Kernel.BraidedTrace.authorities_differ
#print axioms Integration.Kernel.BraidedTrace.pool_does_not_determine_authority
#print axioms Integration.Kernel.BraidedTrace.pool_descends_through_braid
#print axioms Integration.Kernel.BraidedTrace.braid_strictly_refines_pool
#print axioms Integration.Kernel.BraidedTrace.every_pair_admits_a_trivial_crossing
#print axioms Integration.Kernel.BraidedTrace.lawful_crossing_preserves_invariant
#print axioms Integration.Kernel.BraidedTrace.no_lawful_crossing_of_different_invariant
#print axioms Integration.Kernel.BraidedTrace.lawful_crossing_does_not_merge_authority

/-! ### Integration.Kernel.LineageEdge -/

#print axioms Integration.Kernel.LineageEdge.generative_iff
#print axioms Integration.Kernel.LineageEdge.amplification_is_not_generative
#print axioms Integration.Kernel.LineageEdge.funding_is_not_generative
#print axioms Integration.Kernel.LineageEdge.reporting_is_not_generative
#print axioms Integration.Kernel.LineageEdge.roots_constant_along_amplification
#print axioms Integration.Kernel.LineageEdge.amplified_copies_are_not_independent_replication
#print axioms Integration.Kernel.LineageEdge.star_roots_eq_generative_roots
#print axioms Integration.Kernel.LineageEdge.star_kinds_differ
#print axioms Integration.Kernel.LineageEdge.edge_kind_does_not_descend_through_roots
#print axioms Integration.Kernel.LineageEdge.star_all_amplified
#print axioms Integration.Kernel.LineageEdge.downstream_count_is_not_source_count

/-! ### Integration.Kernel.PromotionTransport -/

#print axioms Integration.Kernel.PromotionTransport.holds_of_corresponds_and_sound
#print axioms Integration.Kernel.PromotionTransport.artifact_does_not_give_correspondence
#print axioms Integration.Kernel.PromotionTransport.correspondence_does_not_give_transport_soundness
#print axioms Integration.Kernel.PromotionTransport.holds_does_not_give_inhabitance
#print axioms Integration.Kernel.PromotionTransport.first_three_do_not_close_the_fourth
#print axioms Integration.Kernel.PromotionTransport.receipt_yields_term
#print axioms Integration.Kernel.PromotionTransport.receipt_needs_all_four
#print axioms Integration.Kernel.PromotionTransport.receipt_exists_of_inhabitant

/-! ### Integration.Kernel.Welds.RuntimeBraidedProvenance -/

#print axioms Integration.Kernel.Welds.RuntimeBraidedProvenance.laneEvents_idem
#print axioms Integration.Kernel.Welds.RuntimeBraidedProvenance.laneRoots_extract
#print axioms Integration.Kernel.Welds.RuntimeBraidedProvenance.mem_laneEvents_iff
#print axioms Integration.Kernel.Welds.RuntimeBraidedProvenance.payload_pooling_does_not_determine_lane
#print axioms Integration.Kernel.Welds.RuntimeBraidedProvenance.payload_pooling_does_not_determine_authority
#print axioms Integration.Kernel.Welds.RuntimeBraidedProvenance.no_lawful_crossing_of_disjoint_lanes
#print axioms Integration.Kernel.Welds.RuntimeBraidedProvenance.lanes_are_independent
#print axioms Integration.Kernel.Welds.RuntimeBraidedProvenance.pooling_destroys_independence
#print axioms Integration.Kernel.Welds.RuntimeBraidedProvenance.flat_event_count_is_not_root_count

/-! ### Integration.Kernel.Welds.AmplifiedObservationCount -/

#print axioms Integration.Kernel.Welds.AmplifiedObservationCount.amplified_from_rootNode
#print axioms Integration.Kernel.Welds.AmplifiedObservationCount.amplified_from_root
#print axioms Integration.Kernel.Welds.AmplifiedObservationCount.twenty_observations_are_three_sources
#print axioms Integration.Kernel.Welds.AmplifiedObservationCount.same_class_are_not_independent
#print axioms Integration.Kernel.Welds.AmplifiedObservationCount.different_class_are_independent
#print axioms Integration.Kernel.Welds.AmplifiedObservationCount.far_apart_but_dependent
#print axioms Integration.Kernel.Welds.AmplifiedObservationCount.count_is_not_support

/-! ### Integration.Kernel.Welds.RemedyRuntimeFeedback -/

#print axioms Integration.Kernel.Welds.RemedyRuntimeFeedback.consumers_disagree_on_one_episode
#print axioms Integration.Kernel.Welds.RemedyRuntimeFeedback.verdict_does_not_descend_through_episode
#print axioms Integration.Kernel.Welds.RemedyRuntimeFeedback.verdict_descends_through_pair
#print axioms Integration.Kernel.Welds.RemedyRuntimeFeedback.only_failing_consumer_reopens
#print axioms Integration.Kernel.Welds.RemedyRuntimeFeedback.reopens_of_failing_edge
#print axioms Integration.Kernel.Welds.RemedyRuntimeFeedback.full_success_reopens_nothing
#print axioms Integration.Kernel.Welds.RemedyRuntimeFeedback.runtime_success_does_not_close_the_remedy
#print axioms Integration.Kernel.Welds.RemedyRuntimeFeedback.remedy_receipt_closes

/-! ### Integration.Kernel.Welds.SituatedMediationCarriers -/

#print axioms Integration.Kernel.Welds.SituatedMediationCarriers.Mediates.effect_does_not_descend_through_global
#print axioms Integration.Kernel.Welds.SituatedMediationCarriers.Mediates.effect_descends_through_pair
#print axioms Integration.Kernel.Welds.SituatedMediationCarriers.process_effect_does_not_descend_through_recipe
#print axioms Integration.Kernel.Welds.SituatedMediationCarriers.rule_effect_does_not_descend_through_rule
#print axioms Integration.Kernel.Welds.SituatedMediationCarriers.process_separates_three
#print axioms Integration.Kernel.Welds.SituatedMediationCarriers.carriers_are_not_relabellings

/-! ### Integration.Kernel.Welds.ResidualSalienceScheduler -/

#print axioms Integration.Kernel.Welds.ResidualSalienceScheduler.separates_iff_splitCount_pos
#print axioms Integration.Kernel.Welds.ResidualSalienceScheduler.constant_reading_no_progress
#print axioms Integration.Kernel.Welds.ResidualSalienceScheduler.separating_strictly_narrows
#print axioms Integration.Kernel.Welds.ResidualSalienceScheduler.salience_does_not_descend_through_magnitude_and_cost
#print axioms Integration.Kernel.Welds.ResidualSalienceScheduler.salience_is_live_set_relative
#print axioms Integration.Kernel.Welds.ResidualSalienceScheduler.salience_descends_through_pair
#print axioms Integration.Kernel.Welds.ResidualSalienceScheduler.salience_scheduler_beats_magnitude_scheduler

/-! ### Integration.Kernel.Welds.DeliberativeMoves -/

#print axioms Integration.Kernel.Welds.DeliberativeMoves.search_injective
#print axioms Integration.Kernel.Welds.DeliberativeMoves.strategyE_extends_strategy
#print axioms Integration.Kernel.Welds.DeliberativeMoves.strategyE_never_deliberates
#print axioms Integration.Kernel.Welds.DeliberativeMoves.search_refines
#print axioms Integration.Kernel.Welds.DeliberativeMoves.ask_refines
#print axioms Integration.Kernel.Welds.DeliberativeMoves.listen_refines
#print axioms Integration.Kernel.Welds.DeliberativeMoves.reformulate_preserves_fibre
#print axioms Integration.Kernel.Welds.DeliberativeMoves.listening_can_do_what_no_probe_can
#print axioms Integration.Kernel.Welds.DeliberativeMoves.reformulation_can_close_without_narrowing
#print axioms Integration.Kernel.Welds.DeliberativeMoves.the_four_moves_are_not_interchangeable

/-! ### Integration.Kernel.Welds.CommutingProvenanceSquare -/

#print axioms Integration.Kernel.Welds.CommutingProvenanceSquare.projection_iterate
#print axioms Integration.Kernel.Welds.CommutingProvenanceSquare.projection_transports_along_pipeline
#print axioms Integration.Kernel.Welds.CommutingProvenanceSquare.agreement_now_is_not_a_projection
#print axioms Integration.Kernel.Welds.CommutingProvenanceSquare.whole_trajectory_agreement_is_not_a_projection
#print axioms Integration.Kernel.Welds.CommutingProvenanceSquare.no_coarse_step_commutes
#print axioms Integration.Kernel.Welds.CommutingProvenanceSquare.ProjectionClaim.transports
#print axioms Integration.Kernel.Welds.CommutingProvenanceSquare.compatibility_does_not_promote

/-! ### Integration.Kernel.Bridges.QuorumThreshold -/

#print axioms Integration.Kernel.Bridges.QuorumThreshold.switched_monotone
#print axioms Integration.Kernel.Bridges.QuorumThreshold.one_member_flips_the_collective_state
#print axioms Integration.Kernel.Bridges.QuorumThreshold.collective_state_is_not_an_individual_property
#print axioms Integration.Kernel.Bridges.QuorumThreshold.quorum_by_count_is_not_quorum_by_independent_roots
#print axioms Integration.Kernel.Bridges.QuorumThreshold.members_are_not_independent

/-! ### Integration.Kernel.Bridges.InformationLossLocus -/

#print axioms Integration.Kernel.Bridges.InformationLossLocus.collapse_persists
#print axioms Integration.Kernel.Bridges.InformationLossLocus.firstLoss_spec
#print axioms Integration.Kernel.Bridges.InformationLossLocus.pair01_lost_at_one
#print axioms Integration.Kernel.Bridges.InformationLossLocus.pair23_lost_at_two
#print axioms Integration.Kernel.Bridges.InformationLossLocus.locus_is_pair_relative
#print axioms Integration.Kernel.Bridges.InformationLossLocus.pair01_stays_lost

/-! ### Integration.Kernel.Bridges.CorroborationPhase -/

#print axioms Integration.Kernel.Bridges.CorroborationPhase.more_reports_less_support
#print axioms Integration.Kernel.Bridges.CorroborationPhase.support_does_not_descend_through_count
#print axioms Integration.Kernel.Bridges.CorroborationPhase.inPhase_net_eq_count
#print axioms Integration.Kernel.Bridges.CorroborationPhase.coherent_pair_beats_incoherent_quartet

/-! ### Integration.Kernel.Welds.LaneProjectionSquare -/

#print axioms Integration.Kernel.Welds.LaneProjectionSquare.laneRoots_append
#print axioms Integration.Kernel.Welds.LaneProjectionSquare.lane_extraction_is_a_projection
#print axioms Integration.Kernel.Welds.LaneProjectionSquare.lane_roots_transport
#print axioms Integration.Kernel.Welds.LaneProjectionSquare.flat_log_is_not_a_projection_of_the_lane_state

/-! ### Integration.Kernel.Welds.SalienceOverLineage -/

#print axioms Integration.Kernel.Welds.SalienceOverLineage.indexParity_splits_observations
#print axioms Integration.Kernel.Welds.SalienceOverLineage.classReading_splits_observations
#print axioms Integration.Kernel.Welds.SalienceOverLineage.classReading_splits_roots
#print axioms Integration.Kernel.Welds.SalienceOverLineage.hypothesis_separation_does_not_imply_root_separation
#print axioms Integration.Kernel.Welds.SalienceOverLineage.root_separating_reading_also_separates_hypotheses
#print axioms Integration.Kernel.Welds.SalienceOverLineage.salience_ordering_disagrees
#print axioms Integration.Kernel.Welds.SalienceOverLineage.separated_but_dependent
