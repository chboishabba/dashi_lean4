import Integration.Variation.Pairing
import Integration.Variation.CutoffLimit
import Integration.Variation.CommonLanguage
import Integration.Variation.SourceCoordinate
import Integration.Variation.MetricDensity
import Integration.Variation.SymmetricFibre
import Integration.Variation.Weld
import Integration.Variation.SymmetricField
import Integration.Variation.InverseMetric
import Integration.Variation.SectorFilter
import Integration.Variation.ThirdOrder
import Integration.Variation.SourceCoordinateBanach
import Integration.Variation.DenseFibre
import Integration.Reconciliation.Stage7Boundary
import Integration.Reconciliation.QFTGRBoundary
import Integration.Reconciliation.ContinuumProducerBoundary

/-!
# Axiom audit — the QFT/GR common-variation tranche

Every result of `Integration.Variation.*` is listed here; the build log must
show only `propext`, `Classical.choice` and `Quot.sound` for each of them.
Anything else — in particular a `sorryAx` — is a failure of the audit.
-/

-- Lane 1: the stress pairing and separation.
#print axioms Integration.Variation.Pairing.pair_add_right
#print axioms Integration.Variation.Pairing.pair_smul_right
#print axioms Integration.Variation.Pairing.pair_sum
#print axioms Integration.Variation.Pairing.eq_of_pair_eq_on_spanning
#print axioms Integration.Variation.Pairing.eq_of_pair_eq_on_top
#print axioms Integration.Variation.Pairing.pair_tsum
#print axioms Integration.Variation.Pairing.eq_of_pair_eq_on_dense
#print axioms Integration.Variation.Pairing.eq_of_pair_eq_on_dense_submodule
#print axioms Integration.Variation.Pairing.separates_iff_dense
#print axioms Integration.Variation.Pairing.exists_ne_agreeing_of_ne_top
#print axioms Integration.Variation.Pairing.separates_iff_eq_top
#print axioms Integration.Variation.Pairing.plane_pairing_does_not_separate

-- Lane 2: finite cutoff to continuum, and sector aggregation.
#print axioms Integration.Variation.CutoffLimit.scalar_limit_interchange
#print axioms Integration.Variation.CutoffLimit.exists_unique_continuum_stress
#print axioms Integration.Variation.CutoffLimit.continuum_stress_of_cutoff_family
#print axioms Integration.Variation.CutoffLimit.exists_unique_continuum_functional
#print axioms Integration.Variation.CutoffLimit.sector_aggregate_variation
#print axioms Integration.Variation.CutoffLimit.sector_aggregate_variation_tsum
#print axioms Integration.Variation.CutoffLimit.sector_aggregation_commutes_with_cutoff_limit
#print axioms Integration.Variation.CutoffLimit.pairing_convergence_is_not_tensor_convergence
#print axioms Integration.Variation.CutoffLimit.l2_pairing_convergence_is_not_tensor_convergence
#print axioms Integration.Variation.CutoffLimit.divergent_cutoff_family_has_no_continuum_pairing
#print axioms Integration.Variation.CutoffLimit.one_sector_is_not_the_total

-- Lane 3: one common metric-variation language.
#print axioms Integration.Variation.CommonLanguage.CommonVariation.pairings_agree
#print axioms Integration.Variation.CommonLanguage.stress_weld_of_common_carrier
#print axioms Integration.Variation.CommonLanguage.stress_weld_of_dense_carrier
#print axioms Integration.Variation.CommonLanguage.stress_weld
#print axioms Integration.Variation.CommonLanguage.tensor_unique_of_spanning
#print axioms Integration.Variation.CommonLanguage.mismatched_carrier_maps_do_not_weld
#print axioms Integration.Variation.CommonLanguage.non_spanning_fibre_does_not_weld
#print axioms Integration.Variation.CommonLanguage.separate_actions_do_not_weld

-- Lane 4: source-coordinate discipline.
#print axioms Integration.Variation.SourceCoordinate.second_deriv_comp
#print axioms Integration.Variation.SourceCoordinate.second_deriv_comp_affine
#print axioms Integration.Variation.SourceCoordinate.naive_hessian_identification_fails
#print axioms Integration.Variation.SourceCoordinate.affine_iff_no_correction_at

-- The assembled cutset.
#print axioms Integration.Variation.Weld.qftgr_stress_weld_of_cutset
#print axioms Integration.Variation.Weld.common_variation_has_one_stress
#print axioms Integration.Variation.SourceCoordinate.second_fderiv_comp
#print axioms Integration.Variation.SourceCoordinate.second_fderiv_comp_of_const_fderiv
#print axioms Integration.Variation.SourceCoordinate.correction_is_detected_by_a_linear_energy

-- Lane 5: the metric-density first variation.
#print axioms Integration.Variation.MetricDensity.hasDerivAt_det_one_add_smul
#print axioms Integration.Variation.MetricDensity.hasDerivAt_det_add_smul
#print axioms Integration.Variation.MetricDensity.hasDerivAt_sqrt_neg_det
#print axioms Integration.Variation.MetricDensity.density_variation_is_a_trace_pairing
#print axioms Integration.Variation.MetricDensity.density_variation_is_linear
#print axioms Integration.Variation.MetricDensity.density_variation_does_not_determine_the_perturbation

-- Lane 6: the symmetric perturbation fibre.
#print axioms Integration.Variation.SymmetricFibre.trace_mul_single
#print axioms Integration.Variation.SymmetricFibre.isSymm_singlePair
#print axioms Integration.Variation.SymmetricFibre.eq_of_trace_eq_on_symmetric
#print axioms Integration.Variation.SymmetricFibre.symmetric_perturbations_do_not_separate_general_tensors
#print axioms Integration.Variation.SymmetricFibre.symmetry_of_the_stress_is_load_bearing

-- Lane 8: the symmetric perturbation field fibre.
#print axioms Integration.Variation.SymmetricField.fieldPair_add_right
#print axioms Integration.Variation.SymmetricField.fieldPair_add_left
#print axioms Integration.Variation.SymmetricField.fieldPair_smul_right
#print axioms Integration.Variation.SymmetricField.isSymmField_localise
#print axioms Integration.Variation.SymmetricField.fieldPair_localise
#print axioms Integration.Variation.SymmetricField.eq_of_localised_pairing_on_symmetric
#print axioms Integration.Variation.SymmetricField.eq_of_fieldPair_eq_on_symmetric
#print axioms Integration.Variation.SymmetricField.vanishing_density_hides_a_point
#print axioms Integration.Variation.SymmetricField.symmetric_field_perturbations_do_not_separate_general_fields
#print axioms Integration.Variation.SymmetricField.field_weld_hypotheses_are_load_bearing

-- Lane 9: the inverse-metric variation.
#print axioms Integration.Variation.InverseMetric.hasDerivAt_inv_add_smul
#print axioms Integration.Variation.InverseMetric.inverse_variation_is_a_trace_pairing
#print axioms Integration.Variation.InverseMetric.isSymm_inverse_variation
#print axioms Integration.Variation.InverseMetric.inverse_variation_determines_the_perturbation
#print axioms Integration.Variation.InverseMetric.inverse_variation_is_injective
#print axioms Integration.Variation.InverseMetric.hasDerivAt_sqrt_neg_det_smul_inv

-- Lane 10: sector aggregation beyond summability.
#print axioms Integration.Variation.SectorFilter.hasSum_pair
#print axioms Integration.Variation.SectorFilter.tendsto_pair_of_tendsto_sum
#print axioms Integration.Variation.SectorFilter.exhaustion_total_unique
#print axioms Integration.Variation.SectorFilter.summable_of_smul_const
#print axioms Integration.Variation.SectorFilter.sum_range_condFamily
#print axioms Integration.Variation.SectorFilter.not_summable_condFamily
#print axioms Integration.Variation.SectorFilter.conditionally_convergent_sector_family
#print axioms Integration.Variation.SectorFilter.exhaustion_total_is_not_the_unconditional_total

-- Lane 11: the third-order source-coordinate law.
#print axioms Integration.Variation.ThirdOrder.third_deriv_comp
#print axioms Integration.Variation.ThirdOrder.third_deriv_comp_affine
#print axioms Integration.Variation.ThirdOrder.third_order_correction_is_load_bearing

-- The source-coordinate law in a normed space.
#print axioms Integration.Variation.SourceCoordinateBanach.second_deriv_comp_curve
#print axioms Integration.Variation.SourceCoordinateBanach.second_deriv_comp_affine_curve
#print axioms Integration.Variation.SourceCoordinateBanach.third_deriv_comp_curve
#print axioms Integration.Variation.SourceCoordinateBanach.third_deriv_comp_curve_symm
#print axioms Integration.Variation.SourceCoordinateBanach.second_fderiv_apply_real
#print axioms Integration.Variation.SourceCoordinateBanach.banach_third_term_is_load_bearing

-- A proper, dense, separating admitted fibre.
#print axioms Integration.Variation.DenseFibre.span_basis_dense
#print axioms Integration.Variation.DenseFibre.span_basis_ne_top
#print axioms Integration.Variation.DenseFibre.basis_span_separates
#print axioms Integration.Variation.DenseFibre.proper_dense_admitted_fibre_exists

-- Stage-7 reconciliation: the robustness frontier as propositions.
#print axioms Integration.Reconciliation.Stage7Boundary.boundary_claims_are_false
#print axioms Integration.Reconciliation.Stage7Boundary.every_obligation_has_generic_content
#print axioms Integration.Reconciliation.Stage7Boundary.boundary_and_obligations_are_different_registers

-- QFT/GR reconciliation: the two Agda boundary ledgers as propositions.
#print axioms Integration.Reconciliation.QFTGRBoundary.natValued_hasDerivAt_eq_zero
#print axioms Integration.Reconciliation.QFTGRBoundary.phaseLift_not_injective
#print axioms Integration.Reconciliation.QFTGRBoundary.pinned_false_entries_are_refuted
#print axioms Integration.Reconciliation.QFTGRBoundary.pinned_true_entries_have_generic_content
#print axioms Integration.Reconciliation.QFTGRBoundary.qftgr_boundary_ledger_has_theorem_content

-- Continuum-producer reconciliation: endpoint sector variation and aggregation.
#print axioms Integration.Reconciliation.ContinuumProducerBoundary.endpoint_aggregation_suffices
#print axioms Integration.Reconciliation.ContinuumProducerBoundary.endpoint_aggregation_suffices_tsum
#print axioms Integration.Reconciliation.ContinuumProducerBoundary.ledger_false_entry_is_refuted
#print axioms Integration.Reconciliation.ContinuumProducerBoundary.producer_ledger_has_theorem_content
