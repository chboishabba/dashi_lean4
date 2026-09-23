/-
# Axiom audit for the BIDI development

Every theorem of the BIDI chain is printed here with its axiom dependencies.
The only axioms that may appear are Lean's standard three (`propext`,
`Classical.choice`, `Quot.sound`).  No postulate, no `sorry`, no receipt and no
promotion flag occurs anywhere in this development.
-/
import RequestProject.YangMills.BIDI.EndToEndWitness
import RequestProject.YangMills.BIDI.PolymerShellBridge
import RequestProject.YangMills.BIDI.BoundedSpectrumBridge

namespace RequestProject.YangMills.BIDI.Audit

open RequestProject.YangMills.BIDI

-- §3, §9: CMP116 localization
#print axioms abs_sum_le_of_termwise_le
#print axioms abs_double_sum_le_of_termwise
#print axioms abs_double_sum_le_of_norm_termwise

-- §4, §7: the noncommutative telescope and the marked product
#print axioms norm_prod_before_le
#print axioms norm_prod_before_sub_prod_after_le
#print axioms teleBound_eq_sum
#print axioms teleBound_marked
#print axioms marked_product_bound
#print axioms fourStage_bound_of_marked_outer
#print axioms fourStage_bound_of_marked_log
#print axioms fourStage_bound_of_marked_transport
#print axioms fourStage_bound_of_marked_path

-- §6: the CMP99 marked stage
#print axioms second_resolvent_identity
#print axioms norm_resolvent_defect_le
#print axioms valid_ofResolventDefect
#print axioms valid_marked_of_le

-- §10: Cauchy extraction
#print axioms norm_mixed_deriv_le
#print axioms norm_mixed_deriv_le_cauchyConst
#print axioms norm_polarized_mixed_le

-- §2, §11, §13: source calculus and order closures
#print axioms covFinite_eq_mixedLogDeriv
#print axioms exp_decay_transfer
#print axioms norm_le_of_tendsto

-- §14: clustering to the gap
#print axioms measure_Ioo_eq_zero_of_laplace_decay
#print axioms energy_ge_of_gap_support
#print axioms energy_ge_of_laplace_decay
#print axioms hasVacuumFormGap_of_clustering

-- the assembled chain
#print axioms shell_sup_bound_of_localization
#print axioms mixedLog_bound_of_source_data
#print axioms polarized_bound_of_source_data
#print axioms covariance_bound_finite
#print axioms covariance_bound_continuum
#print axioms continuum_clustering_of_source_data
#print axioms mass_gap_of_clustering
#print axioms resolvent_solvable_below_gap
#print axioms no_eigenvalue_below_gap

-- backward bridges to the existing material
#print axioms far_shell_energy_tsum_le
#print axioms cauchy_shell_estimate_of_polymer
#print axioms continuum_formGap_of_cutoff_clustering
#print axioms continuum_no_spectrum_below_gap_of_clustering
#print axioms continuum_resolvent_bound_of_clustering
#print axioms hasFormGap_of_clustering_bounded
#print axioms spectrum_restrict_subset_halfPlane_of_clustering
#print axioms notMem_spectrum_of_clustering
#print axioms spectrum_inter_Ioo_eq_empty_of_clustering

-- end to end, and non-vacuity
#print axioms source_covariance_bound_of_polymer
#print axioms bidi_end_to_end
#print axioms mixedLogDeriv_bilinear
#print axioms clusteringWitness_formGap
#print axioms end_to_end_nonvacuous

end RequestProject.YangMills.BIDI.Audit
