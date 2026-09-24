import Synthesis.EndToEnd

/-!
# Axiom audit

Building this module prints the axiom dependencies of the spine's headline
results.  Every one of them uses only the standard Lean/Mathlib axioms
(`propext`, `Classical.choice`, `Quot.sound`); none uses `sorry`, a project
axiom, or `Lean.ofReduceBool` (i.e. no `native_decide` anywhere in the spine).
-/

#print axioms Synthesis.EndToEnd.crossDomainSpine
#print axioms Synthesis.EndToEnd.spine_end_to_end
#print axioms Synthesis.EndToEnd.fabricTone_act_iterate
#print axioms Synthesis.ToneCore.halfTone_fibre_card
#print axioms Synthesis.DialecticTone.no_equivariant_fourfold_tone
#print axioms Synthesis.DialecticTone.residual_routes_diverge
#print axioms Synthesis.DialecticTone.equivariant_sixfold_tone_iff
#print axioms Synthesis.DialecticTone.card_equivariant_sixfold_tones
#print axioms Synthesis.RelationSeam.factors_through_iff
#print axioms Synthesis.RelationSeam.bucket_not_factor_through_root
#print axioms Synthesis.RelationSeam.promotion_not_determined_by_bucket
#print axioms Synthesis.RelationSeam.seam_nonempty
#print axioms Synthesis.RelationSeam.stageTone_seam_minimal
#print axioms Synthesis.RelationSeam.stage6Tone_seam_empty
#print axioms Synthesis.Hyperfabric.card_collapse_fibre
#print axioms Synthesis.MonsterFibre.dSSP_eq_zero_iff
#print axioms Synthesis.MonsterFibre.projectSSP_contractive
#print axioms Synthesis.MonsterFibre.isometric_reindex_eq_refl
#print axioms Synthesis.Hyperfabric.no_nontrivial_geometric_base_action
#print axioms Synthesis.WalkGeometry.walk_distance_complement
#print axioms Synthesis.MoonshineBase.maskProduct_trivector
#print axioms Synthesis.MoonshineBase.maskProduct_dvd_iff
#print axioms Synthesis.WalkArithmetic.step_arith_dSSP_empty_le
#print axioms Synthesis.Hyperfabric.fabricAct_next6
#print axioms Synthesis.Hyperfabric.support_not_hom
#print axioms Synthesis.CodecBridge.fabricOrbits_value
#print axioms Synthesis.CodecBridge.card_fabric_eq_pow
#print axioms Synthesis.Vec15Fibre.sig15Equiv_scan
#print axioms Synthesis.StatisticsFibre.rank15_eq_card
#print axioms Synthesis.StatisticsFibre.selectMask15_dSSP_empty_mono
#print axioms Synthesis.Vec15Fibre.vec15Equiv_sum
#print axioms Synthesis.InferenceFibre.countNonZero15_eq_card
#print axioms Synthesis.InferenceFibre.countNonZero15_add_rank15_zero
#print axioms Synthesis.InferenceFibre.baselineDecision_failToReject_iff
#print axioms Synthesis.InferenceFibre.pairDecision_failToReject_iff
#print axioms Synthesis.InferenceFibre.supportMask_dvd
#print axioms Synthesis.InferenceFibre.winsorize15_eq_off_outlierMask
#print axioms Synthesis.PhysicsInterfaces.gauge_contract_permits_non_SM
#print axioms Synthesis.PhysicsInterfaces.spin_interface_no_double_cover
#print axioms Synthesis.PhysicsInterfaces.conformsOn_scan_iff_dSSP_zero
#print axioms Synthesis.SpinCoverBridge.card_spin_eq_two_mul_card_base
#print axioms Synthesis.SpinCoverBridge.card_rho_fiber
#print axioms Synthesis.SpinCoverBridge.spin_interface_satisfiable_with_genuine_cover
#print axioms Synthesis.SpinCoverBridge.continuous_cover_interface_vacuous
#print axioms Synthesis.CircleCover.sq_fiber_exact
#print axioms Synthesis.CircleCover.spin_interface_satisfiable_with_continuous_cover
#print axioms Synthesis.ExponentFibre.maskProduct_succ_mod
#print axioms Synthesis.ExponentFibre.jCoefficient_mod_trivector
#print axioms Synthesis.MonsterOrder.monsterOrderNumeral_primeFactors
#print axioms Synthesis.MonsterOrder.radical_monsterOrderNumeral
