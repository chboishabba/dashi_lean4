# Declaration Landscape

This is a name-only map of the current Lean repo and the two local bundle
manifests. It is meant to orient workers before porting or review work; it is
not a claim that bundled declarations have been materialized into this repo.

Regenerate/check the checked-in section with:

```bash
rg -n "^(def|theorem|lemma|structure|inductive|class|abbrev|instance)\s+" -g '*.lean'
```

## Current Lean Repo

### `Main.lean`

- `moonshine`
- `moonshine_eq`
- `phase_transition`
- `main`

### `MoonshineEarn.lean`

- `fstep`
- `perf_product`
- `moonshine_product`
- `step1_fires`
- `step1_result`
- `step1_factors`
- `step2_fires`
- `step2_result`
- `step2_factors`
- `step3_fires`
- `step3_result`
- `step3_factors`
- `earning_chain`
- `moonshine_observed`
- `residue_7`
- `residue_11`
- `residue_23`
- `residue_47`
- `residue_59`
- `residue_71`
- `ratio_not_integer`
- `each_fires_once`
- `f1_inert`
- `f2_inert`
- `f3_inert`
- `full_perf_earn`
- `observer_preserved`
- `taxi_is_1729`
- `taxi_step1`
- `taxi_step2`
- `taxi_step3`
- `taxi_div7`
- `taxi_div13`
- `taxi_div19`
- `taxi_earns_moonshine`
- `earning_quotient`
- `earning_remainder`
- `earning_decomp`
- `taxicab_sum1`
- `taxicab_sum2`

### `MoonshineFractran.lean`

- `SSP`
- `moonshine_kernel`
- `moonshine_observer`
- `moonshine_factored`
- `ssp_len`
- `FractranState`
- `perfState4`
- `moonshinePure`
- `moonshine_mass`
- `observer_residue`
- `phase_invariant`

### `DashiPerf.lean`

No declarations; import hub only.

### `DashiPerf/Basic.lean`

- `hello`

### `DashiPerf/Schema.lean`

- `CborVal`
- `da51Tag`
- `shard_0`
- `shard_0_is_da51`
- `allShards`

### `DashiPerf/Audit.lean`

- `CborVal`
- `da51Tag`
- `shard_0`
- `shard_0_is_da51`
- `allShards`

### `DashiPerf/Sample100.lean`

- `CborVal`
- `da51Tag`
- `shard_0`
- `shard_0_is_da51`
- `allShards`

### `DashiPerf/Sample101.lean`

- `CborVal`
- `da51Tag`
- `shard_0`
- `shard_0_is_da51`
- `allShards`

### `DashiPerf/Sample102.lean`

- `CborVal`
- `da51Tag`
- `shard_0`
- `shard_0_is_da51`
- `allShards`

## DASHI Bundle Candidates

Source: `20260604_070337_allm_20260604_070337.txt`.

These names are embedded in the local bundle text but are not currently
checked-in Lean modules.

### `UltrametricSpace.lean`

- `DiscreteUltrametric`
- `triangle`
- `StrictContractive`
- `IsFixedPt`
- `fixed_unique`
- `ActionMonotone`
- `Counterexample`

### `FascisticSystem.lean`

- `Projection`
- `FascisticSys`
- `FascisticSys.Attractor`
- `FascisticSys.iter`
- `FascisticSys.iter_monotone`
- `InvertibleOp`
- `AntiFascisticSys`
- `projection_vs_unitary`

### `MonsterMask.lean`

- `FactorCount`
- `Mask`
- `fullMask`
- `emptyMask`
- `maskAnd`
- `flipMask`
- `flipMask_involutive`
- `maskAnd_fullMask`
- `maskAnd_emptyMask`
- `maskAnd_comm`
- `maskAnd_idem`
- `maskHammingDist`
- `maskHammingDist_self`
- `maskHammingDist_comm`
- `projectTo`
- `projectTo_idem`
- `projectTo_fixed_unique`
- `WalkState`
- `WalkLens`
- `walkChoose`
- `walkStep`

### `LogicTlurey.lean`

- `Stage`
- `next`
- `stageTrace`
- `stageTrace_length`
- `next_period_4`
- `spin4_next`
- `stageTone`
- `combineStage`
- `stageTone_next_seed`
- `stageTone_next_counter`
- `stageTone_next_resonance`
- `stageTone_next_overflow`
- `resonance_combine`

### `SupersingularPrimes.lean`

- `supersingularPrimes`
- `supersingularPrimes_length`
- `supersingularPrimes_all_prime`
- `supersingularPrimes_sorted`
- `supersingularPrimes_nodup`
- `triangle_196883`
- `prime_47`
- `prime_59`
- `prime_71`
- `coprime_47_59`
- `coprime_47_71`
- `coprime_59_71`
- `mckay_observation`
- `mckay_decomposition`
- `monsterOrder`
- `monsterOrder_positive`
- `bottClassFn`
- `bott_period_8`
- `cl15_bott_class`
- `cl15_dim`
- `coprime_clifford_monster`
- `harmonic_gcd`
- `harmonic_lcm`
- `eigenspace_decomposition`

### `KernelAlgebra.lean`

- `Trit`
- `Trit.inv`
- `Trit.inv_inv`
- `TritState`
- `tritInvol`
- `tritInvol_invol`
- `KernelOp`
- `KernelOp.idK`
- `KernelOp.negK`
- `KernelOp.neg_twice`
- `No2Cycle`

### `TenfoldBridges.lean`

- `topoClass`
- `Bridge`
- `Bridge.sym`
- `bridge_232_323`
- `bridge_sym_nodeA`
- `bridge_sym_nodeB`
- `bridge_sym_sym_nodeA`
- `BottType`
- `bottClock`
- `AZClass`
- `az_classes_count`
- `bott_classes_count`
- `harmonic_gcd_8_10`
- `harmonic_lcm_8_10`
- `cliffordDim`
- `gradeDim`
- `grade_sum`
- `so15_rotation_planes`
- `rotation_105_factored`

### `Overflow.lean`

- `Voxel`
- `VoxelGuard`
- `toVoxel`
- `enforce`
- `only_if`

### `MoonshineEarn.lean`

- `fstep`
- `perf_product`
- `moonshine_product`
- `step1_fires`
- `step1_result`
- `step1_factors`
- `step2_fires`
- `step2_result`
- `step2_factors`
- `step3_fires`
- `step3_result`
- `step3_factors`
- `earning_chain`
- `moonshine_observed`
- `residue_47`
- `residue_59`
- `residue_71`
- `residue_7`
- `residue_11`
- `residue_23`
- `each_fires_once`
- `f1_inert`
- `f2_inert`
- `f3_inert`
- `full_perf_earn`
- `observer_preserved`
- `phase_invariant`
- `taxi_is_1729`
- `taxi_earns_moonshine`
- `taxicab_sum1`
- `taxicab_sum2`
- `SSP`
- `ssp_len`
- `moonshine_kernel`
- `moonshine_factored`

### `CRTPeriod.lean`

- `digitFn`
- `period`
- `period_eq`
- `period_thm`
- `crt_coprime_71_59`
- `crt_coprime_71_47`
- `crt_coprime_59_47`
- `stage1_product`
- `stage2_product`
- `stage3_is_square`
- `digitFn_0`
- `digitFn_1`
- `digitFn_196883`

### `MonsterMoonshine.lean`

- `monsterIrrepDims`
- `monster_trivial_dim`
- `monster_min_nontrivial`
- `jCoefficients`
- `j_constant_term`
- `j_first_coeff`
- `mckay_observation_decomp`
- `j_q2_decomp`
- `genus0Primes`
- `genus0_eq_supersingular`
- `genus0_all_prime`
- `genus0_count`
- `heckeIndexToPrime`
- `hecke_all_prime`
- `monsterValuation`
- `monster_valuation_sum`
- `monster_max_valuation`

### `Base369.lean`

- `spin`
- `TriTruth`
- `index`
- `rotate`
- `xor`
- `rotate_period_3`
- `xor_left_identity`
- `xor_assoc`
- `xor_comm`
- `HexTruth`
- `index`
- `rotate`
- `xor`
- `rotate_period_6`
- `xor_left_identity`
- `NonaryTruth`
- `index`
- `rotate`
- `xor`
- `rotate_period_9`
- `xor_left_identity`

### `DashiCarrier.lean`

- `Ternary`
- `CarrierField`
- `Ternary.support`
- `Sign`
- `Carrier`
- `Ternary.factor`
- `Ternary.reconstruct`
- `Ternary.roundtrip`
- `from_signed`
- `to_signed`
- `carrier_roundtrip`
- `Carrier.valid`
- `from_signed_valid`
- `to_signed_ternary`
- `Ternary.neg'`
- `Ternary.neg'_neg'`
- `Ternary.neg'_support`
- `carrierNeg`
- `carrierNeg_invol`
- `carrierNeg_support`
- `Ternary.toPQ`
- `Ternary.fromPQ`
- `Ternary.pq_roundtrip`
- `Ternary.pq_roundtrip_rev`
- `Ternary.pq_injective`
- `Ternary.pq_bijective`

### `DashiDefect.lean`

- `Kernel.IsContractive`
- `idempotent_is_contractive`
- `Kernel.iterate`
- `Kernel.iterate_zero`
- `Kernel.iterate_succ`
- `Kernel.iterate_fixed`
- `idempotent_one_step`
- `supportCount`
- `supportCount_le_card`

### `DashiHierarchy.lean`

- `MLevel`
- `M3`
- `M6`
- `M9`
- `LiftProject`
- `LiftProject.no_spurious_defect`
- `identityLiftProject`
- `LiftProject.comp`
- `LiftProject.comp_id_left`
- `LiftProject.comp_id_right`
- `ternaryMul`
- `ternaryMul_comm`
- `ternaryMul_zero_left`
- `ternaryMul_zero_right`
- `ternaryMul_pos_left`
- `ternaryMul_pos_right`
- `ternaryMul_assoc`
- `tensorLift`
- `tensorProject`
- `tensorLift_support`
- `backendEquivalent`
- `backendEquivalent_refl`
- `backendEquivalent_symm`
- `backendEquivalent_trans`

### `DashiAnnihilation.lean`

- `NeighborGraph`
- `Ternary.oppositeSigned`
- `Ternary.oppositeSigned_symm`
- `Ternary.oppositeSigned_zero_left`
- `Ternary.oppositeSigned_zero_right`
- `Ternary.oppositeSigned_self`
- `hasOppositeNeighbor`
- `isAnnihilationStable`
- `stable_no_opposites`
- `zero_annihilation_stable`
- `pos_annihilation_stable`
- `neg_annihilation_stable`
- `ternaryToInt`
- `majorityOfList`
- `majorityOfList_nil`
- `majorityOfList_uniform_pos`
- `majorityOfList_uniform_neg`

### `DashiAdmissibility.lean`

- `AdmissibilityTransform`
- `admissible_equiv`
- `admissible_equiv_refl`
- `admissible_equiv_symm`
- `admissible_equiv_trans`
- `admissible_equiv_equivalence`
- `kernelEquivariant`
- `kernelStrictlyEquivariant`
- `strict_implies_equivariant`
- `identityKernel_equivariant`
- `MDLScore`
- `MDLScore.isAdmissibilityInvariant`
- `MDLComparison`
- `mdl_tie_on_equivalent`

### `BottPeriodicity.lean`

- `BottType`
- `bottClock`
- `cl15_bott_type`
- `bott_periodic`
- `cliffordDim`
- `cl15_total_dim`
- `gradeComponentDim`
- `grade_symmetry`
- `grade_sum`
- `AZClass`
- `azLabels`
- `az_count`
- `harmonic_bridge_gcd`
- `harmonic_bridge_lcm`
- `prime_transitions`
- `BMCInvariant`
- `canonicalBMC`
- `bmc_bott`
- `bmc_monster`
- `bmc_clifford`
- `bmc_mckay`
- `bmc_excess`
- `thompson_275`
- `rotationPlanes`
- `so15_rotation_planes`
- `rotation_105_factored`

### `DashiKernel.lean`

- `Kernel`
- `Kernel.IsIdempotent`
- `Kernel.IsFixedPoint`
- `Kernel.idempotent_image_fixed`
- `localDefect`
- `aggregateDefect`
- `localDefect_zero_iff`
- `aggregateDefect_zero_iff`
- `idempotent_zero_defect`
- `identityKernel`
- `identityKernel_idempotent`
- `identityKernel_fixed`
- `zeroKernel`
- `zeroKernel_idempotent`
- `clampKernel`
- `clampKernel_idempotent`
- `support_monotone`
- `Kernel.comp`
- `Kernel.comp_self_eq`

## Senate Bundle Reference

Source: `jmd_senate.txt`.

This bundle is unrelated to the DASHI Agda port. It is indexed here only
because it is present locally and may otherwise confuse repo orientation.

### `Basic.lean`

- `ProceduralSource`
- `ProceduralSource.floorEnforceable`
- `committeeRule_not_floor_enforceable`
- `partyConferenceRule_not_floor_enforceable`
- `informalPractice_not_floor_enforceable`
- `standingRule_floor_enforceable`
- `constitution_floor_enforceable`
- `ProceduralSource.fromRulemakingAuthority`
- `standingOrder_from_rulemaking`
- `rulemakingStatute_from_rulemaking`
- `rulemaking_implies_floor_enforceable`
- `PrecedentOrigin`
- `PrecedentOrigin.weight`
- `senateVote_gt_presidingOfficerRule`
- `presidingOfficerRule_gt_parliamentaryInquiry`
- `senateVote_gt_parliamentaryInquiry`
- `precedent_weight_total`

### `Recognition.lean`

- `SenatorRole`
- `SenatorRole.priorityRank`
- `majorityLeader_highest_priority`
- `majorityLeader_before_minorityLeader`
- `minorityLeader_before_majorityManager`
- `majorityManager_before_minorityManager`
- `minorityManager_before_other`
- `majorityLeader_before_all`
- `other_senators_equal_priority`
- `recognizeFirst`
- `majorityLeader_always_recognized`

### `Voting.lean`

- `SenateAction`
- `VoteThreshold`
- `SenateAction.requiredThreshold`
- `VoteThreshold.strictness`
- `unanimousConsent_strictest`
- `cloture_on_rules_harder_than_general`
- `adopt_easier_than_cloture_on_rules`
- `waive_and_alter_uc_same_threshold`
- `overrule_is_majority`
- `totalSenateSeats`
- `quorumRequired`
- `quorum_is_51`
- `clotureThreshold`
- `cloture_threshold_is_60`
- `twoThirdsThreshold`
- `two_thirds_threshold_is_67`
- `cloture_exceeds_quorum`
- `two_thirds_exceeds_cloture`
- `recordedVoteFraction`
- `recorded_vote_fraction_is_one_fifth`
- `senatorsNeededForRecordedVote`
- `recorded_vote_at_quorum`
- `recorded_vote_full_attendance`

### `SenateManual.lean`

- `ManualComponent`
- `manual_has_seven_components`
- `ManualSection`
- `clotureSection`
- `standingOrderSectionRange`
- `standing_order_sections_count`
- `numStandingRules118th`
- `num_standing_rules`
- `fractionNewTerms`
- `fractionContinuing`
- `continuing_fraction_is_two_thirds`
- `continuing_exceeds_quorum_fraction`
- `adjournmentSections`
- `ruleXXXIII_section`
- `committeeRulesDeadline_section`

### `UCagreements.lean`

- `UCAgreement`
- `UCAgreement.floorEnforceable`
- `objectionsToBlockAlteration`
- `single_senator_can_block`
- `StandingOrderDuration`
- `ucStandingOrders118th`
- `uc_standing_orders_118th_is_11`
- `OverridableAuthority`
- `uc_overrides_all`

### `Enforcement.lean`

- `PointOfOrderOutcome`
- `AppealOutcome`
- `RulingEvent`
- `rulingNotAppealed_origin`
- `rulingAppealed_origin`
- `MandatorySubmission`
- `MandatorySubmission.debateAllowed`
- `germaneness_no_debate`
- `constitutional_questions_debatable`
- `establishes_precedent`
- `every_ruling_establishes_precedent`
- `presidingOfficerSuaSponte`
- `sua_sponte_under_cloture`
- `no_sua_sponte_without_cloture`

### `Committees.lean`

- `CommitteeRuleTopic`
- `CommitteeRulesSystem`
- `senateCommitteeRulesSystem`
- `lateCommitteeDeadlineDays`
- `late_committee_deadline_is_60`
- `CommitteeRulesVenue`
- `num_publication_venues`
- `CommitteeRulesVenue.mandatory`
- `only_record_mandatory`

### `RulemakingStatutes.lean`

- `RulemakingCategory`
- `three_rulemaking_categories`
- `budgetActYear`
- `lraYears`
- `lra_years_20th_century`
- `RulemakingStatute`
- `withRulemakingClause`
- `BudgetResolutionScope`
- `paygoFirstYear`
- `paygo_first_year_is_1993`
- `craIsExpedited`

### `Riddick.lean`

- `riddickCoverageStart`
- `riddickCoverageEnd`
- `riddick_coverage_span`
- `riddickPublicationYear`
- `RiddickTopicEntry`
- `clotureEntry`
- `clotureAmendmentSubtopics`
- `cloture_amendment_subtopics_is_18`
- `RiddickCitationStyle`
- `RiddickCitationStyle.indicatesInquiry`
- `riddickTenureStart`
- `riddickTenureEnd`
- `riddick_tenure_length`
- `fruminFirstTenureStart`
- `fruminFirstTenureEnd`
- `fruminSecondTenureStart`
- `fruminSecondTenureEnd`
- `frumin_total_tenure`
- `ucPrecedentsStartPage`
- `ucPrecedentsEndPage`
- `uc_precedents_pages`

### `Main.lean`

- `nine_procedural_sources`
- `six_floor_enforceable`
- `three_not_floor_enforceable`
- `enforceability_partition`
- `four_rulemaking_sources`
- `all_rulemaking_floor_enforceable`
- `rules_change_asymmetry`
- `rules_cloture_harder`
- `precedent_weight_injective`
- `precedent_weight_strict_total`
- `continuing_senators_at_least_66`
- `continuing_exceeds_quorum`
- `threshold_strict_order`
- `threshold_strictness_injective`
- `manual_and_rules_summary`
- `reference_sources_summary`
