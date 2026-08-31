# Lean → Agda reconciliation across the six fronts

This report answers one question, front by front: **for each item, is the content
a checked Lean theorem, an Agda record field that is *assumed*, an Agda `Bool`
ledger entry, or genuinely absent?**  It does not claim parity from shared
vocabulary, and it does not claim that any Lean proof term is an Agda proof
term.

## Snapshot provenance and what was and was not checked

| item | status |
|---|---|
| Agda snapshot in `Agda/` | refreshed this round from the newer handoff bundle (agda-suite pinned at `611e947ab9cc467faf27a5d7e9f86a46af4fba28`); 13 718 `.agda` modules |
| live Agda `master` | reported as `685940d7b0eb34be43b0be3279333ff090a3f301`, i.e. **ahead of the snapshot**; the merge train beyond the pin is not present here |
| Agda typechecking | **not performed** — no Agda toolchain is available in this environment.  Every Agda row below is read off the *source text* of the snapshot (record fields, `postulate`s, `Bool` ledgers), never from a successful check |
| Lean | `lake build` (all default targets: `Synthesis`, `Cuisine`, `AgdaMirror`, `Spine`, `Integration`) is clean, `sorry`-free; every headline theorem is `#print axioms`-audited to `propext, Classical.choice, Quot.sound` in `Lean/Integration/AxiomAuditVariation.lean` |
| Agda files | **no Agda file was created or modified** in this round |
| build configuration | the `AgdaMirror` library glob was `AgdaMirror.*`, which pulled in the root aggregate `Lean/AgdaMirror.lean` and therefore a Yang–Mills module deliberately absent from this cutset; it is now `AgdaMirror.+` (submodules only), matching the comment already in the lakefile, and the whole default target set builds |
| PR fronts #645/#646/#647 | the PR heads/patches are not part of the delivered material, so their content is **undetermined here** (see `PR_HEADS_STATUS.md`); no row below cites a PR ref |

Register legend used throughout:

* **L-thm** — a checked Lean theorem in this project;
* **A-field** — an Agda record *field*, i.e. an assumed hypothesis a user of the
  record must supply;
* **A-ledger** — an Agda `Bool` field pinned by `refl`, which records an
  intended reading but proves nothing about any machinery;
* **open** — no owner on either side.

---

## Front 1 — Stage-7 robust inference

Agda owners in the snapshot: `DASHI.Core.RobustExperimentInferenceFrontierExact`
(the frontier: a six-constructor `RobustnessObligation` enumeration, the
interface records `DiscrepancyModel`, `CorrelatedUncertaintyInterface`,
`ExperimentDesign`, `HeldOutRepair`, and the four-entry
`RobustExperimentFrontierBoundary` ledger),
`DASHI.Core.CalibratedExperimentInferenceExact`,
`DASHI.Core.PredictionEnvelopeExact`.

| obligation / boundary entry | Agda register | Lean register |
|---|---|---|
| model discrepancy `y = f_θ(x) + δ(x) + ε` | A-field (`DiscrepancyModel` interface; no semantics) | L-thm `Experiment.ModelDiscrepancy.truth_eq_model_add_discrepancy`, `fit_is_not_adequacy`, `fit_precise_yet_arbitrarily_inadequate` |
| "calibrated fit determines model adequacy" ≡ `false` | A-ledger | **refuted** as a proposition: `Reconciliation.Stage7Boundary.boundary_claims_are_false` |
| coverage under discrepancy | not present as a theorem | L-thm `Experiment.DiscrepancyCoverage.discrepancy_destroys_nominal_coverage`, `no_positive_level_under_discrepancy`, `inflated_tolerance_restores_full_coverage` |
| vector state/parameter/control dynamics, trajectory sensitivity | absent | L-thm `Experiment.VectorDynamics.output_sensitivity_chain_rule`, `sensitivity_column_unique`, `unexcited_parameter_makes_information_singular` |
| correlated uncertainty, attribution | A-field (`CorrelatedUncertaintyInterface`, with `propagationReceipt : Set` assumed) | L-thm `Experiment.CorrelatedUncertainty.totalVariance_split`, `correlated_variance_has_no_canonical_attribution` |
| "a diagonal variance budget solves correlated attribution" ≡ `false` | A-ledger | **refuted** (same theorem as above) |
| experiment design, information matrix | A-field (`ExperimentDesign`, with `criterionJustification : Set` assumed) | L-thm `Experiment.InformationMatrix.singular_iff_invisible_direction`, `criteria_disagree`, `all_three_criteria_disagree` |
| quantitative local identifiability | absent | L-thm `Experiment.IdentifiabilityRadius.certifiably_identifiable_within_radius`, `no_radius_without_curvature_control` |
| "local Jacobian rank gives global identifiability" ≡ `false` | A-ledger | **refuted** via `Experiment.LocalIdentifiability.local_identifiability_is_not_global` |
| held-out repair validation | A-field (`HeldOutRepair`, with `heldOutDiscriminationReceipt : Set` assumed) | L-thm `Experiment.RepairSearch.offset_repair_is_promoted`, `fit_and_refutability_do_not_give_a_held_out_prediction` |
| "a repair that fits the training data is scientifically supported" ≡ `false` | A-ledger | **refuted** (same) |
| observational equivalence of model ladders | absent | L-thm `Experiment.ObservationalEquivalence.obsClass_strictly_shrinks`, `pairwise_separation_does_not_give_one_discriminating_experiment` |

Net: on this front the Agda side owns the **architecture** (enumeration,
interfaces, ledger); the Lean side owns the **content**.  The reconciliation
module `Integration.Reconciliation.Stage7Boundary` makes that precise: all four
ledger entries become refuted propositions and all six obligations get a proved
generic statement (`boundary_and_obligations_are_different_registers`).

**Genuinely missing on both sides:** stochastic semantics (the Agda
`DiscrepancyModel` has none, and the Lean coverage lane is a
finitely-supported/level-set model, not a measure-theoretic one); parameter
differentiability of an actual flow (the Lean variational equation is a
*property* of the pair `(x, S)`, supplied, not derived).

---

## Front 2 — dense and symmetric pairing separation

Agda owner: `DASHI.Physics.Foundations.EinsteinCommonActionVariationFrontierExact`.
Its `EinsteinTensorVariationReceipt` has the **assumed field**

```
pairingSeparatesStressOnAdmittedDomain : … → left ≡ right
```

and its `EinsteinVariationBoundary` is a five-entry ledger.

| item | Agda register | Lean register |
|---|---|---|
| separation on the admitted fibre | **A-field (assumed)** | L-thm, and *characterised*: `Variation.Pairing.separates_iff_dense` (complete space: separation ⟺ dense fibre), `separates_iff_eq_top` (complemented case) |
| "equality of pairings ⇒ tensor equality without a separation theorem" ≡ `false` | A-ledger | **refuted**: `Reconciliation.QFTGRBoundary.pinned_false_entries_are_refuted`, via `Pairing.plane_pairing_does_not_separate` |
| "the tensor name alone determines the metric variation functional" ≡ `false` | A-ledger | **refuted**, via `Variation.CommonLanguage.mismatched_carrier_maps_do_not_weld` |
| "the field equation alone derives the common action" ≡ `false` | A-ledger | **refuted** (equal tensors, two carrier readings, two different functionals) |
| "separately named GR and QFT actions are one common action" ≡ `false` | A-ledger | **refuted**, via `CommonLanguage.separate_actions_do_not_weld` |
| "a finite additive `ℕ` action defines a metric functional derivative" ≡ `false` | A-ledger | **refuted** by a new theorem: `QFTGRBoundary.natValued_hasDerivAt_eq_zero` (a `ℕ`-valued action has zero derivative wherever differentiable) |
| "the action phase lift defines the stress tensor" ≡ `false` | A-ledger | **refuted** by a new theorem: `QFTGRBoundary.phaseLift_not_injective` |
| "common metric variation = Einstein pairing is still a physical theorem" ≡ `true` | A-ledger | proved content: the separation property is exactly density, so the Agda field is a genuine physical hypothesis and the Lean side names which one |
| "variation + separation + field equation builds the GR source" ≡ `true` | A-ledger | L-thm `CommonLanguage.stress_weld_of_dense_carrier`, `Variation.Weld.qftgr_stress_weld_of_cutset` |
| symmetric perturbations separate **symmetric** tensors | absent | L-thm `Variation.SymmetricFibre.*`, and at field level `Variation.SymmetricField.eq_of_fieldPair_eq_on_symmetric` |
| symmetric perturbations do **not** separate general tensors | absent | L-thm `SymmetricField.symmetric_field_perturbations_do_not_separate_general_fields` |
| a vanishing density weight hides a base point | absent | L-thm `SymmetricField.vanishing_density_hides_a_point`, packaged as `field_weld_hypotheses_are_load_bearing` |
| a **proper** admitted fibre that is nevertheless dense and separating | absent | L-thm `Variation.DenseFibre.proper_dense_admitted_fibre_exists`: in `ℓ²(ℕ,ℝ)` the finitely supported perturbations are a proper subspace, dense, and separating |

**Genuinely open (physical, not generic):** that the physical fibre of
compactly supported symmetric metric perturbations is dense in the space the
stress lives in; that the objects being separated are symmetric (a *hypothesis*
in the Lean field-level theorem, not a consequence).  What is now settled is
that the hypothesis is *satisfiable by a proper fibre*: the gap between
"separating" and "everything" is inhabited
(`DenseFibre.proper_dense_admitted_fibre_exists`), so requiring density is not a
disguised way of requiring the whole space.

---

## Front 3 — abstract continuum-functional existence

Agda owners: `DASHI.Physics.Foundations.BalabanAllSectorContinuumProducerExact`,
`…BalabanNativeSectorRecoveryTransportExact`,
`…BalabanTransportedSectorFamilyProducerExact`.  In all three the sector
continuum variation and the identity
`sectorContinuumVariationIsLiteralStressPairing` are **record fields**, i.e.
endpoint data assumed by the producer.

| item | Agda register | Lean register |
|---|---|---|
| the continuum sector variation is a stress pairing | A-field (assumed) | L-thm — *derived*: `Variation.CutoffLimit.exists_unique_continuum_stress` builds it (uniquely) from pointwise convergence of the cutoff pairings, over a complete space |
| existence of a continuum functional from cutoff data | absent | L-thm `CutoffLimit.exists_unique_continuum_functional` (Banach–Steinhaus/Riesz style, under the stated completeness hypotheses) |
| scalar limit interchange | absent | L-thm `CutoffLimit.scalar_limit_interchange` |
| convergence of pairings is not convergence of tensors | absent | L-thm `CutoffLimit.pairing_convergence_is_not_tensor_convergence`, `l2_pairing_convergence_is_not_tensor_convergence` |
| a divergent cutoff family has no continuum pairing | absent | L-thm `CutoffLimit.divergent_cutoff_family_has_no_continuum_pairing` |
| `downstreamCommonActionNeedsIndependentConvergenceRelation ≡ false` | A-ledger | **refuted**: `Reconciliation.ContinuumProducerBoundary.ledger_false_entry_is_refuted` |
| `endpointSectorVariationPlusExactAggregationIsSufficient ≡ true` | A-ledger | L-thm `ContinuumProducerBoundary.endpoint_aggregation_suffices` (hypothesis list contains no convergence relation) |

**Genuinely open:** concrete cutoff estimates for any physical sector family —
nothing here shows that a physical cutoff family converges.

---

## Front 4 — sector aggregation and summability

| item | Agda register | Lean register |
|---|---|---|
| finite sector aggregation `T_total = Σ_G T_G` | A-field / A-ledger (the producer records assume the aggregation identity) | L-thm `CutoffLimit.sector_aggregate_variation`, `sector_aggregation_commutes_with_cutoff_limit` |
| infinite (summable-family) aggregation | absent | L-thm `CutoffLimit.sector_aggregate_variation_tsum`, `ContinuumProducerBoundary.endpoint_aggregation_suffices_tsum`, `Variation.SectorFilter.hasSum_pair` |
| one sector is not the total | absent | L-thm `CutoffLimit.one_sector_is_not_the_total` |
| aggregation along an exhaustion ≠ unconditional total | absent | L-thm `SectorFilter.exhaustion_total_is_not_the_unconditional_total`, with the explicit conditionally convergent witness `SectorFilter.conditionally_convergent_sector_family` |
| uniqueness of the exhaustion total | absent | L-thm `SectorFilter.exhaustion_total_unique` |

So the summability hypothesis that the infinite aggregation results carry is
**not removable**, and the Lean side has the counterexample that shows it.

**Genuinely open:** summability of the *physical* sector family.

---

## Front 5 — source-coordinate calculus

| item | Agda register | Lean register |
|---|---|---|
| `D²(E∘A) = D²E[A',A'] + DE[A'']` | no non-YM/non-NS owner found in the snapshot (the search for a source-coordinate chain-rule owner outside those two lanes returned only general calculus modules, which this round does not claim as owners) | L-thm `Variation.SourceCoordinate.second_deriv_comp`, with the affine corollary and a counterexample to the naive identification |
| third order: `(f∘A)''' = f'''(A)(A')³ + 3f''(A)A'A'' + f'(A)A'''` | absent | L-thm `Variation.ThirdOrder.third_deriv_comp`, `third_deriv_comp_affine`, `third_order_correction_is_load_bearing` |
| metric-density variation `δ√(−det g)` | absent | L-thm `Variation.MetricDensity.*` |
| inverse-metric variation `δ(g⁻¹) = −g⁻¹(δg)g⁻¹` | absent | L-thm `Variation.InverseMetric.hasDerivAt_inv_add_smul`, `inverse_variation_is_injective`, and the combined `hasDerivAt_sqrt_neg_det_smul_inv` |
| the same law along a curve in a **normed space**: `D²(E∘A) = D²E[A',A'] + DE[A'']` | absent | L-thm `Variation.SourceCoordinateBanach.second_deriv_comp_curve`, with the affine case, the reduction `second_fderiv_apply_real` to `f''(x)v²` in one dimension, and `banach_third_term_is_load_bearing` |
| third order along a curve in a normed space | absent | L-thm `SourceCoordinateBanach.third_deriv_comp_curve` (no symmetry used) and `third_deriv_comp_curve_symm` (`+ 3 D²E[A',A'']`, via symmetry of the second derivative) |

The metric results (`MetricDensity`, `InverseMetric`) are finite-matrix; the
second- and third-order source-coordinate laws now hold for an arbitrary real
normed space along a `C²`/`C³` curve.

**Genuinely open:** the Einstein–Hilbert variation itself.  The two algebraic
ingredients (density and inverse metric) are proved; the curvature term is not,
and nothing in this corpus derives `δ(√(−g) R)`.

---

## Front 6 — the open PR fronts

Not determinable from the delivered material: no PR heads, patches or refs are
present (see `PR_HEADS_STATUS.md`, whose findings this round re-confirmed on the
refreshed snapshot).  No claim is made about what #645/#646/#647 do or do not
already contain.

---

## What this round added

| file | content |
|---|---|
| `Lean/Integration/Variation/SymmetricField.lean` | symmetric 2-tensor **fields** with a density weight; separation, its two failure modes, and `field_weld_hypotheses_are_load_bearing` |
| `Lean/Integration/Variation/InverseMetric.lean` | `δ(g⁻¹) = −g⁻¹(δg)g⁻¹`, its symmetry, injectivity, and the densitised inverse metric |
| `Lean/Integration/Variation/SectorFilter.lean` | exhaustion totals vs unconditional sums, with an explicit conditionally convergent sector family |
| `Lean/Integration/Variation/ThirdOrder.lean` | the third-order source-coordinate law |
| `Lean/Integration/Variation/DenseFibre.lean` | a proper, dense, separating admitted fibre in `ℓ²(ℕ,ℝ)` |
| `Lean/Integration/Variation/SourceCoordinateBanach.lean` | the second- and third-order source-coordinate laws for a curve in a real normed space, with the one-dimensional reduction and the symmetric third-order form |
| `Lean/Integration/Reconciliation/Stage7Boundary.lean` | front 1: the Stage-7 ledger refuted, the six obligations discharged generically |
| `Lean/Integration/Reconciliation/QFTGRBoundary.lean` | front 2: the two QFT/GR ledgers — six `false` entries refuted (two by new theorems), three `true` entries given proved content |
| `Lean/Integration/Reconciliation/ContinuumProducerBoundary.lean` | fronts 3–4: the producer ledger settled; endpoint aggregation sufficiency, its `tsum` form, and the load-bearing summability hypothesis |

All of these are imported by the `Integration` aggregate and audited in
`Lean/Integration/AxiomAuditVariation.lean`.

## The honest frontier — exact remaining obligations

1. **Einstein–Hilbert curvature variation.**  Derive `δ(√(−g) R)`; only the
   density and inverse-metric factors are proved.
2. **The physical perturbation carrier.**  Define the actual symmetric
   tensor-field perturbation space of a spacetime (the Lean model is a finite
   base with a weight), and prove its admitted physical fibre is dense — the
   exact hypothesis `Pairing.separates_iff_dense` shows is required.
3. **Instantiating the continuum hypotheses.**  Show a physical cutoff family
   satisfies the pointwise convergence hypothesis of
   `CutoffLimit.exists_unique_continuum_stress`.
4. **Physical sector summability.**  Show the physical sector family is
   summable, or fix an exhaustion and accept the order dependence that
   `SectorFilter` exhibits.
5. **The fully bi-Banach source-coordinate calculus.**  The second- and
   third-order laws are proved for a curve into an arbitrary real normed space;
   the form with a Banach-valued *substitution* (`A : Y → X` rather than
   `A : ℝ → X`) is not proved.
6. **Stochastic semantics for Stage 7.**  The coverage lane is combinatorial;
   a measure-theoretic coverage statement is not proved.
7. **Parameter differentiability of the flow.**  The variational equation is a
   supplied property of `(x, S)`, not derived from a generic flow.
8. **Cross-language transport.**  Nothing here makes a Lean proof term an Agda
   proof term.  Turning any row above into an Agda receipt means restating it in
   Agda and checking it there, with an Agda toolchain — which this environment
   does not have.
