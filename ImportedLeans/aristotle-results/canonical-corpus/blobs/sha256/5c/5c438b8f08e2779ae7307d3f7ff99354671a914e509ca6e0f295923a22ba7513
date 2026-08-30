# Stage 6 — calibrated dynamical inference

Seven new Lean modules under `Lean/Integration/Experiment/`, all sorry-free, all
imported by `Lean/Integration.lean` (entries 51g–51m) and audited in
`Lean/Integration/AxiomAudit.lean`.  Six of them open a lane each; the seventh,
`CalibratedCell.lean`, is the acceptance instance that carries one synthetic
dynamical experiment through every lane at once.

Verification state at the time of writing: `lake build` succeeds (8338 jobs);
`Integration.AxiomAudit` emits 897 `#print axioms` lines and every one reports a
subset of `{propext, Classical.choice, Quot.sound}`; no `sorry`, no project
axiom, no `native_decide`, no `@[implemented_by]`.

Nothing below is a physical claim.  Every "experiment" is a Lean record of
declared numbers; every theorem is a statement about those records.

---

## 1. Lane 1 — coverage / calibration semantics

`Integration.Experiment.CoverageSemantics`.  The missing scientific concept was
`P_θ(θ ∈ C(Y)) ≥ 1 − α`.  A `SamplingModel Θ Ω` gives, for each parameter, a
probability mass function on a finite outcome space; `coverageProb S C θ` is the
mass of the outcomes whose reported region contains `θ`, and `HasLevel S C l`
says this is `≥ l` uniformly in `θ`.

| Statement | Kind | Content |
|---|---|---|
| `coverageProb_nonneg`, `coverageProb_le_one` | theorem | coverage is a probability |
| `coverageProb_eq_one_iff` | theorem | full coverage ⇔ every positive-mass outcome reports a region containing `θ` |
| `coverageProb_mono`, `hasLevel_mono`, `hasLevel_of_le` | theorem | monotonicity in the region and in the level |
| `level_le_one` | theorem | a nonempty model admits no level above 1 |
| `coverage_inter_ge`, `hasLevel_inter` | theorem | Bonferroni: intersecting an `a`-level and a `b`-level region gives level `a + b − 1` |
| **`tolerance_procedure_has_full_coverage`** | theorem | under bounded noise, the Stage-4 tolerance region is a **coverage-one** procedure |
| `tolerance_procedure_hasLevel` | theorem | hence has every level `≤ 1` |
| `full_coverage_is_free`, `trivial_procedure_hasLevel` | negative | the whole parameter space always has coverage one — level alone is worthless |
| `credible_mass_is_not_coverage`, `coverage_is_not_credible_mass` | negative | the two masses are provably different numbers on `blindModel`/`skewedPrior` |
| **`no_function_from_envelope_to_level`** | negative | no function from a reported region to a coverage level can be correct: identical regions occur with different coverage |

The three interval kinds stay separate by construction: a prediction envelope is
a `Set` of predicted values, a credible region carries a `FinPMF`/density mass,
a confidence region carries a `HasLevel` proof, and the negatives above prove no
automatic coercion between them exists.

## 2. Lane 2 — continuous Bayesian parameter inference

`Integration.Experiment.ContinuousBayes`.  A `ParamPrior` is a continuous,
nonnegative density on a compact interval `[lo, hi]` integrating to 1.

| Statement | Kind | Content |
|---|---|---|
| `evidence`, `posterior` | definition | `∫ L·π` and `L(θ)π(θ)/evidence` |
| `evidence_nonneg`, `posterior_nonneg` | theorem | signs |
| `posterior_integral_eq_one` | theorem | the posterior is again a density |
| `posterior_pos_iff` | theorem | support characterisation |
| `zero_prior_stays_zero` | theorem | Bayes cannot create support |
| `bayes_ratio` | theorem | division-free posterior odds |
| `flat_likelihood_leaves_the_prior` | theorem | uninformative data changes nothing |
| `no_posterior_of_total_refutation` | theorem | total refutation gives evidence 0, no posterior |
| `update`, `sequential_is_batch` | definition/theorem | updating is associative in the data |
| **`posterior_support_subset_compatible`** | theorem | `supp π(·∣y) ⊆ Θ_y` — the architecture-preserving bridge |
| **`region_does_not_determine_the_posterior`** | negative | `uniform01` and `tilted01` have the same surviving region and different posteriors |

## 3. Lane 3 — the uncertainty budget derived from the graph

`Integration.Experiment.VarianceBudget`.  Input covariance `RCov n` plus a
certified derivative row gives the propagated variance and its contribution
shares.

| Statement | Kind | Content |
|---|---|---|
| `totalVariance`, `ownShare`, `shareFraction` | definition | `rᵀ S r`, `rᵢ²Sᵢᵢ`, and its fraction |
| `totalVariance_eq_push`, `totalVariance_eq_dotProduct` | theorem | agrees with the existing `Cov.push` compiler field |
| `totalVariance_nonneg`, `ownShare_nonneg`, `variance_diag_nonneg` | theorem | signs |
| `totalVariance_diag` | theorem | for a diagonal covariance the total is exactly `Σ rᵢ²σᵢ²` |
| `shareFraction_sum_eq_one` | theorem | the shares are a genuine decomposition |
| `exists_dominant_input`, `dominant_share_ge_average` | theorem | a maximiser exists and carries at least `1/n` of the variance |
| `zeroing_removes_exactly_its_share` | theorem | perfecting input `i` removes exactly `rᵢ²σᵢ²` |
| **`reducing_the_dominant_helps_most`** | theorem | measurement selection by *actual variance reduction*, not by a declared modulus |
| `totalVariance_mono` | theorem | monotone in the input variances |
| **`derivedBudget_is_from_certified_derivatives`** | theorem | the budget is the propagated variance of the *proved* derivative row |
| `shares_do_not_account_for_correlation` | negative | with `fullyCorrelated` inputs the shares miss the cross terms |
| `derived_budget_ignores_model_discrepancy` | negative | two certified laws with the same row have the same budget and different values |

## 4. Lane 4 — nonlinear local identifiability

`Integration.Experiment.LocalIdentifiability`.  `measurementMap F ts` is
`θ ↦ (F.predict θ tⱼ)ⱼ`; `LocallyIdentifiable h θ` is local injectivity;
`InvisibleDirection J v` is a nonzero `v` in `ker J`.

| Statement | Kind | Content |
|---|---|---|
| **`locallyIdentifiable_of_injective_deriv`** | theorem | an antilipschitz derivative gives local identifiability (`rank J = n ⇒` locally identifiable) |
| `exact_readings_pin_down_locally` | theorem | the payoff for a measurement map: readings pin the parameter down near `θ` |
| `invisible_direction_of_not_injective` | theorem | a non-injective Jacobian exhibits an invisible direction |
| `invisible_direction_vanishes_to_first_order` | theorem | along it the measurements change to `o(t)` |
| **`few_measurements_give_invisible_direction`** | theorem | `m < n` ⇒ an invisible direction for *every* model at *every* operating point |
| **`tolerance_cannot_repair_missing_rank`** | theorem | the obstruction is independent of the tolerance |
| `first_order_test_is_only_first_order` | negative | `θ ↦ θ³` is injective with zero derivative |
| `local_identifiability_is_not_global` | negative | local identifiability everywhere does not give global |

## 5. Lane 5 — trajectory sensitivities

`Integration.Experiment.TrajectorySensitivity`.  A `ParamSystem` is a scalar
field `f(x, θ, t)` on a compact window whose partials `f_x`, `f_θ` come with
their derivative certificates.  `IsSensitivity θ x s` is the variational
equation `ṡ = f_x·s + f_θ`, `s(0) = 0`.

| Statement | Kind | Content |
|---|---|---|
| `ParamSystem`, `IsParamTrajectory`, `IsSensitivity` | structure | the system, its trajectory, the variational equation |
| `sensitivity_unique` | theorem | the sensitivity is unique on the window (via ODE uniqueness) |
| **`sensitivity_bound`** | theorem | Grönwall: `\|s(t)\| ≤ B(e^{Kt} − 1)/K` — a *computed* modulus |
| `constantRate_isParamTrajectory`, `constantRate_isSensitivity` | theorem | worked instance `ẋ = −θ` |
| **`constantRate_sensitivity_is_the_theta_derivative`** | theorem | the solved sensitivity really is `∂x/∂θ`: the interchange is verified, not assumed |
| `locally_identifiable_of_nonzero_sensitivity` | theorem | nonzero sensitivity ⇒ local identifiability at that reading time |
| `zero_sensitivity_time_is_first_order_blind` | negative | a zero-sensitivity time sees nothing to first order |
| `most_sensitive_reading_is_maximal`, `most_sensitive_reading_mem` | theorem | the computed sensitivity drives the existing Stage-5 selector |

## 6. Lane 6 — repair obligations

`Integration.Experiment.RepairObligations`.  Sharpening the obligation *before*
any search, and enforcing `repair restores fit ⇏ repair gains support`.

| Statement | Kind | Content |
|---|---|---|
| `RepairClass`, `repairClass_card` | inductive/theorem | exactly the six declared classes (parameter, latent state, interaction, dynamics, measurement model, source assumption) |
| `Functional`, `interpolant`, `interpolant_at_reading`, `interpolant_mem_compatible` | definition/theorem | any functionally consistent dataset is interpolated exactly |
| **`freeFamily_fits_everything`** | theorem | the unrestricted patch generator fits every functionally consistent dataset |
| **`freeFamily_not_refutable`**, `freeFamily_predicts_nothing` | negative | and therefore says nothing |
| `Refutable`, `RepairProposal` | definition/structure | refutability is a *field* of a proposal — the gate |
| **`saturated_repair_is_no_proposal`** | theorem | hence the free family cannot inhabit `RepairProposal` |
| `offsetData_functional`, `proportional_family_cannot_fit_the_offset_data`, `offsetRead_fits`, `offsetRead_refutable`, `offsetProposal` | theorem/definition | worked contrast: the classes are not interchangeable, a measurement-model repair earns status a parameter repair cannot |

## 7. The milestone instance

`Integration.Experiment.CalibratedCell` instantiates the whole stack on the
synthetic dynamical experiment of `LithiumContinuous`:

```
ż = −θ,  z(0) = 0.9,  window [0, 10],  y = z,  θ ∈ [0.02, 0.04]
one reading:  t = 4,  y = 0.78,  tolerance 0.01
```

| Milestone item | Theorem | Reused generic result |
|---|---|---|
| certified trajectory sensitivity | `cell_trajectory_sensitivity`, `cell_sensitivity_is_the_theta_derivative` | lane 5 |
| confidence region | `cell_region_is_a_coverage_one_procedure` | lane 1 |
| posterior over a continuous parameter | `cell_evidence_pos`, `cell_posterior_is_a_density` | lane 2 |
| posterior support inside the deterministic region | `cell_posterior_support_subset_compatible`, `cell_posterior_support_subset_surviving_region` | lane 2 bridge |
| prediction interval | `endpoint_envelope_after_the_first_reading` | Stage 4 |
| derived uncertainty budget and shares | `cell_budget_total`, `initial_state_dominates` | lane 3 |
| optimal next measurement | `endpoint_is_the_most_sensitive_time`, `perfecting_the_initial_state_helps_most` | lanes 3, 5 |
| model-family refutation | `family_is_falsified_by_the_low_reading` | Stage 4 |
| classified, refutable repair | `offsetCellFamily_fits`, `offsetCellFamily_refutable`, `cellRepairProposal` | lane 6 |

The file is deliberately data-only: no new mathematics is proved there, every
conclusion is an application of a lane theorem to declared numbers.

One design correction worth recording: the generic support bridge requires
`0 < density θ → θ ∈ F.prior`, which a globally constant density does not
satisfy.  The instance therefore derives prior membership from the *likelihood*
support (`cellLikelihood_pos_prior`), not from the density.

## 8. Dependency / provenance map

```
Experiment.Core  (Reading, ParamFamily, Compatible)          [Stage 4]
   │
   ├── ProbabilityLayer (FinPMF)  ──────────┬──> CoverageSemantics      (lane 1)
   │                                        │
   ├── ParameterRegion, LithiumContinuous ──┼──> ContinuousBayes        (lane 2)
   │                                        │
   ├── CertifiedPropagation (CertifiedSensitivity, RCov, Cov.push)
   │        └──────────────────────────────────> VarianceBudget         (lane 3)
   │
   ├── MultiParameterRegion (affine rank obstruction)
   │        └──────────────────────────────────> LocalIdentifiability   (lane 4)
   │
   ├── ContinuousDynamics, BestReading ────────> TrajectorySensitivity  (lane 5)
   │
   └── ModelSelection ─────────────────────────> RepairObligations      (lane 6)

   all six  +  LithiumContinuous  ────────────> CalibratedCell          (milestone)
                                                      │
                                    Integration.lean 51g–51m,  AxiomAudit
```

External support used: Mathlib's `intervalIntegral`,
`intervalIntegral.intervalIntegral_pos_of_pos_on`,
`ODE_solution_unique_of_mem_Icc_right`, the Grönwall lemmas, `AntilipschitzWith`
and `HasFDerivAt`.  No Agda file was rechecked (no Agda toolchain here); nothing
in this stage depends on the Agda mirrors.

## 9. Which Stage-5 frontier items are now closed

| Stage-5 item | Status after Stage 6 |
|---|---|
| 1. Bayes stops at the finite family | **closed in 1-D**: `ContinuousBayes` gives a density posterior on a compact interval with the support bridge.  Multi-parameter remains open. |
| 2. No coverage statement | **closed**: `CoverageSemantics` gives `HasLevel`, and the tolerance procedure is proved coverage-one under bounded noise.  The three interval kinds remain provably distinct. |
| 3. Declared tolerances / noise bounds | **open, unchanged**: nothing estimates an instrument model. |
| 4. Certification per-edge and opt-in | **open, unchanged**. |
| 5. Budget separately declared | **closed**: `derivedBudget` is computed from the certified derivative row and the input covariance, with proved contribution shares and a selection theorem. |
| 6. Multi-parameter identifiability only affine | **closed**: `locallyIdentifiable_of_injective_deriv` and `few_measurements_give_invisible_direction` are the Jacobian versions. |
| 7. Nonlinear discrimination ranks guarantees only | **partly closed**: lane 3 now ranks by actual variance reduction; the modulus ranking is unchanged and still only a guarantee. |
| 8. Repairs classified, not searched | **partly closed**: the classes are now an inductive type with a refutability gate, and the saturated repair is proved inadmissible.  No search exists. |

Additionally the Stage-5 dynamics gap is now partly closed: trajectory
sensitivities exist for scalar parametric systems.

## 10. Honest frontier — exact remaining obligations

1. **The variational equation is a hypothesis, not a derivation.**
   `IsSensitivity` is assumed of `(x, s)`; the general theorem that
   `∂x/∂θ` *satisfies* it (differentiability of the flow in the parameter) is
   not proved.  It is verified only in the worked instance `constantRate`.
2. **Coverage is finite-sample-space only.** `SamplingModel` requires
   `Fintype Ω`; there is no continuous noise model, no asymptotic coverage, no
   confidence interval constructed by inversion of a continuous test.
3. **Continuous Bayes is one-dimensional.** A single real parameter, a Lebesgue
   density on a compact interval, no product priors, no posterior contraction,
   no consistency, no decision theory.
4. **Share accounting assumes a diagonal input covariance.**
   `shareFraction_sum_eq_one`, `zeroing_removes_exactly_its_share` and
   `reducing_the_dominant_helps_most` are stated for `RCov.diag`; the correlated
   case is only given a negative (`shares_do_not_account_for_correlation`).
5. **Model discrepancy is still undeclared.** `derived_budget_ignores_model_discrepancy`
   proves the budget cannot see it; no term in any structure represents it.
6. **Local identifiability is local and first-order.** No global identifiability,
   no radius estimate for the neighbourhood, no rank condition checked
   automatically for a given family.
7. **Only scalar dynamics.** `ParamSystem` has a scalar state and a scalar
   parameter; vector states, several parameters, control inputs `u`, and Fisher
   information are all absent.
8. **Repairs are gated but not searched.** No enumeration, no cost, no proposal
   generator; `RepairProposal` must be constructed by hand.
9. **Tolerances, noise bounds, priors and likelihoods are all declared data.**
   Nothing in the corpus estimates them, and no theorem claims they are correct
   for any real system.

## 11. What this does *not* claim

No physical theory-of-everything claim, and no claim about lithium cells,
batteries, thermal systems, safety or instrumentation.  A "posterior" here is a
normalised density under a declared likelihood; a "confidence region" is a
region with a proved `HasLevel` under a declared sampling model; a "sensitivity"
is a proved derivative of a declared model.  Whether any of these declared
objects describes a real experiment is outside the corpus.
