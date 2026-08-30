# Stage 5 — weighted inference, several parameters, and certified propagation

Stage 3 (`TOE_EXPERIMENT_CALCULUS.md`) built a finite, discrete-time experiment
calculus; Stage 4 (`TOE_STAGE4_INFERENCE.md`) made it continuous and
deterministic and added a probability layer that deliberately stopped at the
likelihood. This round takes four of the exact obligations that report left
open and discharges what is actually provable in each.

| Stage-4 frontier item | This round |
|---|---|
| 1 — "no prior, no posterior, no Bayes rule … nothing connects the likelihood to the parameter regions" | **closed for finite families**: `Integration/Experiment/BayesUpdate.lean` |
| 8 — "multi-parameter regions are not developed" | **closed**: `Integration/Experiment/MultiParameterRegion.lean` |
| 3 — "certification is opt-in … `compile` still does not invoke `Cov.push`" | **closed**: `Integration/Experiment/CertifiedPropagation.lean` + two new compiler fields |
| 5 — "the next-measurement optimisation is affine-only" | **generalised, with the honest limit**: `Integration/Experiment/NonlinearDiscrimination.lean` |

Everything below is machine-checked Lean. The whole project builds
(`lake build`, 8 331 jobs, no errors); there is no `sorry`, no `admit`, no
project `axiom`, no `@[implemented_by]` and no `native_decide`; the axiom audit
(`Lean/Integration/AxiomAudit.lean`, 54 new `#print axioms` lines this round)
reports only `propext`, `Classical.choice` and `Quot.sound`. No Yang–Mills or
Navier–Stokes material was read, referenced or modified.

**One build repair.** The `AgdaMirror` library glob in `lakefile.toml` had again
regressed to `AgdaMirror.*`, which pulls in the root aggregate
`Lean/AgdaMirror.lean`; that aggregate imports the Yang–Mills mirror excluded
from this cutset, so `lake build` failed during job computation before any Lean
file was elaborated. It is back to `AgdaMirror.+`, exactly as the comment beside
it documents. No Yang–Mills file was read or added.

---

## 1. Lane 1 — Bayes' rule, and the bridge to the set-valued core

`Integration/Experiment/BayesUpdate.lean`.

`evidence p lik = ∑ π(h)L(h)`; `posterior p lik hnn hpos` is Bayes' rule
returned as a genuine `FinPMF` (masses proved nonnegative, proved to sum to
one), so nothing downstream depends on an unnormalised weight.

| Theorem | Content |
|---|---|
| `evidence_pos_iff` | an update is possible exactly when some hypothesis has both positive prior and positive likelihood |
| `posterior_pos_iff` | the posterior support is exactly `prior support ∩ likelihood support` |
| `zero_prior_stays_zero` | no resurrection: a hypothesis excluded a priori is never revived by data |
| `bayes_factor` | posterior odds = prior odds × likelihood ratio, in division-free form |
| `posterior_mono` | equal priors, ordered likelihoods ⇒ ordered posteriors |
| `sequential_is_batch` | updating on `L₁` then `L₂` equals one update on `L₁·L₂` |
| `flat_likelihood_leaves_the_prior` | the probabilistic form of the Stage-3 negative "data cannot separate identical predictions" |
| `posterior_concentrates` | a single surviving hypothesis gives its point mass |
| `no_posterior_of_total_refutation` | all likelihoods zero ⇒ zero evidence ⇒ no posterior: refutation is at the level of the family |

**The bridge** (what Stage 4 said was missing). `jointLikelihood` multiplies the
per-reading likelihoods of the Stage-4 `MeasurementModel` along the predictions
of a `ParamFamily`.

| Theorem | Content |
|---|---|
| `jointLikelihood_pos_iff_all_pos` | positive jointly ⇔ positive on every reading |
| `positive_joint_likelihood_fits` | with noise bounded by each reading's declared tolerance, positive likelihood ⇒ the reading is *fitted* in the set-valued sense |
| `posterior_support_subset_compatible` | **the posterior's support lies inside the surviving parameter region `Θ_E`** |
| `posterior_support_subset_compatible_cons` | the same, reading by reading |
| `falsified_family_has_no_posterior` | a falsified family has zero evidence, so the probabilistic layer inherits the typed model-family failure instead of silently renormalising |

and the two negatives that stop the bridge being read as an identification:
`compatible_does_not_determine_the_posterior` (same region and same likelihood,
different posteriors — a region carries no weights) and
`posterior_support_can_be_strictly_smaller` (a tolerance-compatible parameter
can have zero posterior mass).

## 2. Lane 2 — surviving regions in several parameters

`Integration/Experiment/MultiParameterRegion.lean`, over an arbitrary real
normed parameter space.

| Theorem | Content |
|---|---|
| `affineConstraint_convex`, `affineConstraint_isClosed` | one reading of a parameter-affine family cuts a convex closed slab |
| `affineCompatible_convex`, `affineCompatible_isClosed` | so the surviving region is convex and closed whenever the prior region is |
| `affineCompatible_ordConnected` | the Stage-4 one-dimensional interval result is the `dim = 1` case |
| `envelope_ordConnected_of_isPreconnected` | a continuous consumer over a connected region has an **interval** envelope |
| `envelope_eq_Icc_of_isCompact` | over a nonempty compact connected region the envelope is exactly `[min, max]`, both attained |

The genuinely multi-dimensional content is the identifiability dichotomy:

| Theorem | Content |
|---|---|
| `unidentified_direction_survives` | a direction invisible to every reading is never resolved: the region is invariant along it |
| `envelope_not_a_point_of_unidentified_direction` | a consumer seeing that direction has a non-point envelope — this does not shrink when the tolerances do |
| `few_readings_do_not_identify` | with `k < d` readings of a `d`-parameter affine family such a direction always exists (rank–nullity): the obstruction is a **rank** condition |
| `exact_readings_identify` | conversely, jointly injective gradients read exactly pin the parameter to a point |

A two-parameter line instance (`lineGrad`, `lineTruth`, `exactReading`) shows
both sides are satisfiable: one exact reading leaves a whole line
(`line_one_reading_does_not_identify`), two fix the parameter
(`line_two_exact_readings_identify`).

## 3. Lane 3 — certified sensitivities and a compiler that propagates them

`Integration/Experiment/CertifiedPropagation.lean`, plus two new fields in
`Integration/Experiment/Compiler.lean`.

`CertifiedLaw n` is a quantity-graph `Law` together with a real extension
`realEval` of its rational `eval`, the proof `agrees` that they agree on
rational inputs, and the proof `certified` that the edge's **own declared**
`sensitivity` list is the vector of partial derivatives of that extension.
`chargeCertificate` (`Q = I t`) and `energyCertificate` (`E = V Q`) discharge it
for two edges.

`ExperimentSpec` gains `inputVariances` (default `[]` — *nothing declared*) and
`ExperimentPrediction` gains `propagatedVariance`, which `compile` computes.

| Theorem | Content |
|---|---|
| `compile_propagatedVariance` | the reported number is the declared row applied to the declared variances |
| `compile_propagatedVariance_eq_push` | and it **is** `Cov.push` of that row against the diagonal input covariance — the compiler now invokes first-order propagation itself |
| `compile_propagatedVariance_nonneg` | nonnegative when the declared variances are |
| `compile_propagatedVariance_of_nothing_declared` | with nothing declared it is `0` — a *declaration gap*, not an uncertainty claim |
| `compile_variance_from_certified_derivatives` | with a `CertifiedLaw` supplying the row, every factor is a genuine partial derivative |
| `propagation_cannot_detect_a_wrong_row` | the compiler's output is a function of the row it is given: an uncertified row is equally well typed |
| `certificate_does_not_make_propagation_exact` | a certified derivative is still only first order |

Instantiated on the lithium cell (data only): `propagated_variance_is_computed`
(`1/20` from `(∂T/∂R, ∂T/∂I) = (10, 20)` and input variances `10⁻⁴`),
`propagated_variance_is_the_push`, and the honest
`propagated_variance_is_not_the_declared_budget` — populating the three-way
budget from the graph remains open, and nothing here silently does it.

## 4. Lane 4 — measurement choice beyond the affine case

`Integration/Experiment/NonlinearDiscrimination.lean`.

`SeparationModulus F t L θ*` says `L·|θ − θ*| ≤ |predict θ t − predict θ* t|` for
every prior parameter: a hypothesis about the model that needs no slope,
monotonicity or differentiability.

| Theorem | Content |
|---|---|
| `compatible_subset_Icc_of_modulus` | one reading with modulus `L > 0` confines the region to half-width `tol / L` |
| `affine_separationModulus` | affine families have modulus `\|slope\|`, so the Stage-4 result is the special case |
| `separationModulus_mono`, `guaranteedRadius_antitone` | a modulus is a lower bound; a larger one is a smaller guaranteed radius |
| `mostSeparating_guarantee_is_best` | the Stage-4 selector, applied to declared moduli, gives the smallest guaranteed radius offered |
| `mostSeparating_region_within_guarantee` | and the region really is inside it |
| `bigger_modulus_does_not_contract_more` | **the honest limit**: a larger modulus does *not* give a smaller region, so this ranks guarantees, not regions |
| `guarantee_is_vacuous_at_zero_modulus` | a reading blind to the parameter admits no positive modulus and guarantees nothing |

## 5. Dependency / provenance map

```
Integration.Experiment.ParameterRegion            (Stage 4)
   ├── Experiment.MultiParameterRegion            (new: convexity, envelope shape, identifiability)
   ├── Experiment.BestReading                     (Stage 4)
   │      └── Experiment.NonlinearDiscrimination  (new: separation modulus, guarantees)
   └── Experiment.BayesUpdate                     (new: Bayes rule + bridge)
            └── Experiment.ProbabilityLayer       (Stage 4: FinPMF, likelihood)

Integration.Experiment.QuantityGraph  ┐
Integration.Experiment.Uncertainty    ├── Experiment.CertifiedPropagation (new)
Integration.Experiment.Compiler       ┘        └── Experiment.Lithium §11 (instance, data only)
```

Modified existing files: `Compiler.lean` (two new fields, one new line in
`compile`; both additions are defaulted or computed, so no instance changed),
`Lithium.lean` (declared input variances and a new §11), `Integration.lean`
(imports and four module-doc entries), `AxiomAudit.lean` (imports and 54 audit
lines), `lakefile.toml` (the glob repair). No existing theorem was restated or
weakened.

## 6. Honest frontier — exact remaining obligations

1. **Bayes stops at the finite family.** `posterior` is over a `Fintype`; there
   is no continuous prior, no posterior *density* over the parameter regions of
   the continuous lane, no asymptotics, no consistency and no decision theory.
   The bridge is an inclusion of supports, not a measure on `Θ_E`.
2. **No coverage statement.** Nothing here attaches a probability to a reported
   interval, and the three separation theorems of the probability layer
   (`envelope ≠ confidence ≠ credible`) still stand unweakened.
3. **Tolerances and noise bounds are declared.** Unchanged from Stage 4:
   nothing estimates an instrument model from repeated measurements.
4. **Certification is still per-edge and opt-in.** Two edges carry a
   `CertifiedLaw`; the remaining `Law` values in the quantity graph carry
   uncertified rational sensitivity lists, and `ExperimentSpec.inputVariances`
   is declared data whose first components are only *proved* to be derivatives
   when a certificate is supplied alongside.
5. **The uncertainty budget is still declared.** `compile` now reports a
   *computed* propagated variance, but the three-way `Budget` is unchanged and
   provably distinct from it in the lithium instance.
6. **Multi-parameter identifiability is proved for affine gradients.** The rank
   obstruction is stated for families affine in the parameter; a nonlinear
   multi-parameter analogue (local injectivity of a Jacobian) is not proved.
7. **The nonlinear discrimination ranking is by guarantee only.** Proved not to
   be a ranking of regions, and there is still no cost model on measurements and
   no guarantee that the offered candidate list is itself well chosen.
8. **Repairs are still classified, not searched**, and receipts are still free
   fields (Stage-4 items 6 and 7, untouched).

## 7. What this does *not* claim

No physical theory-of-everything claim. No empirical claim about batteries,
thermal systems, safety or instrumentation. No statistical inference claim
beyond the identities proved: a posterior here is a normalised weighting of a
finite declared family under a declared likelihood, and no interval or region in
this development carries a coverage probability.
