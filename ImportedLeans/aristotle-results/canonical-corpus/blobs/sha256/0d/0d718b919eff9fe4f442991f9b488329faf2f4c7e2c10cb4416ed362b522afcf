# Stage 4 — continuous deterministic scientific inference

Stage 3 (`TOE_EXPERIMENT_CALCULUS.md`) gave an executable experiment calculus
over **finite** hypothesis families and **discrete-time** dynamics, with
set-valued prediction and risk envelopes and a first-class model-family failure.

This round builds the first four items of the Stage-4 priority ordering that do
not require probability:

| # | Item | Status this round |
|---|---|---|
| 1 | Continuous parameter envelopes | **built** — `Integration/Experiment/ParameterRegion.lean` |
| 1b | Best-next-measurement selection over a candidate set | **built** — `Integration/Experiment/BestReading.lean` |
| 2 | True derivative/Jacobian sensitivity | **built** — `Integration/Experiment/JacobianSensitivity.lean` |
| 3 | Continuous-time experiment dynamics | **built** — `Integration/Experiment/ContinuousDynamics.lean` |
| — | Anti-pattern guard (receipts) and typed repair frontier | **built** — `Integration/Experiment/ModelReceipts.lean` |
| — | Milestone instance and portability test | **built** — `Integration/Experiment/LithiumContinuous.lean`, `Integration/Experiment/ThermalRC.lean` |
| 4 | Probability / measurement-noise semantics | **built as a separate layer** — `Integration/Experiment/ProbabilityLayer.lean` |
| 5 | Likelihood / model weighting | **likelihood built; weighting/posterior deliberately not** (see §5b, §6) |
| 6 | Automated repair search | **typed, not searched** (see §6) |

Everything below is machine-checked Lean. The whole project builds
(`lake build`, 8 327 jobs, no errors); there is no `sorry`, no `admit`, no project `axiom`, no
`@[implemented_by]` and no `native_decide`. The axiom audit
(`Lean/Integration/AxiomAudit.lean`, 121 new `#print axioms` lines this round)
reports only `propext`, `Classical.choice` and `Quot.sound`. No Yang–Mills or
Navier–Stokes material was read, referenced or modified.

**Claim boundary.** The set-valued core (lanes 1–3, both instances, the receipts
and the repair frontier) contains no probability measure at all: a surviving
parameter region is a *possibility set*, not a confidence interval and not a
credible interval, and tolerances are declared rather than estimated. Lane 4
adds probability in a **separate file that nothing in the core imports**, so no
earlier result acquires a probabilistic reading; inside that file the three
notions are kept apart by three negative theorems (§5b). No claim is made about
lithium cells, thermal systems, safety, instrumentation, or any physical
theory.

---

## 1. The milestone

> Give the compiler a continuously parameterised dynamical experiment and
> measured time series, have it derive the surviving parameter region, propagate
> that region to a prediction and risk envelope, compute which additional
> measurement best contracts it, and correctly report when the entire parameter
> family is falsified.

`Integration/Experiment/LithiumContinuous.lean` does exactly this, on

```
ż = -θ,   z(0) = 0.9,   T = 10,   y = z,   θ ∈ [0.02, 0.04]
```

| Milestone step | Theorem | Content |
|---|---|---|
| dynamical model, not a curve fit | `predict_is_the_trajectory`, `trajectory_is_unique` | the family's predictions are the ODE's unique trajectories |
| surviving region from a measured series | `surviving_region_after_the_first_reading` | `Θ_E = [0.0275, 0.0325]`, exactly |
| the data did work | `first_reading_contracts`, `truth_survives_the_first_reading` | strict contraction of `[0.02, 0.04]`; the generating `θ* = 0.03` survives |
| region is reportable | `surviving_region_is_an_interval` | compact, order-connected, nonempty |
| prediction envelope | `endpoint_envelope_after_the_first_reading` | `[0.575, 0.625]` |
| risk envelope | `risk_unresolved_after_the_first_reading` | `{true, false}` — the safety question is still open |
| next measurement | `endpoint_reading_is_more_discriminating` | the steeper (endpoint) reading leaves the smaller region |
| and it answers the question | `risk_resolved_after_the_endpoint_reading` | the risk envelope collapses to `{false}` |
| repeating is not measuring | `repeating_the_early_reading_adds_nothing` | the region is unchanged |
| family failure | `family_is_falsified_by_the_low_reading` | no parameter explains the observation |
| failure is total | `falsified_family_predicts_nothing`, `falsification_is_permanent` | empty prediction *and* risk envelopes; no later data revives the family |
| certified sensitivity | `endpoint_sensitivity_is_certified` | `∂z(T)/∂θ = -10` is a derivative, not an annotation |

Every architectural conclusion is an instantiation of a generic theorem; the
instance file supplies data and arithmetic only.

## 2. Lane 1 — continuous parameter envelopes

`Integration/Experiment/ParameterRegion.lean`. Objects: `Reading` (time, value,
declared tolerance), `ParamFamily Θ` (prior region + predicted series),
`Compatible F E` (the surviving region `Θ_E`), `envelope`, `riskEnvelope`,
`FamilyFalsified`.

The Stage-3 architecture is reproduced with a *region* in place of a sublist:

| Theorem | Content |
|---|---|
| `compatible_subset_prior`, `compatible_nil`, `compatible_append` | evidence only removes; evidence combines by intersection |
| `more_evidence_no_larger` | **monotonicity**: more discriminating evidence ⇒ no larger admissible family |
| `envelope_antitone`, `riskEnvelope_antitone` | hence no wider prediction or risk envelope |
| `truth_survives`, `truth_survives_exact`, `truth_in_envelope`, `truth_in_riskEnvelope` | soundness |
| `coarser_tolerance_admits_more` | a loose instrument is paid for in width |
| `data_cannot_separate_identical_predictions` | the Stage-3 negative, in the continuum |
| `envelope_subsingleton_iff` | a point prediction is exactly agreement of survivors |
| `falsified_iff_forall_exists_bad_reading`, `falsified_is_permanent`, `falsified_envelope_empty`, `falsified_riskEnvelope_empty`, `falsified_no_survivor` | `refutation_is_total`, continuously |

New, with no finite analogue — the *shape* of the region:

| Theorem | Content |
|---|---|
| `compatible_isClosed`, `compatible_isClosed_of_continuousOn` | closed under continuous parameter dependence |
| `compatible_ordConnected`, `compatible_ordConnected_of_monotoneOn` | an interval under monotone dependence |
| `envelope_eq_Icc` | the envelope of a continuous consumer over a nonempty compact interval region **is** `[lo, hi]` |

and the quantitative discrimination result that replaces the counted Lane-5
sensor ranking:

| Theorem | Content |
|---|---|
| `affineConstraint_eq_Icc` | one reading of a parameter-affine family cuts an interval of half-width `tol/|slope|` |
| `steeper_reading_contracts_more`, `steeper_reading_leaves_smaller_region` | of two readings generated by the same true parameter at equal tolerance, the steeper one leaves the smaller region |

## 3. Lane 2 — sensitivities that are derivatives

`Integration/Experiment/JacobianSensitivity.lean` closes Stage-3 frontier item 1
*for the objects that carry the new certificate*, and keeps the three layers
apart.

* **Derivative.** `jacobian f x` is `fderiv` in coordinates.
  `jacobian_of_linear`, `jacobian_of_affine`, and `jacobian_comp` — the chain
  rule in matrix form, the derivative-level counterpart of `push_push`.
* **Sensitivity.** `CertifiedSensitivity` bundles a declared sensitivity vector
  with the proof that each entry is the matching partial derivative;
  `declared_is_the_partial_derivative`, `declared_unique`. The coulomb-counting
  pair `(∂Q/∂I, ∂Q/∂t) = (t, I)` — the one Stage 3 propagated as declared data —
  is certified as `chargeSensitivity`.
* **Propagation.** `RCov` is the real twin of the Stage-3 `Cov`, with symmetry
  and positive semidefiniteness proved preserved by `push`, and `propagate` uses
  the *certified* Jacobian.

The layers are proved not to collapse:

| Theorem | Content |
|---|---|
| `affine_variation_is_exactly_the_jacobian` | for an affine law, first-order propagation is exact |
| `derivative_zero_does_not_bound_variation` | a vanishing sensitivity is not insensitivity over a finite range (`t ↦ t²` at `0`) |
| `jacobian_does_not_determine_the_output_covariance` | the same Jacobian with two input covariances gives two output covariances: a sensitivity list is not an uncertainty statement |

Still declared, not certified: the `Law.sensitivity` fields of the Stage-3
quantity graph, and the budget entries of `ExperimentSpec`. The certificate now
exists; wiring it into every edge is a separate obligation (§6).

## 4. Lane 3 — continuous-time dynamics

`Integration/Experiment/ContinuousDynamics.lean`: `ContinuousSystem` (horizon,
initial state, protocol `u`, vector field `f(t,x,u)`), `IsTrajectory`, and four
consumers a static calculator cannot express — `endpoint`, `peak`, `integrated`,
`crossingTime`.

| Theorem | Content |
|---|---|
| `trajectory_unique` | under a state-Lipschitz field the trajectory — hence the prediction — is well defined |
| `affine_isTrajectory`, `affineSolution_unique` | the constant-rate solution and its uniqueness |
| `peak_mem_image`, `endpoint_le_peak` | the peak is attained and dominates the endpoint |
| `integrated_affine` | closed form for the integrated consumer |
| `crossing_exists`, `crossingTime_mem`, `crossingTime_is_first` | the threshold time exists, is attained, and is the *first* crossing |
| `parameterisedFamily`, `parameterised_predictions_are_well_defined` | the bridge: a θ-indexed dynamical family is a `ParamFamily`, so all of lane 1 applies to it |

## 5. The anti-pattern guard and the typed repair frontier

`Integration/Experiment/ModelReceipts.lean` blocks
"sophistication ⇒ authority" and "repair proposal = repair acceptance".

| Theorem | Content |
|---|---|
| `receipts_are_independent` | structure, parameter-evidence and validation receipts are free coordinates |
| `structure_does_not_determine_validation` | same structure, different validation record |
| `finer_structure_does_not_imply_better_prediction` | a strictly more mechanistic model with a strictly worse worst-case error |
| `better_prediction_does_not_imply_finer_structure` | and the converse fails too |
| `adding_parameters_without_evidence_is_underdetermined` | the cost of new mechanism, made explicit |
| `RepairKind` | the six declared repair classes |
| `accepted_repair_is_refutable` | acceptance always exhibits an observation that would have killed the repair |
| `unfalsifiable_repair_admits_no_acceptance`, `proposal_is_not_acceptance` | a model class that fits anything explains the anomaly and can never be accepted |
| `repair_does_not_rehabilitate_the_old_family` | the falsified family stays falsified |

## 5a. Lane 1b — choosing the next measurement

`Integration/Experiment/BestReading.lean` upgrades the pairwise comparison
`steeper_reading_contracts_more` into a selection over a finite candidate list.

| Theorem | Content |
|---|---|
| `steepest` | selects a candidate of maximal declared parameter sensitivity `\|slope t\|` |
| `steepest_mem` | the selection is one of the offered candidates — it never invents a measurement |
| `le_steepest`, `steepest_maximal` | the selection attains the maximal sensitivity over the list |
| `steepest_contracts_most` | the region surviving the selection is contained in the region surviving *any* candidate |
| `steepest_envelope_smallest`, `steepest_riskEnvelope_smallest` | hence the narrowest prediction and risk envelopes offered |
| `steepest_of_flat_candidates_is_no_better` | the negative: equal sensitivities make the choice vacuous |

Instantiated in the milestone over three candidates (`t = 4, 7, 10`):
`best_next_measurement_is_the_endpoint`,
`selected_measurement_contracts_most`,
`selected_measurement_gives_the_narrowest_envelope`.

## 5b. Lane 4 — the separate probability layer

`Integration/Experiment/ProbabilityLayer.lean` adds probability *beside* the
set-valued core rather than inside it (`possible worlds + measure`). It is
imported by no other module in the corpus.

| Theorem / definition | Content |
|---|---|
| `FinPMF` | a finite probability mass function: nonnegative masses summing to one |
| `expect`, `variance`, `cov` | `E[X]`, `Var(X)`, `Cov(X,Y)` for `X : Ω → ℝ` |
| `expect_add`, `expect_const_mul`, `expect_const`, `expect_mono`, `expect_nonneg` | linearity and monotonicity |
| `variance_eq_expect_sq_sub`, `variance_nonneg`, `variance_const` | `Var X = E[X²] − (E X)²`, nonnegativity |
| `cov_comm`, `cov_self`, `variance_add` | symmetry, `Cov(X,X) = Var X`, `Var(X+Y) = Var X + Var Y + 2Cov(X,Y)` |
| `cov_sq_le_variance_mul_variance` | Cauchy–Schwarz |
| `MeasurementModel`, `likelihood` | `Y_obs = h(x) + ε`, `ε ~ P_ε`; `L(h ∣ y) = P(Y = y ∣ h)` |
| `likelihood_nonneg`, `likelihood_le_one`, `likelihood_pos_iff` | basic semantics of the likelihood |
| `likelihood_pos_imp_tolerance` | with noise supported in `[-ε, ε]`: positive likelihood **⇒** tolerance-compatible — the Stage-3 layer survives as a coarsening |
| `tolerance_does_not_imply_positive_likelihood`, `tolerance_cannot_rank_hypotheses` | the inclusion is strict, and tolerance cannot order hypotheses: `tolerance compatibility ⊊ likelihood comparison` |
| `measure_is_not_determined_by_the_possible_values` | no function of the set of attainable values returns the mean: an envelope determines no probabilistic summary |
| `credible_can_be_strictly_inside_the_envelope` | a credible set can be a proper subset of the prediction envelope |
| `coverage_is_not_a_property_of_the_reported_interval` | two procedures reporting the same interval can have different coverage, so a confidence level is a property of the procedure |

The last three are the formal content of
`prediction envelope ≠ confidence interval ≠ credible interval`.

## 6. Honest frontier — exact remaining obligations

1. **Probability stops at likelihood.** There is no prior, no posterior, no
   Bayes rule, no model weighting, no asymptotics and no continuous
   distribution: `FinPMF` is finite and `MeasurementModel` is finitely
   supported. Nothing connects the likelihood to the parameter regions of lane 1
   (there is no probabilistic analogue of `Compatible`), and `massOf` /
   `coverage` are definitions used only in the three separation theorems, not a
   developed theory of credible sets or confidence procedures.
2. **Tolerances are declared.** `Reading.tol` is an input. Nothing estimates an
   instrument model from repeated measurements; `likelihood_pos_imp_tolerance`
   relates a *declared* bound on the noise support to a *declared* tolerance,
   and does not derive either from data.
3. **Certification is opt-in.** `CertifiedSensitivity` exists and two laws use
   it (`chargeSensitivity`, `endpointSensitivity`). The Stage-3 quantity-graph
   edges still carry uncertified rational sensitivity lists, and `compile` still
   does not invoke `Cov.push`/`RCov.push`. Obligation: a certified field on
   `Law`, and a compiler field carrying the propagated covariance.
4. **Existence is proved only for bounded, globally Lipschitz fields.**
   `trajectory_exists` / `trajectory_exists_unique` now invoke Picard–Lindelöf,
   and `constantRate_trajectory_exists` shows the hypotheses are satisfiable;
   but the bound `‖f t x‖ ≤ L` is global in the state, so fields with unbounded
   growth are not covered, and there is still no discretisation-error bound
   relating the continuous lane to the Stage-3 discrete one.
5. **The next-measurement optimisation is affine-only.** `steepest`
   (`Integration/Experiment/BestReading.lean`) now selects from an arbitrary
   finite candidate list and is proved optimal over that list
   (`steepest_contracts_most`, and the milestone's
   `selected_measurement_contracts_most` over three candidates), but only for a
   family *affine* in the parameter, with a common generating parameter and a
   common declared tolerance. There is still no analogue for nonlinear parameter
   dependence (the `ThermalRC` instance is not covered), no cost model on
   measurements, and no guarantee that the offered candidate list is itself
   well-chosen.
6. **Repairs are still classified, not searched.** `RepairKind` and
   `RepairProposal` type the frontier and `RepairAcceptance` gives it teeth, but
   no generator produces candidate repairs and nothing proves a candidate set
   exhaustive (Stage-4 item 6).
7. **Receipts are free fields.** Nothing checks that a `ModelStructureReceipt`
   describes the Lean model it is attached to — the same caveat Stage 3 recorded
   for `assumptions` and `provenance`.
8. **Multi-parameter regions are not developed.** Both instances have a single
   real parameter. The generic lane-1 theorems are stated for an arbitrary
   parameter type, but the interval-shape results (`compatible_ordConnected`,
   `envelope_eq_Icc`) are one-dimensional.

## 7. Dependency / provenance map

```
Integration.Experiment.Compiler            (Stage 3)
        └── Experiment.ModelSelection      (Stage 3)
                └── Experiment.ParameterRegion        (new: Θ_E, envelopes, FamilyFalsified)
                        ├── Experiment.ContinuousDynamics  (new: ODEs, consumers, bridge)
                        │       ├── Experiment.LithiumContinuous (new: the milestone)
                        │       └── Experiment.ThermalRC         (new: portability)
                        ├── Experiment.ModelReceipts       (new: receipts, repair frontier)
                        └── Experiment.BestReading         (new: measurement selection)
                                └── Experiment.LithiumContinuous

Integration.Experiment.ProbabilityLayer    (new: FinPMF, moments, likelihood)
        — standalone: it imports no Stage-3/Stage-4 module and none imports it;
          only Integration.lean and the axiom audit pull it in.

Integration.Experiment.Uncertainty         (Stage 3)
        └── Experiment.JacobianSensitivity (new: certified derivatives, RCov)
                └── Experiment.LithiumContinuous
```

No existing module was rewritten. `Lean/Integration.lean` and
`Lean/Integration/AxiomAudit.lean` gained imports, a module-doc entry and audit
lines.  One build repair was needed: the `AgdaMirror` library glob in
`lakefile.toml` was `AgdaMirror.*`, which pulls in the root aggregate
`Lean/AgdaMirror.lean` — that aggregate imports the Yang–Mills mirror excluded
from this cutset, so a whole-project `lake build` failed before any Lean file
was elaborated.  It is restored to `AgdaMirror.+` (submodules only), exactly as
the comment beside it already documents; no Yang–Mills file was read or
added.

## 8. What this does *not* claim

No physical theory-of-everything claim. No empirical claim about batteries,
thermal systems, safety or instrumentation. No statistical inference claim: the
probability layer proves moment identities and measurement-model semantics only,
and no interval produced by the set-valued core is a confidence or credible
interval — no parameter region carries a coverage probability. The
numbers in the two instance files are declared constants chosen to exercise the
calculus.
