# The executable experiment calculus (Stage 3)

This round builds a small, end-to-end scientific execution path over the
existing prediction/evidence machinery:

```
experimental specification → typed quantities → model selection over candidate
hypotheses → prediction envelope → uncertainty → risk → testable output
```

and runs it on two unrelated domains: a lithium cell under a galvanostatic hold,
and a heated slab with a hidden interior node.

Everything below is machine-checked Lean. The full project builds
(`lake build`, 8 319 jobs, no errors); there is no `sorry`, no `admit`, no
project `axiom`, no `@[implemented_by]` and no `native_decide`; the axiom audit
(1 125 `#print axioms` checks, of which 88 are new this round) reports only
`propext`, `Classical.choice` and `Quot.sound`. No Yang–Mills or Navier–Stokes
material was read, referenced or modified.

**Claim boundary.** Nothing here is a claim about real lithium cells, real
slabs, or any physical system. `CellState` is four rationals, `SlabState` is
three, an "instrument" is a rational-valued function of them, and a hazard
threshold is a declared rational. The theorems are about those objects. The two
domain files were chosen to test whether the calculus survives a change of
domain, and that portability — not any number in them — is the result.

---

## 1. What was built, lane by lane

| Lane | Module | Content |
|---|---|---|
| 1a | `Integration/Experiment/Dimension.lean` | `Dim` (six integer exponents), `Quantity`, total multiplication, **partial** addition; `three_volt_plus_two_coulomb_rejected`; `dimensional_consistency_does_not_determine_the_law` |
| 1b | `Integration/Experiment/QuantityGraph.lean` | `Law` edges carrying arity, provenance, assumptions, validity domain, sensitivities and epistemic kind; typed application; composition; the dimensional-identity/constitutive-model separation |
| 2 | `Integration/Experiment/Uncertainty.lean` | `Cov` (symmetric, PSD), `Cov.push` = `J Σ Jᵀ` with both properties **proved preserved**; the scalar formula derived; the three-way `Budget`; `Coverage` and intervals |
| 3 | `Integration/Experiment/Protocol.lean` | `Dynamics`, `trajectory`, `Protocol`, the pulse and its closed forms, `ExperimentRun`, and the bridge `trajectory_reachableIn` to the existing language-indexed reachability |
| 4 | `Integration/Experiment/Risk.lean` | `Hazard`, risk `profile`, risk envelope = image of the prediction fibre, `instrumentation_insufficient_for_the_risk_question`, the `Verdict` dichotomy |
| 5 | `Integration/Experiment/MeasurementValue.lean` | `ambiguity` (counted collisions), `ambiguity_eq_zero_iff_determines`, `ambiguity_join_le`, `bestSensor` and its minimality/adequacy theorems, plus two honest negatives |
| 6 | `Integration/Experiment/FailureLocalisation.lean` | `FailureClass`, `Derivation` with a real soundness field, `falsification_localises_to_a_dependency`, non-uniqueness of localisation, repair discrimination, and "a repair is not a promotion" |
| 3+ | `Integration/Experiment/ModelSelection.lean` | `InstrumentModel` (a declared comparison tolerance, not a distribution), `traceAgree`, data-driven `dataAdmissible`/`refine`; `refine_shrinks`, `truth_survives_refinement`, `truth_in_refined_envelope`, `refined_envelope_subset`, and the negatives `data_cannot_separate_identical_traces`, `coarser_instrument_admits_more`, `refutation_is_total`, `surviving_pair_is_not_a_selection` |
| — | `Integration/Experiment/Compiler.lean` | `ExperimentSpec → ExperimentPrediction` and its guarantees |
| — | `Integration/Experiment/Lithium.lean` | domain instance 1 (data only) |
| — | `Integration/Experiment/ThermalDiffusion.lean` | domain instance 2 (data only) |

## 2. The compiler

`ExperimentSpec H State Control Obs` carries: initial state per candidate
hypothesis, controls (protocol), dynamics per hypothesis, instrumentation,
admissibility (validity region and prior evidence), a nominal hypothesis,
prediction consumers, hazards, the uncertainty budget, the coverage rule, the
inherited assumptions, declared sensitivities, the support cone, and candidate
sensors.

`compile` returns: trajectory, prediction envelope per consumer, reported
intervals, risk envelope, assumptions, sensitivities, support cone, computed
epistemic status, the uncertainty budget (still three fields), and the
recommended next measurement.

Proved about it:

| Theorem | Content |
|---|---|
| `truth_in_envelope`, `truth_in_risk_envelope` | soundness: an admissible truth is inside the reported envelopes |
| `envelope_is_a_point_iff_determined` | a point prediction is exactly determination by the admissible set |
| `risk_resolved_iff_no_ambiguity` | the risk verdict is the counted collision criterion |
| `recommendation_is_minimal` | the recommendation minimises residual ambiguity among declared candidates |
| `recommendation_resolves_iff_possible` | it resolves the question exactly when some candidate does |
| `status_is_the_computed_one` | the tier comes from the support cone, not from the specification |
| `compile_keeps_the_budget`, `compile_keeps_the_assumptions` | the budget is not summed away and the assumptions travel |
| `refine_shrinks`, `refined_envelope_subset`, `truth_in_refined_envelope` | selecting on data can only tighten the envelope, and still covers an admissible truth |

## 3. The lithium test (Stage-3 acceptance criterion)

Two candidate cells — a low-resistance cell at higher state of charge and a
high-resistance cell at lower state of charge — are chosen so that the
voltage-and-current trace is identical for the whole hold.

| Output | Theorem |
|---|---|
| identical predicted traces | `traces_agree` |
| different thermal risk | `risks_differ` |
| instrumentation verdict | `voltage_and_current_are_insufficient_for_the_thermal_risk` |
| prediction envelope | `temperature_envelope_is_not_a_point` (`{310, 320}`) |
| uncertainty budget | `budget_is_not_one_number` (dominant quantified source = parameter; model discrepancy **unquantified**) |
| interval vs envelope | `reported_interval_does_not_cover_the_envelope` — the quantified interval misses the second admissible prediction; the missing width is the unquantified discrepancy |
| next measurement | `temperature_sensor_resolves`, `voltage_repeat_does_not_resolve`, `recommendation_resolves_the_risk_question` |
| typed-quantity agreement | `charge_delivered_is_typed`; `amount_needs_the_assumptions` |
| epistemic status | `epistemic_status_is_model_conditional`, `analogy_step_weakens_the_status` |
| falsification loop | `threeFifty_outside_envelope`, `observing_350_localises`, `two_repairs_of_the_overheat` |
| data-driven selection | `observation_keeps_the_truth` (the true cell survives selection on its own trace), `data_does_not_select` (no observation separates the pair), `observing_the_trace_leaves_the_pair` (so the derived admissible set is still not a point, and the answer is a new sensor rather than more data) |

The pipeline was **not** special-cased: the lithium file supplies data and
domain arithmetic; every architectural conclusion is an instantiation of a
generic theorem.

## 4. The portability test

`ThermalDiffusion` is a different kind of problem — a latent *state* rather than
a latent *parameter*, a scalar observation rather than a pair, a different
hazard and a different winning sensor (an interior thermocouple). It reuses the
same `ExperimentSpec`, `compile`, `Hazard`, `Sensor`, `Resolves` and `Budget`
without a single change to any lane file. `same_calculus_two_domains` states the
two instances' end-to-end conclusions side by side.

## 5. Dependency / provenance map

```
Integration.CoordinateSufficiency        (existing: Determines)
        └── Integration.FactorisationCollision   (existing: Collision owner)
                └── Integration.ClaimTransportGeometry (existing)
                        └── Integration.PredictionEnvelope (existing: Pred)
                                └── Integration.PredictionStatus (existing: Tier, Step, chain)

Integration.Experiment.Dimension            (new, Mathlib only)
        └── Experiment.QuantityGraph        (new; uses Collision)
                └── Experiment.Uncertainty  (new; uses Mathlib Matrix, Collision, Pred)
                        └── Experiment.Protocol (new; uses LanguageReachability)
                                └── Experiment.Risk (new; uses Pred, Collision)
                                        └── Experiment.MeasurementValue (new)
                                                └── Experiment.FailureLocalisation (new; uses PredictionStatus)
                                                        └── Experiment.Compiler (new)
                                                                └── Experiment.ModelSelection (new)
                                                                ├── Experiment.Lithium (new)
                                                                └── Experiment.ThermalDiffusion (new)
```

No existing module was rewritten. `Lean/Integration.lean` and
`Lean/Integration/AxiomAudit.lean` gained imports and audit lines; the
`lakefile.toml` `AgdaMirror` glob was restored to `AgdaMirror.+` (a regression
that broke the whole-project build, since the root aggregate imports the
excluded Yang–Mills mirror).

## 6. Honest frontier — exact remaining obligations

1. **First-order propagation is not connected to the graph's `sensitivity`
   fields.** `Law.sensitivity` is declared data; nothing yet proves that a law's
   sensitivity list *is* the Jacobian of its `eval`, and `Cov.push` is not
   invoked by `compile`. Obligation: a theorem
   `sensitivity_is_the_derivative` for each edge (needs a derivative notion over
   `ℚ`, or a move to `ℝ`), and a compiler field carrying the propagated
   covariance.
2. **Coverage rules are abstract.** `Coverage` is any monotone nonnegative
   half-width function; no distributional statement (e.g. a 95% interval) is
   made or provable here, since no probability measure is in play. Obligation:
   either a probabilistic layer or an explicit statement that intervals are
   bookkeeping only.
3. **Model selection is now data-driven, but not probabilistic.**
   `Integration.Experiment.ModelSelection` derives `admissible` from an observed
   trace under a declared instrument tolerance and proves the derived set
   shrinks the envelope and still contains the truth
   (`truth_in_refined_envelope`), that identical predicted traces are never
   separated by data (`data_cannot_separate_identical_traces` — instantiated on
   the lithium cell as `data_does_not_select`), and that an observation matching
   no candidate empties the family (`refutation_is_total`). What remains: there
   is still no likelihood, no fitting and no posterior weight, so a hypothesis
   is either kept or dropped; the instrument tolerance is declared rather than
   estimated; and continuous parameter families are outside the enumeration.
   Obligation: a weighted selection with a proved coverage property, which needs
   the probabilistic layer of obligation (2).
4. **`assumptions`, `provenance` and `sensitivities` are strings/rationals.**
   They travel with the prediction and are proved to travel, but nothing checks
   that they *describe* the edge. This is the same free-field caveat the corpus
   records elsewhere.
5. **The uncertainty budget is not populated from the graph.** In both instances
   the budget is declared in the specification; deriving `measurement` and
   `parameter` variances from the edges' sensitivities is obligation (1)'s
   consequence.
6. **Repairs are hypotheses, not searches.** `Repair` is a record supplied by
   the analyst; there is no generator of repair candidates and no proof that a
   generated set is exhaustive. `failure_does_not_localise_uniquely` shows why
   exhaustiveness would be needed for any stronger claim.
7. **Continuous dynamics are absent.** All dynamics here are discrete-time maps
   over `ℚ`; no differential equation, no discretisation error bound. A
   `modelDiscrepancy` entry is the placeholder for exactly that gap, and in both
   instances it is honestly `none`.
8. **The sensor ranking is by counted ambiguity on a finite hypothesis family.**
   It is exact for that family and says nothing about hypotheses outside it.

## 7. What this does *not* claim

No physical theory-of-everything claim. No empirical claim about batteries,
thermal systems, safety or instrumentation. No claim that the lithium or thermal
numbers describe any real device. No probabilistic claim: "uncertainty" here is
a rational bookkeeping entry with a monotone reporting rule, not a variance of a
random variable in a measure-theoretic sense.
