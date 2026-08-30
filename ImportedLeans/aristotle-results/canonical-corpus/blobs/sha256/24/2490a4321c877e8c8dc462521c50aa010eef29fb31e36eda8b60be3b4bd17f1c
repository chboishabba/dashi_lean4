# The decision / intervention / aggregation tranche: rows 45–60

This is the companion report for the second intake round of this session.  The
first round (`TOE_PHYSICAL_BIOLOGY_TRANCHE.md`, rows 25–44) consumed the
physical-biology and product-state material.  This one takes the remaining
Level-II programme: the mathematics that several unrelated lanes keep rebuilding
under domain names — **selective decisions, interventions and responses,
multi-objective outcomes, reachability under a declared action language,
marginalisation versus interaction, and completeness relative to a declared
carrier**.

Everything below marked *proved* is elaborated by `lake build` (full build:
8 282 jobs, zero errors) and there is no `sorry` in any build-target file.
Every new result is listed in `Lean/Integration/AxiomAudit.lean`; all 530
audited results there depend only on `propext`, `Classical.choice` and
`Quot.sound`.  **No Agda typechecker is available in this environment**, so no
Agda module is claimed to compile, and every registry row is proved to say so
(`SewingRegistry.no_row_claims_agda_typechecked`).

---

## 1. What was added

| Lean module | what it owns |
|---|---|
| `Lean/Integration/SelectiveDecision.lean` | three-valued verdicts with abstention, the resolution map, and what compiling abstention away destroys |
| `Lean/Integration/CounterfactualEffect.lean` | the intervention layer: response, homogeneity, label-vs-effect, and observation-vs-intervention |
| `Lean/Integration/ParetoOutcome.lean` | multi-objective dominance as a strict order, incomparability, and what a scalar summary invents |
| `Lean/Integration/ReachabilityBarrier.lean` | reachability relative to a declared action language, and the only general route to unreachability |
| `Lean/Integration/Marginalisation.lean` | marginal contrasts: weight-invariant iff separable, and the finite-count reversal |
| `Lean/Integration/DeclaredCarrier.lean` | exhaustion, verification and observer sufficiency, all relative to a declared carrier |

---

## 2. Dependency and provenance map

`(mirror)` means the Lean text transcribes Agda text; `(about)` means the Lean
text is a development *about* a surface it does not transcribe.

```
Agda/DASHI/Control/LearnedAbstentionBoundary.agda             (mirror)
    │  Direction, Action, Decision, compileDecision, ExecutionSemantics,
    │  abstentionCompilesToHold, holdPreservesExposure
    └─▶ Integration.SelectiveDecision
            ├─▶ Verdict / Resolution / resolve          (the generic owner)
            └─▶ Integration.CoordinateSufficiency.Determines
        ▲
        │ supplies the two threshold numerals and the clamp
Agda/DASHI/Physics/SeverityMapping.agda                       (about)
        safeThresholdᵣ = 3, brokenThresholdᵣ = 4, clamp9

Agda/DASHI/Education/EarlyLearningCounterfactualHeterogeneityExact.agda (mirror)
    │  SituatedExposure, interventionProjection,
    │  counterfactualRelativeEffect, observedGroupProjection
    └─▶ Integration.CounterfactualEffect
            ├─▶ Response / Homogeneous / contrast       (the generic owner)
            └─▶ Integration.CoordinateSufficiency.Determines
                    └─▶ Agda/DASHI/Core/IntersectionalNonFactorability.agda
                        (identified with `Determines` in the previous round by
                         Integration.ContextIndexedRole.factorsThrough_iff_determines)

Agda/DASHI/Environment/ParetoPlanning.agda                    (mirror)
    │  Direction, ObjectiveScore, scoreNoWorse, scoreStrictlyBetter,
    │  VectorNoWorse, SomeStrictlyBetter, Dominates,
    │  SelectionSeparationBoundary (five free Bools)
    └─▶ Integration.ParetoOutcome
            └─▶ Integration.CoordinateSufficiency (aggregation)

Agda/DASHI/Core/AdmissibleReachability.agda                   (mirror)
    │  Reachable, Executes, executesImpliesReachable
    │  (over Agda/DASHI/Core/TypedDependencyCore.agda's
    │   DependentActionSystem / AdmissibleAction)
    └─▶ Integration.ReachabilityBarrier

Integration.CoordinateSufficiency.Separable                   (about)
    └─▶ Integration.Marginalisation
            (marginal contrast, weight invariance, the pooled reversal)

Agda/DASHI/Culture/Cuisine/CuisineKnowledgeSourceAtlas.agda    (about)
Agda/DASHI/Governance/RevolutionarySourceAtlas.agda            (about)
    │  prose disclaimers of exhaustive coverage
    └─▶ Integration.DeclaredCarrier
            └─▶ Integration.CoordinateSufficiency.Determines
```

---

## 3. The rows

| # | corpus surface | TOE owner | class | Lean witness |
|---:|---|---|---|---|
| 45 | `LearnedAbstentionBoundary.compileDecision` | `SelectiveDecision` | negative | `action_does_not_determine_direction` |
| 46 | …its `Action.flatten` | `SelectiveDecision` | negative | `compile_never_flattens` |
| 47 | `SeverityMapping` threshold pair | `SelectiveDecision.gated` | negative | `corpus_thresholds_admit_no_abstention` |
| 48 | `SeverityMapping.clamp9` | `CoordinateSufficiency` (aggregation) | negative | `clamp9_not_determines` |
| 49 | `…CounterfactualHeterogeneityExact.interventionProjection` | `CounterfactualEffect` | negative | `intervention_label_cannot_determine_effect` |
| 50 | …its `SituatedExposure` | `CoordinateSufficiency` (essential coordinates) | negative | `effect_essential_set` |
| 51 | …its `observedGroupProjection` | `CoordinateSufficiency.Determines` | negative | `observed_group_cannot_determine_individual_effect` |
| 52 | `ParetoPlanning.Dominates` | `ParetoOutcome` | negative | `incomparable_pair` |
| 53 | weighted totals of its objectives | `CoordinateSufficiency` (aggregation) | negative | `total_not_determines_outcome` |
| 54 | `ParetoPlanning.SelectionSeparationBoundary` | `Levels.Socket` | **open socket** | `separation_flags_underdetermined` |
| 55 | `AdmissibleReachability.Reachable` | `ReachabilityBarrier` | negative | `barrier_is_language_relative` |
| 56 | `AdmissibleReachability.Executes` | `ReachabilityBarrier` (monotonicity) | candidate bridge | `reachable_of_weaker_precondition` |
| 57 | marginal readings of two-coordinate consumers | `CoordinateSufficiency.Separable` | negative | `parityQ_not_separable` |
| 58 | pooled comparisons over strata | `Marginalisation` | negative | `pooled_reversal` |
| 59 | the atlases' coverage disclaimers | `DeclaredCarrier` | negative | `sample_not_exhaustive_ambient` |
| 60 | model-internal completeness claims | `DeclaredCarrier.DeterminesOn` | negative | `determinesOn_not_determines` |

Registry census, proved by `rfl` in `SewingRegistry.kinds_exercised`: **2** exact
instances, **2** approximate, **1** finite shadow, **1** structural analogue,
**4** candidate bridges, **42** negatives, **8** open sockets — **60 rows**
(`registry_length`), of which **50** are refutations or sockets
(`negatives_and_sockets_dominate`).

---

## 4. The six owners, and why each is generic

### 4.1 Selective decision

A verdict is `reject / abstain / accept`; a `Resolution` compiles it into an
action.  The cost is stated once:
`resolve_not_injective_of_default_collision` — as soon as the abstention
default coincides with a determinate action, the executed action no longer
determines the verdict.

The corpus's control lane is an executable instance.  Its own three lemmas are
re-proved, and three statements it does not make are added:
`compile_never_flattens` (closing exposure is not in the image, which the module
asserts only in prose), `action_does_not_determine_direction`, and
`exposure_does_not_determine_abstention` (execution erases abstention, because
abstaining is observationally the identity).

The sharpest find is `direction_essential_only_when_not_abstaining`: the
direction coordinate is essential to the action when the abstain flag is
`false` and inessential when it is `true`.  **Coordinate essentiality is itself
context-dependent** — which is the shape `Integration.ContextIndexedRole` owns,
now with a second, independent witness.

For the threshold form, `abstention_is_reachable_iff` says the abstention region
is non-empty exactly when the thresholds leave a gap.  The corpus's own numerals
(`safeThresholdᵣ = 3`, `brokenThresholdᵣ = 4`) are adjacent, so
`corpus_thresholds_admit_no_abstention`: that lane's three-valued vocabulary
carries a two-valued rule.

### 4.2 Counterfactual effect

`Response`, `Homogeneous` and `contrast` are the whole apparatus.  Two theorems
carry the weight: `contrast_not_homogeneous` (the action does not name a number,
it names a function of the state) and `level_not_determines_post` (two states
the observation identifies are separated by the action).
`intervention_can_reverse_ordering` sharpens the second: the action can reverse
the observed order, so even a monotone reading of the observation transfers
nothing across it.

The corpus instance is re-proved and *extended* with its positive half:
`counterfactual_determines_effect` shows the hidden coordinate is sufficient, so
`effect_essential_set` identifies it as the unique essential coordinate.  The
corpus module records only the negative.

### 4.3 Pareto outcome

The Agda module defines the dominance relation and proves nothing about it.
Here it is a strict order (`dominates_irrefl`, `dominates_asymm`,
`dominates_trans`), genuinely partial (`incomparable_pair`), and
`noWorse_direction` records a consequence of its own `⊥` clauses that the module
does not state: comparability forces agreement of direction, so the relation is
a preorder on each direction class and not on all scores.

`scalarisation_invents_order` is the result worth keeping: a scalar total
strictly orders a pair the dominance relation leaves incomparable **in both
directions**.  A weighted total does not refine the Pareto order; it replaces it,
and nothing in the scalar records that a replacement occurred.

### 4.4 Reachability barrier

`not_reachable_of_invariant` is the only general route to unreachability, and it
is explicitly relative to one system.  `reachable_of_weaker_precondition` shows
enlarging the action language can only add reachable pairs, and
`barrier_is_language_relative` exhibits a target unreachable under one language
(by a parity invariant) and reachable under an extension of it.  So *currently
unreachable* and *unreachable after refinement* are different statements and
only the first is ever established.

### 4.5 Marginalisation

The complementary pair:

* `separable_contrast_weight_invariant` — for a separable consumer the
  coordinate contrast is the same under every convex weighting of the other
  coordinate, so marginalising loses nothing about it;
* `interaction_contrast_can_reverse` — for an interacting one the contrast can
  change sign with the weighting;
* `reversal_implies_interaction` — hence a reversal between two marginal
  analyses is a *proof of interaction*, not a paradox.

`pooled_reversal` gives the finite-count version with explicit integers (equal
group totals, so the reversal is not an artefact of unequal sizes),
`pooling_weights_differ` names the mechanism, and `common_weights_no_reversal`
proves no reversal is possible once the weightings agree.

### 4.6 Declared carrier

`universal_of_exhaustive` is the transfer theorem: checking a property on an
enumeration is a universal claim exactly when the enumeration is exhaustive *of
the intended carrier*, and it cannot be applied without naming the carrier.
`verified_not_universal` shows the failure without that hypothesis, and
`determinesOn_not_determines` gives the observer form: an observation sufficient
for a consumer on the declared carrier can fail on a larger one.  A model
complete in its own chart licenses nothing about the exterior.

---

## 5. Frontier: exactly what remains open

### 5.1 Obligations stated but not discharged

* **Row 54 (Pareto boundary).**  Five free `Bool`s.  In particular the field
  asserting that *weights do not erase reported tradeoffs* is set to `true` in
  the module's canonical inhabitant, while `scalarisation_invents_order` shows
  what a weighted total actually does to a tradeoff.  Discharging this row needs
  an actual weighting map and an actual preservation statement; the corpus has
  neither.
* **Row 56 (candidate bridge).**  The hypothesis is the language inclusion, and
  each lane must supply it for its own pair of systems.  It is discharged here
  for the counter witness (`coarse_subset_full`); a lane whose extended system
  changes the *postconditions* rather than only the preconditions would need the
  second hypothesis too.
* **Rows 47 and 48.**  `SeverityMapping` declares two numerals and a clamp but
  no decision procedure.  The gated rule is the Lean reading of a safe/broken
  threshold pair and is not claimed to be the module's own; discharging these
  rows properly needs the module to define the rule it names.

### 5.2 Places where the corpus names a theorem it does not prove

* `LearnedAbstentionBoundary` says in prose that closing exposure "cannot be
  produced by `compileDecision`" and proves only that the risk compiler produces
  it.  The non-surjectivity itself is `compile_never_flattens`.
* `ParetoPlanning` defines `Dominates`, `NonDominatedIn` and `FiniteParetoResult`
  and proves no order property of any of them; the four order facts here are new.
* `AdmissibleReachability` proves `executesImpliesReachable` and never states
  transitivity, monotonicity in the action language, or any unreachability
  criterion.

### 5.3 A flagged reading, not a claim

`EarlyLearningCounterfactualHeterogeneityExact.agda` writes the two clauses of
`counterfactualRelativeEffect` against `higherCounterfactualExposure` and
`lowerCounterfactualExposure`, which are **defined names in that module, not
constructors**.  The Lean mirror therefore defines the effect by constructor
patterns on the hidden coordinate, which is the reading the module's header and
its own downstream lemmas require.  No Agda checker is available here, so
nothing is asserted about whether the Agda text elaborates as written; this is
recorded so that a round with an Agda toolchain can settle it.  The same caveat
is carried in the claim boundary of row 49.

### 5.4 Boundaries of what was proved

* Every carrier in this tranche is finite or numeric: three- and four-element
  label types, `Bool`, `Fin 2`, `ℕ`, `ℚ`.  Nothing here is a claim about
  trading, control, monitoring, physics, education, childcare, planning,
  environment, governance or any population.
* `Marginalisation` contains **no probability space, sample, estimator or
  convergence statement**.  Its results are deterministic facts about weighted
  averages.  The complementary deterministic statement about sample size is
  `CoordinateSufficiency.no_sample_statistic_separates`, proved in the previous
  tranche; neither is a claim about estimation error.
* The explicit integers in `pooled_reversal` are a witness, not data.
* `ParetoOutcome` drops the `String` fields of the Agda `ObjectiveScore` and the
  two admissibility fields of `Dominates`; those carry no order content, and the
  row's claim boundary says so.
* No Yang–Mills or Navier–Stokes material was read, written or cited.

### 5.5 Still not attempted

The lane-scale `Bool` census (16 004 pinned and 7 831 free fields recorded in
`CORPUS_INVENTORY.md`) remains deliberately un-automated, for the same reason as
last round: turning it into registry rows would grow a status database rather
than sew mathematics.  Six of the eight open sockets in the registry are exactly
the places where that census would have to start.
