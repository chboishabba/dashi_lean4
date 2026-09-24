# TOE Level-II discharge and stress-test tranche

Registry rows **70–81**.  This tranche did not add an owner.  It took the four
Level-II owners as frozen and asked, of real corpus surfaces, whether they can
be welded exactly, welded under an explicit hypothesis, refuted, or left open.

Owners treated as frozen:

| owner | file |
| --- | --- |
| `Integration.RealisationAdequacy` | `Lean/Integration/RealisationAdequacy.lean` |
| `Integration.FactorisationCollision` | `Lean/Integration/FactorisationCollision.lean` |
| `Integration.SeparabilityContrast` | `Lean/Integration/SeparabilityContrast.lean` |
| `Integration.LanguageReachability` | `Lean/Integration/LanguageReachability.lean` |

One *new* module is generic rather than domain-shaped and is a composition
result about the owners, not a fifth owner: `Integration.PipelineAdequacy`.

**Standing caveats.**  No Agda typechecker is available in this environment, so
no Agda module is claimed to have been rechecked; every Lean mirror is Lean text
transcribing Agda text, and `no_row_claims_agda_typechecked` proves that no
registry row asserts otherwise.  No Yang–Mills or Navier–Stokes material is
read, imported or referenced.  Every carrier below is a finite label type, a
`Bool`-valued record, `ℕ`, `ℚ` or `ℝ`; nothing here is a physical, empirical,
educational, institutional or theory-of-everything claim.

---

## 1. What was added

| file | contents |
| --- | --- |
| `Lean/Integration/PipelineAdequacy.lean` | multi-stage pipelines; collision propagation; the repair dichotomy |
| `Lean/AgdaMirror/NonFactorabilityKernels.lean` | mirrors of the two generic Agda collision kernels and four consumers |
| `Lean/AgdaMirror/FibreAveraging.lean` | mirror of the corpus's normalised fibre-averaging pair |
| `Lean/AgdaMirror/InteractionTables.lean` | mirrors of three corpus two-coordinate value tables |
| `Lean/Integration/SourceExactWelds.lean` | welds 62 / 63 / 67 and the kernel identification |
| `Lean/Integration/AveragingResidualWeld.lean` | the averaging pipeline, arrow by arrow |
| `Lean/Integration/InteractionWelds.lean` | the interaction owner against real corpus tables |
| `Lean/Integration/OutstandingObligations.lean` | the frontier extractor |

All are in the `Integration` / `AgdaMirror` build targets, imported by
`Lean/Integration.lean`, and audited in `Lean/Integration/AxiomAudit.lean`.

---

## 2. The three unresolved welds, sharpened

### Weld 62 — provisioning: **exact instance** (registry row 71)

The requested carrier chain was recovered from a real checked-shape Agda module,
`Agda/DASHI/Core/SocioEcologicalFeedbackExact.agda`, mirrored in
`AgdaMirror.NonFactorabilityKernels.SocioEcologicalFeedback`.  Its actual
surface is

```
  World  --actorOf-->    ActorDisposition
  World  --staticScore-> StaticPlanScore
  World  --react i-->    Outcome
```

so the literal `R → P → N → W` chain is *not* what the corpus states; what it
states is a resource observer `staticScore`, a provisioning observer `actorOf`,
and a realised outcome `react`.  The precise question was answered in the
negative, in exactly the requested shape:

```lean
theorem resource_does_not_determine_realised_outcome :
    ∃ x y : World,
      resourceObserver x = resourceObserver y ∧
      provisioningObserver x ≠ provisioningObserver y ∧
      realisedOutcome x ≠ realisedOutcome y
```

and welded to both frozen owners rather than to a new framework:

* `resourceCollision : Collision resourceObserver realisedOutcome` — the
  `FactorisationCollision` side;
* `resource_observer_not_adequate` — for **every** downstream reading
  `observe : StaticPlanScore → Obs`, the resource pipeline is not
  `AdequateFor` the realised-outcome consumer;
* `provisioned_pipeline_adequate` — restoring the provisioning observer
  restores adequacy;
* `resource_repair_is_representational` — and the repair is therefore
  representational, not computational.

`weld62_resource_adequacy` bundles the four.

### Weld 63 — the interaction bridge: **re-assigned owner** (registry rows 72, 77–81)

Weld 63 was welded to `SeparabilityContrast`, and that was wrong.  Two findings.

1. **The contrast owner cannot apply on the corpus's provisioning surface.**
   `SocioEcologicalFeedbackExact.Intervention` has a *single* constructor, so
   the first coordinate is a subsingleton and every table over it is separable:

   ```lean
   theorem separable_of_subsingleton_left {A B M} [AddCommGroup M] [Subsingleton A]
       (C : A → B → M) : Separable C
   theorem socioEcological_every_table_separable ...
   ```

   That is a genuine negative result, not a missing proof.

2. **The corpus's contextual and intersectional consumers are separable too.**
   Every consumer in that lane — `counterfactualRelativeEffect`,
   `effectiveCapabilityWitness`, `withinGroupEffect`, `uptakeAt`,
   `labourIncidenceAt` — is a function of a *single* fine coordinate; the
   corpus's point is always that a *coarse* projection collides.  A
   one-coordinate table is separable, so the interaction owner has nothing to
   refute there.  Recorded as `contextual_effect_separable` and
   `intersectional_capability_separable` (registry row 80).

   **These surfaces belong to `FactorisationCollision`, not to
   `SeparabilityContrast`.**  That is the owner-level correction this tranche
   produced: a re-assignment, not a new abstraction.

Where, then, does the interaction owner have real instances?  In three
*independent* corpus modules that never mention interaction (§4).

### Weld 67 — exhaustiveness: **bridge hypothesis discharged; socket still open** (registry row 76)

The requested demonstration —
`AdequateOn + Exhaustive ⇒ Adequate` on a real proof-producing carrier — is
`Integration.SourceExactWelds.SSPAdequacy`, over the corpus's fifteen-element
`SSP` carrier from `Agda/MonsterOntos.agda`:

* `sspEnumeration_complete : ∀ p : SSP, p ∈ sspEnumeration` — **by `decide`**,
  a kernel-checked constructive completeness proof, not a flag;
* `sspExhaustive : Exhaustive (· ∈ sspEnumeration)`;
* `twoDigit_adequate` — global adequacy obtained from `AdequateOn` plus that
  evidence, through the owner theorem `adequate_of_adequateOn_exhaustive`;
* `lastDigit_adequateOn_atlas`, `sspAtlas_not_exhaustive`,
  `lastDigit_not_adequate` — the same route over a three-element sub-atlas
  delivers nothing, because that carrier has no such evidence;
* `exhaustiveness_evidence_is_load_bearing` bundles the contrast.

The corpus's own *atlas* modules still declare coverage as a `Bool` field rather
than proving it, so the socket on those surfaces stays open (row 69).

---

## 3. The Fanning-shaped pipeline, arrow by arrow

No module named `Fanning` exists in the corpus.  The surface with that shape —
raw → normalised → residual → within-domain aggregate → consumer — is the
fibre-averaging pair `Agda/DASHI/Analysis/NormalizedFibreAveragingExact.agda`
and `Agda/DASHI/Analysis/WeightedCoarseFineOrthogonalExact.agda`, mirrored in
`AgdaMirror.FibreAveraging` and classified in
`Integration.AveragingResidualWeld`.

| arrow | question | verdict | theorem |
| --- | --- | --- | --- |
| `pullback` | injective? | **yes** | `pullback_injective` |
| `average` | determines the coarse component? | **yes** | `average_determines_coarse` |
| `average` | determines the residual `Q`? | **no** | `average_does_not_determine_residual` |
| `P = pullback ∘ average` | equals `pullback ∘ average`? | yes, by definition | `average_P` |
| `decompose = (average, Q)` | determines the observable? | **yes** | `decompose_determines_observable` |
| any downstream `f ∘ average` | recovers the residual? | **no** | `no_reading_of_the_average_recovers_the_residual` |
| repair | computational or representational? | **representational** | `averaging_repair_is_representational`, `decompose_is_the_repair` |

`averaging_pipeline_classified` bundles the classification.

The compensation phenomenon now reads as exactly what the instruction predicted
and nothing more exotic:

```lean
def compensationCollision : Collision average Q
```

two fine observables whose within-fibre averages agree and whose residuals do
not.  The module is conceptually smaller than the phenomenon it records: the
whole content is one `Collision` plus the four positive arrows above.

---

## 4. Interaction structure: three independent consumers, one obstruction

`Integration.InteractionWelds` tests `SeparabilityContrast` against three corpus
modules that share nothing but the corpus prelude and none of which mentions
interaction, separability or contrast.  In each case the *same* generic theorem
`Integration.CoordinateSufficiency.separable_rectangle` produces the refutation
from a rectangle violation `C₀₀ + C₁₁ ≠ C₀₁ + C₁₀`.

| corpus surface | coordinates | verdict | theorem |
| --- | --- | --- | --- |
| `FiniteAnisotropicKernelExact.positiveKernelValue` | sharpness × radius class | **interacts** | `Kernel.kernel_not_separable` |
| `SelfConsistentEventRendererExact.combinedAffinity` | kernel value × shared depth | **interacts** | `Affinity.combinedAffinity_not_separable` |
| `MeasureFieldAdapterExact.restrictField` | slice choice × two-cell field | **interacts** | `Slice.restrictField_not_separable` |
| `SelfConsistentEventRendererExact.additiveAffinity` | kernel value × shared depth | **separable** | `Affinity.additiveAffinity_separable` |
| `EarlyLearningCounterfactualHeterogeneityExact` effect | position × counterfactual | **separable** | `Contextual.contextual_effect_separable` |
| `EarlyLearningIntersectionalCapabilityExact` capability | care burden × labour | **separable** | `Intersectional.intersectional_capability_separable` |

`three_corpus_tables_one_rectangle` is the success criterion; the criterion was
not three examples but that all three instantiate the same obstruction, and they
do.  `the_owner_is_discriminating` records that the owner also certifies the
three non-instances, so it is not a device that says "nonseparable" about
everything.

A by-product worth naming.  The corpus states of the renderer pair only that the
product and the sum disagree at the single point `(3, shared2)`
(`productAndAdditiveAreModellingChoices`).  Disagreeing at a point is compatible
with both being separable.  The owner upgrades this to a structural difference —
`corpus_pointwise_claim_is_weaker`.

### Interaction is not another coordinate

For any table `C : A → B → ℚ` over finite nonempty coordinates define the
**additive surrogate**

```
  surrogate C a b = rowMean C a + colMean C b − grandMean C.
```

Proved in `Integration.InteractionWelds`:

* `rowMean_surrogate`, `colMean_surrogate` — the surrogate has *exactly* the row
  means and column means of `C`;
* `surrogate_separable` — and it is separable;
* `interaction_is_not_another_coordinate` — hence for every nonseparable `C`
  there is a **different** table agreeing with `C` on every marginal
  coordinate.

So a representation may retain every marginal coordinate and still fail to
determine the table: the lost quantity is not a coordinate that could have been
kept alongside the margins.  Instantiated on the corpus's own kernel table as
`kernel_marginals_do_not_determine_the_table` (registry row 81) and on the
renderer's product rule as `affinity_marginals_do_not_determine_the_table`.

---

## 5. The pipeline theorem and the repair dichotomy

`Integration.PipelineAdequacy` supplies the composition result the instruction
asked for.  A `Stages` is a family `Carrier : ℕ → Type` with
`step i : Carrier i → Carrier (i+1)`; `Stages.run i j` is the composite.

* `collision_propagates`, `collision_propagates_le` — a collision at stage `i`
  survives every later stage.
* `no_downstream_determination` — if `P x = P y` and `C x ≠ C y` then for every
  downstream `f`, `f (P x) = f (P y)`; hence no computation depending only on
  `P` determines `C`.
* `no_downstream_repair` — **consumer-relevant collision at stage `i` ⇒ no later
  deterministic stage repairs adequacy.**
* `ComputationRepair` / `RepresentationRepair`, `no_computation_repair`,
  `representationRepair_exists`, `repair_dichotomy`,
  `repair_dichotomy_downstream` — the two repairs are formally distinguished,
  and the first is proved impossible exactly when a collision is present, while
  the second always exists (restore the information before the collision).
* `not_adequateFor_of_state_collision`,
  `pipeline_adequacy_lost_at_realisation`,
  `realisation_repair_is_representational` — the same statements in the
  `RealisationAdequacy` vocabulary, so the two owners compose rather than
  duplicate.

This is the result used by welds 62 and 63 and by the averaging classification,
which is the evidence that it is generic rather than bespoke.

---

## 6. The corpus defines the collision owner twice

A structural finding about the corpus itself (registry row 70).

`Agda/DASHI/Core/IntersectionalNonFactorability.agda` and
`Agda/DASHI/Core/ReopenableConsumerInterventionKernelExact.agda` §1 declare the
**same record** under two names.  Mirrored and identified in
`Integration.SourceExactWelds`:

```lean
def kernelWitnessEquiv :
    Intersectional.NonFactorabilityWitness P C ≃ ConsumerKernel.ConsumerDescentDefect P C
def kernelTransport : Integration.Levels.Transport ...     -- an exactInstance row
theorem kernel_refutations_are_the_owner ...
theorem nonempty_factorsThrough_iff_determines ...
```

Syntactic usage counts over the tracked Agda tree (`rg`, file counts, **not** a
typecheck): 33 files mention `IntersectionalNonFactorability` and 32 import it;
23 mention `ReopenableConsumerInterventionKernelExact`; 20 use
`nonFactorabilityWitness`.  `three_corpus_surfaces_one_owner` shows three
unrelated consumers (situated capability, labour axis, child axis) discharging
through the single Lean owner.

Two corpus "no auto-promotion" boundaries are stated as **empty datatypes** —
declarations, not theorems.  Both now have real theorem content:
`separate_axis_sufficiency_does_not_promote` and
`no_aggregation_rule_determines_the_outcome_vector` (by cardinality, 3 < 162,
with `card_outcomeVector = 162` proved).

---

## 7. The frontier extractor

`Integration.OutstandingObligations` turns the registry from a map of what
happened into a map of what remains provable.

```lean
inductive MissingEvidence
  | exactSourceCarrier (what : String)
  | theoremInhabitingField (field : String)
  | collisionWitness (what : String)
  | enumerationCompleteness (what : String)
  | agdaTypecheckResult

def MissingEvidence.wouldReclassifyTo : MissingEvidence → Option Kind
```

`obligationLedger` has one entry per outstanding row — registry indices
5, 11, 12, 15, 16, 20, 31, 37, 38, 43, 53, 55, 61, 62, 66, 68 — and three facts
are machine-checked, not asserted:

* `ledger_covers_outstanding` — the ledger lists exactly the outstanding rows.
  A row that changes class, or a new open row without a ledger entry, breaks the
  build.
* `outstanding_count` — `obligationLedger.length = kindCensus .candidateBridge +
  kindCensus .openSocket` (= 7 + 9 = 16).
* `discharge_always_closes` — every recorded missing evidence, if supplied,
  moves the row *out of* the two open classes.

`frontier_split` records the shape of the frontier: **6** rows waiting for an
exact source carrier, **9** waiting for a theorem inhabiting a free field, **1**
waiting for a constructive enumeration completeness proof.

---

## 8. Registry census (compiler-evaluated)

`Integration.SewingRegistry`, all by `rfl` / `decide`:

| class | count |
| --- | --- |
| `exactInstance` | 3 |
| `approximateInstance` | 2 |
| `finiteShadow` | 1 |
| `structuralAnalogue` | 1 |
| `candidateBridge` | 7 |
| `negativeResult` | 58 |
| `openSocket` | 9 |
| **total** (`registry_length`) | **81** |
| negatives + sockets | 67 |

`census_total` proves the seven counts sum to `registry_length`;
`negatives_and_sockets_majority` proves negatives and sockets are more than half
the registry; `every_row_has_boundary`, `no_branch_only_rows`,
`every_row_lean_built` and `no_row_claims_agda_typechecked` are the standing
hygiene theorems.

---

## 9. Honest frontier

**Stop condition.**  Outcome (1) of the two the instruction allowed: the four
owners absorbed every real weld surface reached in this tranche **without a
fifth owner being added**.  `PipelineAdequacy` is a composition theorem over the
existing owners, not a new one.  The only owner-level change was a
*re-assignment*: weld 63's corpus surfaces belong to `FactorisationCollision`,
not to `SeparabilityContrast`.

No source-exact object was found that the four owners cannot express, so this
tranche does **not** locate the start of Level III.

**Exact remaining obligations.**

1. **16 registry rows remain open** (7 `candidateBridge`, 9 `openSocket`), each
   with its typed missing evidence in `obligationLedger`.  The dominant shape is
   `theoremInhabitingField` (9 rows): a corpus record declares a `Bool` field
   that no corpus theorem constrains.
2. **No Agda module has been rechecked.**  Every mirror is a transcription;
   `agdaTypecheckResult` is a distinct `MissingEvidence` constructor precisely
   because supplying it would change validation status, not classification.
3. **One transcription hazard is recorded and unresolved.**
   `EarlyLearningCounterfactualHeterogeneityExact.counterfactualRelativeEffect`
   is written in Agda with left-hand patterns that are *defined names* rather
   than constructors.  Whether the Agda text elaborates to the table its clause
   values describe cannot be settled here.  `Integration.CounterfactualEffect`
   states the constructor-pattern reading and the registry row says so; no
   second reading of the same Agda text was introduced.
4. **The corpus's atlas coverage flags remain `Bool`.**  Weld 67's upgrade route
   is demonstrated on `SSP` because that carrier has a decided enumeration; the
   atlas modules do not, and row 69 stays open.
5. **The `Type → Type u` generalisation of the owners was deliberately not
   done.**  No consumer encountered in this tranche was blocked by it.

**Not claimed.**  No physical theory-of-everything; no empirical, educational,
institutional or policy claim; no Monster-group, moonshine or vertex-algebra
result; no measure-theoretic disintegration.  Every numeric entry quoted from
the corpus is one of its own structural witnesses.

---

## 10. Provenance map for this tranche

Each arrow is a Lean `import` plus a named theorem.

```
Integration.CoordinateSufficiency  ──Separable, separable_rectangle──┐
Integration.SeparabilityContrast   ──separable_iff_rectangle─────────┤
                                                                     ├─> Integration.InteractionWelds
AgdaMirror.InteractionTables       ──positiveKernelValue, …──────────┤        (rows 77–81)
Integration.CounterfactualEffect   ──counterfactualRelativeEffect────┘
AgdaMirror.NonFactorabilityKernels ──SituatedCapability──────────────┘

Integration.RealisationAdequacy    ──AdequateFor, AdequateOn, Exhaustive──┐
Integration.FactorisationCollision ──Collision, Determines────────────────┤
                                                                          ├─> Integration.PipelineAdequacy
                                                                          │
AgdaMirror.NonFactorabilityKernels ──SocioEcologicalFeedback──────────────┼─> Integration.SourceExactWelds
AgdaMirror.MonsterOntos            ──SSP──────────────────────────────────┘        (rows 70–74, 76)

AgdaMirror.FibreAveraging          ──average, Q, decompose────────────────> Integration.AveragingResidualWeld
                                                                                   (row 75)

Integration.SewingRegistry         ──kindCensus, sewingRegistry───────────> Integration.OutstandingObligations
```
