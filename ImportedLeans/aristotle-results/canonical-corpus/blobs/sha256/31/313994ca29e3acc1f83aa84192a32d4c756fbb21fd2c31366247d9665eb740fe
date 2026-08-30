# The physical-biology / product-state tranche: rows 25–44

This is the companion report for the intake round that stopped growing the
abstract spine and started consuming the corpus. It covers

* the **eight new Lean modules** added this round,
* the **twenty new registry rows** (25–44) they license,
* the **dependency and provenance map** from Agda source to Lean owner,
* and an **honest frontier**: the exact obligations that remain open, and the
  places where the corpus supplies a name rather than a theorem.

Everything below marked *proved* is elaborated by `lake build` (zero errors, no
`sorry` in any build-target file). Every new result is in
`Lean/Integration/AxiomAudit.lean`; every audited result there depends only on
`propext`, `Classical.choice`, `Quot.sound`. **No Agda typechecker was run**, so
no Agda module is claimed to compile, and the registry proves row by row that no
row claims otherwise.

---

## 1. What was added

| Lean module | what it owns |
|---|---|
| `Lean/Integration/CoordinateSufficiency.lean` | the generic product-state layer: `Determines`, coordinate `Essential`, the sufficiency family, interaction vs dependence, aggregation, observer joins |
| `Lean/Integration/ContextIndexedRole.lean` | the corpus's own non-factorability owner, identified with the Lean one; failure of context elimination; a five-coordinate relational consumer |
| `Lean/Integration/ApproximateTower.lean` | approximate naturality along a whole tower — the `n`-stage generalisation of the Agda two-stage accumulation |
| `Lean/Integration/KernelRenormalisation.lean` | exact descent versus preservation of locality, proved independent |
| `Lean/Integration/NeuralObservation.lean` | the corpus's own coarse projection, its collision, and its three consequences |
| `Lean/Integration/StatefulTransducer.lean` | the transducer → field-controlled-dynamics adapter, and the quantitative instance with memory |
| `Lean/Integration/CellDynamics.lean` | the bioelectric update as field control, cell attractors, and the reaction–diffusion socket |
| `Lean/Integration/HolonomySocket.lean` | the holonomy lane as an explicit open socket, with the obligation stated |

---

## 2. Dependency and provenance map

Arrows point from the corpus surface to the Lean owner that now consumes it.
`(mirror)` means the Lean text transcribes Agda text; `(about)` means the Lean
text is a development *about* a surface it does not transcribe.

```
Agda/DASHI/Core/ApproximateMultiscaleNaturality.agda        (mirror → about)
    │  TowerMetric, ApproximateKernelTower, commutationError,
    │  exact-as-approximate, accumulate-two-errors, ControlledErrorFamily
    └─▶ Integration.ApproximateTower
            ├─▶ Integration.StructureMorphism   (Exact = the commuting square)
            ├─▶ Integration.MultiscaleDescent   (LawTower, ApproxDescendsAt)
            └─▶ Integration.ApproximateIntertwiner (approx_comp)

Agda/DASHI/Core/ThresholdKernelRenormalisation.agda          (about)
    │  KernelCoarseGraining, CommutesExactly, LocalityPreserving/Destroyed
    └─▶ Integration.KernelRenormalisation
            ├─▶ Integration.StructureMorphism   (commutation *is* Exact)
            └─▶ Integration.LocalRealisation    (the separate cost certificate)

Agda/DASHI/Biology/NeuralRepresentationLaplacianExact.agda   (mirror)
    │  PopulationActivation, laplacianVariation, fmriLikeObservation,
    │  fmriProjectionCollision, activationUpdate
    └─▶ Integration.NeuralObservation
            ├─▶ Integration.ObserverBundle      (pullbackDist, not_measured_of_collision)
            ├─▶ Integration.MultiscaleDescent   (NoEffectiveLaw)
            └─▶ Integration.CoordinateSufficiency (Determines, Essential)
        ▲
        │ reuses the same projection
Agda/DASHI/Biology/TernaryMotifNeuralObservationQuotientExact.agda (mirror)
        motifOfTrit ∘ (three-phase carrier) — the ternary-phase collision

Agda/DASHI/Biology/StateDependentMultiplexTransducer.agda    (mirror)
    │  StatefulTransducer.step, canonicalBoolTransducer, the two separations
    └─▶ Integration.StatefulTransducer.toFieldControlled
            ├─▶ Integration.FieldControlledDynamics (FieldControlled, Fixed, Cycle)
            └─▶ Integration.CoordinateSufficiency   (all three inputs essential)
        ▲
        │ instantiates the same record
Agda/DASHI/Biology/QuantitativeStateDynamics.agda            (mirror)
        respond, quantitativeStep, the delayed store/release pair

Agda/DASHI/Biology/Cell/BioelectricNetwork.agda              (mirror)
    │  update : E → C → M → R → X → X, BioelectricPatternProjection
    └─▶ Integration.CellDynamics
            ├─▶ Integration.FieldControlledDynamics (the adapter)
            └─▶ Integration.CoordinateSufficiency   (five essential coordinates)

Agda/DASHI/Biology/Cell/CellStateAttractor.agda              (mirror)
    │  InBasin, StableIn, forwardInvariant (a *field*, i.e. an obligation)
    └─▶ Integration.CellDynamics.basin_forward_invariant (the obligation, proved)

Agda/DASHI/Biology/Morphogenesis/ReactionDiffusionModeSelection.agda (about)
    └─▶ Integration.CellDynamics.modeSelection_trivially_inhabited  [open socket]

Agda/DASHI/Biology/Levin/HolonomyReferenceFrameBoundary.agda (mirror)
    └─▶ Integration.HolonomySocket                                  [open socket]
            └─▶ Integration.CommutatorObservability (the owner it would fill)

Agda/DASHI/Core/IntersectionalNonFactorability.agda          (mirror)
    │  FactorsThrough, NonFactorabilityWitness,
    │  witnessRulesOutEveryFlatFactorisation
    └─▶ Integration.ContextIndexedRole.factorsThrough_iff_determines
            └─▶ Integration.CoordinateSufficiency.Determines
                    └─▶ Integration.LeastSufficient.Refines (the pre-existing owner)
```

The last chain is the most important structural finding of the round: the
corpus **already owns** generic non-factorability, in `DASHI/Core`, and states
it in exactly the form the Lean spine had arrived at independently.
`factorsThrough_iff_determines` proves the two are the same notion, so the
domain lanes are consumers supplying witnesses, not parallel calculi.

---

## 3. The rows

| # | corpus surface | TOE owner | class | Lean witness |
|---:|---|---|---|---|
| 25 | `ApproximateMultiscaleNaturality` | `StructureMorphism`, `MultiscaleDescent` | approximate instance | `ApproximateTower.defect_approx_at_one` |
| 26 | …its `commutationError` | `MultiscaleDescent.NoEffectiveLaw` | negative | `defect_no_effective_law_at_one` |
| 27 | `ThresholdKernelRenormalisation.LocalityPreserving` | `StructureMorphism` vs `LocalRealisation` | negative | `pooling_commutes` + `pooling_destroys_locality` |
| 28 | …its `CommutesExactly` | `StructureMorphism` | negative | `forgetful_no_coarse_law` |
| 29 | `NeuralRepresentationLaplacianExact.fmriLikeObservation` | `CoordinateSufficiency.Determines` | negative | `variation_not_determined` |
| 30 | …its `activationUpdate` | `MultiscaleDescent.NoEffectiveLaw` | negative | `neural_no_effective_law` |
| 31 | `TernaryMotifNeuralObservationQuotientExact` | `ObserverBundle`, `DescentLevel` | negative | `phase_not_determined` |
| 32 | `StateDependentMultiplexTransducer.StatefulTransducer` | `FieldControlledDynamics` | candidate bridge | `field_changes_successor_of_split` |
| 33 | …its `canonicalBoolTransducer` | `CoordinateSufficiency.FactorsOn` | negative | `canonical_output_not_input_only` |
| 34 | `QuantitativeStateDynamics.quantitativeStep` | residual / `CoordinateSufficiency` | negative | `pending_is_a_residual` |
| 35 | `Cell.BioelectricNetwork.update` | `FieldControlledDynamics` | negative | `update_not_state_only` |
| 36 | `BioelectricPatternProjection` | `ObserverBundle`, `MultiscaleDescent` | negative | `pattern_no_effective_law` |
| 37 | `Cell.CellStateAttractor` | `Fixed` / `Basin` / `Cycle` | negative | `phenotype_not_injective` |
| 38 | `Morphogenesis.ReactionDiffusionModeSelection` | `Levels.Socket` | **open socket** | `modeSelection_trivially_inhabited` |
| 39 | `Levin.HolonomyReferenceFrameBoundary` | `CommutatorObservability` | **open socket** | `flags_underdetermined` |
| 40 | `Core.IntersectionalNonFactorability` | `CoordinateSufficiency.Determines` | negative | `flat_reweighting_cannot_repair` |
| 41 | context-indexed role assignments | `ContextIndexedRole` | negative | `role_not_context_free` |
| 42 | product-state consumers | `CoordinateSufficiency.essentialSet` | negative | `access_only_full_is_sufficient` |
| 43 | additive readings of multi-axis consumers | `CoordinateSufficiency.Separable` | negative | `access_pair_not_separable` |
| 44 | aggregation downstream of `fmriLikeObservation` | `CoordinateSufficiency` (aggregation) | candidate bridge | `aggregation_destroys_distinction` |

With rows 25–44 in place the registry stood at 44 rows: 2 exact instances, 2
approximate, 1 finite shadow, 1 structural analogue, 3 candidate bridges, 28
negatives, 7 open sockets — 35 of them refutations or sockets.  A later tranche
added rows 45–60; the current census is the one proved by `rfl` in
`SewingRegistry.kinds_exercised`, and it is reported in
`TOE_LEVEL_II_TRANCHE.md`.

---

## 4. The generic layer, and why it is generic

Five theorem shapes recurred across the lanes under different names. They are
now owned once.

1. **Non-factorability.** `Determines O C` says the consumer is constant on the
   fibres of the observation; `not_determines_of_collision` turns one collided
   pair into a refutation of *every* candidate downstream map. Rows 29, 31, 34,
   40 are witnesses.
2. **Coordinate essentiality.** `Essential j C` and
   `essential_iff_not_factorsOn_compl` make "this axis matters" and "the
   consumer does not factor through the projection forgetting this axis" the
   same statement. On a finite index the essential set is itself sufficient
   (`factorsOn_essentialSet`) and is therefore the *unique least* sufficient
   set; `factorsOn_iff_essentialSet_subset` characterises the whole sufficiency
   family as its upward closure. Rows 33, 35, 42.
3. **Dependence is not interaction.** `Separable` and `separable_rectangle`
   separate "depends on both coordinates" from "cannot be decomposed into
   coordinatewise contributions"; `dependence_ne_interaction` exhibits a
   consumer of each kind on the same carrier. Row 43.
4. **Aggregation.** `no_sample_statistic_separates` and
   `aggregation_destroys_distinction`: repeated observation of two collided
   states produces literally identical data, so every statistic of every sample
   size agrees on them. Row 44. This is a deterministic statement about the
   observation map — it says nothing about estimation error or convergence, and
   the two must not be conflated.
5. **Downstream recharting cannot repair upstream erasure.**
   `not_determines_of_downstream`: post-processing an observation only ever
   loses more.

Two further owners were added for the context cluster:
`ContextEliminable` with `context_not_eliminable_of_split` (a frame-indexed role
need not come from a frame-free one, and eliminability is exactly
non-essentiality of the frame coordinate), and observer `join` with
`join_refines_left/right` and `join_least` — the join is the supremum in the
information order.

---

## 5. Frontier: exactly what remains open

### 5.1 Obligations stated but not discharged

* **Holonomy (row 39).** `Integration.HolonomySocket` states the obligation:
  supply a fibre `E`, a transport `T : E → E` around a closed path, and an
  observation; then exhibit `T x ≠ x`. `defect_can_be_invisible` proves that
  discharging that obligation does **not** discharge the second one (the
  observer may erase the defect entirely), so two separate witnesses are needed.
  The corpus supplies neither: its module has only free `Bool` flags, proved
  free by `flags_underdetermined` and `phaseDefect_flag_is_free`. This row must
  not be promoted without those two witnesses.
* **Reaction–diffusion (row 38).** Every condition in the module — local
  excitation, lateral inhibition, finite-wavelength instability, symmetry
  compatibility — is an uninterpreted field. `modeSelection_trivially_inhabited`
  shows the witness record is inhabited by trivial data, so *no* reading of an
  inhabitant is evidence of an instability. Discharging this needs an actual
  `evolve` and an actual mode predicate; the corpus has neither.
* **Candidate bridge 32.** The adapter is general; its hypothesis — some
  modulator pair splits the successor state — must be supplied per transducer.
  The corpus's Boolean and quantitative instances supply it
  (`canonical_field_separation`, `quantitative_field_separation`); an
  unmodulated transducer would not, so the hypothesis is not free.
* **Candidate bridge 44.** The hypothesis is a non-injective observation. The
  corpus supplies one here; the row records that the *implication* is the owned
  content and the witness is the lane's contribution.

### 5.2 Places where the corpus names a theorem it does not prove

* `ThresholdKernelRenormalisation.localityPreservationIsNotKernelCommutation`
  has type `LocalityPreserving → LocalityPreserving` and is the identity
  function. The separation it names is now proved, in both directions, by
  `KernelRenormalisation.descent_and_locality_independent`.
* `CellStateAttractor.forwardInvariant` is a record *field*: an obligation on
  the inhabitant, not a theorem. It is discharged for basins of fixed points by
  `CellDynamics.basin_forward_invariant`.
* `CellStateBoundary.attractorIsNotSemanticIdentityByDefinition` is an
  uninterpreted `Set`. Its content is proved by
  `CellDynamics.attractor_not_identity`.

### 5.3 Boundaries of what was proved

* `fmriLikeObservation` is a two-component sum of three natural numbers and
  `laplacianVariation` a sum of truncated differences. Neither models an imaging
  modality or a graph Laplacian spectrum. Rows 29–31 are about those functions.
* Every carrier in this tranche is finite or `ℕ`-valued: `Bool`, `Bool × Bool`,
  `Fin 4`, `Fin 5 → Bool`, three natural-number coordinates, and `ℝ` only as a
  readout. Nothing here is a physical, chemical, biological, neural or
  theory-of-everything claim.
* The approximate tier is bounded from below where it matters:
  `approximate_is_strictly_weaker` shows an error-`1` square at a level where no
  exact coarse law exists and every candidate has defect at least `1/2`. An
  approximate row is never an exactness claim.
* Finiteness of the index set is load-bearing in the coordinate theory:
  `essentialSet_not_sufficient_infinite` exhibits a non-constant consumer of an
  infinite product with no essential coordinate at all.
* No Yang–Mills or Navier–Stokes material was read, written or cited.

### 5.4 Not attempted this round

The lane-scale `Bool` census (16 004 pinned and 7 831 free fields) was
deliberately left un-automated, on the reasoning that turning it into registry
rows would grow a status database rather than sew mathematics. The structurally
interesting material is what this round consumed; the census remains available
in `CORPUS_INVENTORY.md` for a later pass.
