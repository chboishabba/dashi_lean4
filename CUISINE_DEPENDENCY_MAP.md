# Cuisine lane: dependency / provenance map and frontier report

Scope: the food-and-cookery material at `Agda/DASHI/Culture/Cuisine/`, its real
imports and callers, the genuinely formal links it does and does not have to the
rest of the corpus, and the Lean library `Lean/Cuisine/` that formalises its
proof-relevant content.

No Yang–Mills and no Navier–Stokes material is touched, referenced or
reintroduced anywhere in this work.

**Method caveat, stated up front.** Agda is not installed in the environment
this report was produced in, and building it here was not feasible. *No Agda
module in this repository was typechecked.* Every claim below about the Agda
sources is the result of reading them, not of running a checker. Everything
that is described as *proved* is proved in Lean and is verified by `lake build`:
the `Cuisine` and `Synthesis` libraries build with no `sorry`, no `axiom`, no
`native_decide`, and no axioms beyond `propext`, `Classical.choice` and
`Quot.sound` (see `Lean/Cuisine/AxiomAudit.lean`, which prints the audit as part
of the build).

---

## 1. The cuisine lane

Fourteen Agda modules, 3 284 lines:

| module | lines | `data` | `record` | `Bool` ledger pairs |
|---|---|---|---|---|
| `QualitativeSensoryCore` | 457 | 12 | 9 | 0 |
| `SituatedMoleWorld` | 518 | 13 | 12 | 9 |
| `ControlledSuccessCore` | 429 | 11 | 8 | 6 |
| `MoleProcessArchitecture` | 417 | 8 | 8 | 5 |
| `CuisineKnowledgeSourceAtlas` | 338 | 0 | 0 | 0 |
| `CuisineKnowledgeEcology` | 187 | 0 | 1 | 1 |
| `CuisineDataFlowCore` | 174 | 4 | 11 | 0 |
| `DishIdentityLineageCore` | 155 | 10 | 4 | 0 |
| `CompositionProvenanceCore` | 153 | 5 | 7 | 0 |
| `CuisineFormalismTests` | 139 | 1 | 0 | 5 |
| `ProvenanceRoutingBridge` | 120 | 3 | 3 | 4 |
| `CulinaryMovementCore` | 102 | 5 | 2 | 0 |
| `CuisineFormalismBundle` | 72 | 2 | 2 | 0 |
| `Everything` | 23 | – | – | – |

There are **no `postulate`s** in the lane, and none anywhere in its transitive
import closure.

### 1.1 Imports out of the lane

Direct external imports (7):

```
DASHI.Core.Prelude
DASHI.Core.GenericReceipt
DASHI.Core.AttributedSourceCore
DASHI.Culture.Preservation.ControlledDisclosureCore
DASHI.Biology.HyperfabricIntersectionalBodyMemoryBridge     (SituatedMoleWorld)
DASHI.Culture.KnotWeaveTopologyCultureBridge                (SituatedMoleWorld)
DASHI.Interop.SweetgrassCarrierSpine                        (SituatedMoleWorld)
```

Transitive closure outside the lane — 13 `DASHI.*` modules plus `Base369` and
`UFTC_Lattice` and the Agda standard library:

```
DASHI.Core.Prelude
DASHI.Core.GenericReceipt
DASHI.Core.AttributedSourceCore
DASHI.Culture.Preservation.ControlledDisclosureCore
DASHI.Biology.HyperfabricIntersectionalBodyMemoryBridge
DASHI.Culture.KnotWeaveTopologyCultureBridge
  └── DASHI.Culture.InverseBidirectionalCultureOperators
  └── DASHI.Interop.ObservationTransportSpine
DASHI.Interop.SweetgrassCarrierSpine
  └── DASHI.Interop.PNFRoleVectorAlgebra
  └── DASHI.Interop.SensibLawResidualLattice
        └── Base369            (HexTruth, rotateHex)
        └── UFTC_Lattice       (Severity)
        └── DASHI.Pressure
        └── DASHI.Interop.ITIRJoinBridge
```

That is 14 + 13 = **27 `DASHI` modules**, out of 8 662 in the repository.

### 1.2 Callers

Only `DASHI.Culture.Cuisine.Everything` is imported from outside the lane, by
exactly two modules:

```
DASHI.EverythingCuisineExtension  →  DASHI.Culture.Cuisine.Everything
DASHI.Culture.Everything          →  DASHI.Culture.Cuisine.Everything
```

`DASHI.Everything` (closure: 592 modules) does **not** reach cuisine.
`DASHI.Tranches.Everything` (closure: 2 686 modules) does, via
`EverythingCuisineExtension`.

---

## 2. What is, and is not, a formal link to the rest of the corpus

The corpus shares a great deal of *vocabulary* across domains. The following
were checked at the level of definitions, not names.

### 2.1 No link at all

There is **no import path, and no definitional dependency, from the cuisine lane
to any of**:

* the Monster material (`Agda/Monster/`, `MonsterGroups`, `MonsterOntos`,
  `MonsterSpec`, `MonsterState`, `MonsterConformance`);
* moonshine, modular or j-invariant material;
* `Agda/MDL/`;
* `Agda/cubical/` and any cubical-library development;
* supervoxel / hypervoxel algebra;
* any trit algebra or ternary arithmetic module;
* the dialectic loom modules (`DialecticalJourneyLoom`, `LoomRelationAlgebra`).

Shared words ("triad", "fibre", "spiral", "trit") occur in *string constants and
constructor names* on both sides. That is not a link, and this report treats it
as none.

### 2.2 Module reachability without definitional dependence

`Base369` — the module that carries the ternary/hexadic tone material — *is*
reachable from cuisine, along

```
SituatedMoleWorld → SweetgrassCarrierSpine → SensibLawResidualLattice → Base369
```

but what `SituatedMoleWorld` actually uses from `SweetgrassCarrierSpine` is the
single name `Sweetgrass.sweetgrassAttribution`, which is a `String` constant
(an attribution line for *Braiding Sweetgrass*). No `Base369` type, constructor
or function appears anywhere in the cuisine lane. This is a module edge, not a
mathematical one.

### 2.3 The one genuine cross-domain definitional dependency

`SituatedMoleWorld` has these fields:

```agda
    knotWeaveBridge      : Knot.KnotWeaveTopologyCultureBridge
    hyperfabricBridge    : Hyper.HyperfabricIntersectionalBodyMemoryBridge
    hyperfabricPowerAxes : List Hyper.PowerAtlasAxis
    hyperfabricPowerAxesAreCanonical :
      hyperfabricPowerAxes ≡ Hyper.canonicalPowerAtlasAxes
```

so the dependency on the "hyperfabric" module is real. That module is a
*guard*: its stated purpose is to treat dialectic / spiral / hypervoxel /
hyperfabric / trit / 369 / stage / prime / p-adic vocabulary as *candidate
interpretive carrier material* and to block its promotion to social, clinical,
legal or educational authority. It imports nothing; in particular it does not
import `Base369` or any ternary algebra.

`Lean/Cuisine/HyperfabricGuard.lean` audits this edge in checked form:

* `admissible_iff_candidate`, `exists_unique_admissible` — the guard has real
  proof content. `AdmissibleInterpretiveRoute` is `⊤` on the candidate route and
  the empty type on the other six; the candidate route is the **only** admissible
  one, so no authority promotion passes. (Agda states this as six separate
  absurdity lemmas and never as a uniqueness statement.)
* `surfaceName_injective` — the eight "triadic relation surfaces" are separated,
  and separated *only*, by their names. This is the checkable core of the
  informal non-collapse claim; Agda lists the names but never states their
  distinctness.
* `no_injective_trit_labelling`, `no_injective_hex_labelling` — eight surfaces do
  not inject into the 3-element `TriTruth` or the 6-element `HexTruth`. So the
  surface named `trit-triad-surface` is **not** a trit, and the family cannot be
  read as ternary structure at all.
* `canonicalPowerAtlasAxes_nodup`, `_length`, `_complete` — the twelve power axes
  are pairwise distinct and the canonical atlas is an enumeration of them.
* `HyperfabricFacet` is `Unique` (`hyperfabricFacetEquivUnit`) — the part of the
  hyperfabric module that the cuisine record actually stores is a singleton type.
  The edge contributes a fixed constant, not information.

### 2.4 The tempting identification, refuted

The cuisine lane's `SafetyEvidence` carrier (verified / unknown / rejected) has
three elements, as does the tone carrier `TriTruth` used by the Lean `Synthesis`
spine. `Lean/Cuisine/ToneSeparation.lean` settles what that coincidence gives:

* `safetyTritEquiv` — they are abstractly isomorphic (as any two 3-element sets
  are);
* `no_canonical_identification` — the isomorphism is not canonical;
* `no_order_three_monotone_selfmap` — **no** self-map of the safety carrier is
  simultaneously fixed-point-moving of order 3 (the defining datum of the tone
  rotation) and monotone for the fail-closed severity order
  `verified < unknown < rejected`;
* `safetyRotate_not_monotone` — in particular the transported rotation is not
  monotone.

So the tone structure provably does not transport. This is the honest, and the
only, bridge between the cuisine lane and the Monster/tone spine.

---

## 3. Classification of the supplied Agda material

The lane mixes five kinds of content. Distinguishing them was the main analytic
task.

| kind | how to recognise it | example | status |
|---|---|---|---|
| **enumerated definition** | `data` with no indices | `CuisineSurface`, `Sauce`, `PowerAtlasAxis` | fine; carries what it says |
| **proven theorem** | a `≡`-typed or `→ ⊥`-typed declaration with a real proof term | `neutralTriadUniversalismRouteRejected`, the `refl` checks in `CuisineFormalismTests` | real, but almost all are single-instance numeric checks |
| **record interface** | `record` whose fields are data + `String` + `Bool` | `SituatedMoleWorld`, `PublicationImpactAssessment` | an interface; inhabiting it is not proving anything about food |
| **`Bool` ledger placeholder** | field pair `f : Bool` and `f ≡ false` (or `≡ true`) | 30 such pairs across the lane | **no content** — see below |
| **unproved obligation** | an informal claim in a comment or a field *name* with no corresponding proposition | "fail-closed", "order-sensitive", "non-additive" | listed in §5 |

The `Bool`-with-`≡ false` pattern is the single most common construct in the
lane (30 pairs). `Lean/Cuisine/LedgerPattern.lean` proves that such a pair is a
singleton type (`FalseLedger` is `Unique`) and hence that a record built only
from such pairs is equivalent to `Unit`
(`cuisinePropositionBoundaryEquivUnit`, `no_information_in_ledger`). What the
pattern *does* achieve is real but modest: the typechecker guarantees the flag
is never set anywhere in the development. What it does **not** do is prove the
informal statement its field name describes.

---

## 4. The Lean library `Lean/Cuisine/`

Builds as the `Cuisine` library (a default target of the root `lakefile.toml`),
sorry-free, 15 modules, ~2 800 lines. Provenance of each module:

| Lean module | transcribes / answers | headline results |
|---|---|---|
| `Cuisine.SensoryCore` | `QualitativeSensoryCore` | `UmamiBlend.succ_combined_eq` (`1+c = (1+g)(1+n)`), `baseline_le_combined`, `not_additive`; `no_stimulus_only_valence`, `no_cue_only_safety` |
| `Cuisine.Surfaces` | the `SurfaceDistinction` non-collapse ledger | `SurfaceDistinction.ne` (sound), `irrefl`, `surfaceDistinction_incomplete` (partial: 6 recorded pairs out of 45), `no_surface_bijection` |
| `Cuisine.Lineage` | `DishIdentityLineageCore` | `SaucePath` refl/trans/`antisymm` — a partial order; `not_bechamel_to_bordelaise`; carbonara identity envelope as a partition |
| `Cuisine.ProcessRoute` | `MoleProcessArchitecture` | **defect**: `processEvent_total`, `processRouteRel_total`, `supplied_witness_does_not_separate_orders`; **repair**: `MoleRoute` with `orders_are_unmergeable`, `moleRoute_antisymm`, `no_route_chile_to_ash` |
| `Cuisine.DataFlow` | `CuisineDataFlowCore` | promotion round-trips, `isEmpty_promotedClaim_of_no_accepted_source`, `no_uniform_promoter`, `promotion_depends_on_policy` |
| `Cuisine.Publication` | `ControlledSuccessCore` | `decisionLevel_publicationDecision`, `publish_iff_low`; **hole** `LooseAssessment.publish_with_all_components_high`; **repair** `TightAssessment.abstains_of_any_component_high`, `publishes_iff_all_low` |
| `Cuisine.Provenance` | `ProvenanceRoutingBridge`, `CompositionProvenanceCore` | `no_source_determined_channel`, `no_three_channel_rule` |
| `Cuisine.LedgerPattern` | the corpus-wide `Bool` ledger idiom | `FalseLedger`/`TrueLedger` `Unique`, `cuisinePropositionBoundaryEquivUnit`, `no_information_in_ledger` |
| `Cuisine.CarryingCapacity` | `CuisineKnowledgeEcology` | **hole** `LooseCapacityProfile.within_while_exceeded`; **repair** `TightCapacityProfile.exceeded_iff`, `standing_functional`, `never_unknown`; **fail-closed variant** `GuardedCapacityProfile.unknown_of_missing`, `measured_of_within` |
| `Cuisine.SourceAtlas` | `CuisineKnowledgeSourceAtlas` | `sourceCount_eq_22`, `sourceIds_nodup` (distinctness the Agda count does not check), `citationCreatesAuthority_eq_false` |
| `Cuisine.HyperfabricGuard` | `HyperfabricIntersectionalBodyMemoryBridge` (the one cross-domain import) | `exists_unique_admissible`, `surfaceName_injective`, `no_injective_trit_labelling`, `canonicalPowerAtlasAxes_nodup`, `HyperfabricFacet` `Unique`, `hyperfabric_edge_audit` |
| `Cuisine.ToneSeparation` | cuisine ↔ `Synthesis.ToneCore` | `safetyTritEquiv`, `no_canonical_identification`, `no_order_three_monotone_selfmap`, `severityMonotone_injective_eq_id` |
| `Cuisine.Witnesses` | `CuisineFormalismTests` | dashi/funk profiles, the divergent-reading and same-cue witnesses, `agda_regressions`, `agda_route_regressions` |
| `Cuisine.EndToEnd` | the whole lane | `CuisineSpine` (26 fields) with inhabitant `cuisineSpine`; composite `cuisine_end_to_end` |
| `Cuisine.AxiomAudit` | – | `#print axioms` for every headline result |

Nothing in this library is an empirical claim about food, chemistry, safety,
history or cultural authority. Every carrier is a finite set or a list of
natural numbers. Nothing here is, or supports, a physical or mathematical
theory of everything.

---

## 5. Frontier report: exact remaining obligations

### 5.1 Defects found in the supplied Agda, with their status

| # | defect | where | status |
|---|---|---|---|
| (a) | `ProcessEvent`/`RecipeTransition` carry **phantom state indices**: no field mentions the two state arguments, so `ProcessRoute`/`Route` are total relations | `MoleProcessArchitecture` | **proved to be a defect** in Lean (`processRouteRel_total`); repaired **in Lean only** (`MoleRoute`). *The Agda source is unchanged and still has the defect.* |
| (b) | `PublicationImpactAssessment.overallRisk` is a free field, unconstrained by the component risks | `ControlledSuccessCore` | hole exhibited (`LooseAssessment.publish_with_all_components_high`), repair given in Lean. Agda unchanged. |
| (c) | `CarryingCapacityProfile.standing` is a free field, unconstrained by capacity vs. demand | `CuisineKnowledgeEcology` | hole exhibited (`LooseCapacityProfile.within_while_exceeded`), total repair and fail-closed variant given in Lean. Agda unchanged. |
| (d) | `sourceCount = 22` is a list length with no distinctness check | `CuisineKnowledgeSourceAtlas` | distinctness proved in Lean (`sourceIds_nodup`). Agda unchanged. |
| (e) | the 30 `flag : Bool` + `flag ≡ false` pairs are uniquely inhabited and prove nothing | lane-wide | characterised in Lean (`LedgerPattern`). Not a fixable "bug" — a documentation-vs-proof distinction. |
| (f) | `SurfaceDistinction` has no proof that the surfaces it relates differ, and covers only 6 of 45 pairs | `QualitativeSensoryCore` | soundness and incompleteness both proved in Lean. Agda unchanged. |
| (g) | `ProvenanceRoutingBridge` was in no aggregate | lane | **fixed in Agda**: a plain (non-`public`) `import` was appended to `DASHI/Culture/Cuisine/Everything.agda`. *Not typechecked here.* |

The Agda repairs for (a)–(d) and (f) are deliberately **not** applied. Editing
indexed families and record laws in 400-line Agda modules without a typechecker
would be irresponsible; the Lean repairs record precisely what the corrected
definitions should say.

### 5.2 Exact open proof obligations

Stated as Lean-side or Agda-side statements that are currently *not* proved
anywhere:

1. **Agda-side (a).** Re-index `ProcessEvent : MoleState → MoleState → Set` so
   each constructor's indices are determined by its data, then prove in Agda the
   analogue of `Cuisine.ProcessRoute.orders_are_unmergeable`.
2. **Agda-side (b).** Add `overallRiskIsJoin : overallRisk ≡ join locationRisk
   appropriationRisk harassmentRisk` to `PublicationImpactAssessment` and
   re-derive the Agda decision lemmas.
3. **Agda-side (c).** Add the standing law to `CarryingCapacityProfile`.
4. **Agda-side (f).** Add `distinctSurfaces : ¬ (a ≡ b)` to `SurfaceDistinction`,
   or replace the six-pair ledger with a decidable inequality on
   `CuisineSurface`; completing it to all 45 pairs is a separate obligation.
5. **Surface independence.** Nothing anywhere proves that the ten cuisine
   surfaces are pairwise *independent* in any sense stronger than "distinct".
   No definition in the corpus even states what independence would mean here.
6. **Cross-lane transport.** No positive cross-domain theorem exists: every
   checked bridge in this work is negative (`no_injective_trit_labelling`,
   `no_order_three_monotone_selfmap`). A positive link would require a
   *structure* on the cuisine carriers that is preserved; none is defined.

### 5.3 Wiring gaps

* Five `DASHI.Culture.*` modules are reachable from no `Everything` aggregate:
  `ProvenancePreservingCulturalHyperfabric`,
  `RelationalProcessProtocolBoundary`,
  `CulturalTriadGovernanceIntegration`,
  `RelationalTeachingCampaignBoundary`,
  `DerivedCulturalUseAdmissibility`.
  They were **not** wired in here, because without a typechecker there is no way
  to know whether adding them would break the aggregate.
* Repository-wide: of 8 662 `DASHI.*` modules, 4 064 are reachable from some
  `*.Everything` aggregate and **4 598 are reachable from none** — i.e. more
  than half the Agda corpus is not covered by any aggregate, and would not be
  checked by a build of the aggregates.
* `DASHI.Everything` reaches 592 modules; `DASHI.Tranches.Everything` reaches
  2 686 and is the only aggregate that reaches cuisine.

### 5.4 What could not be done in this environment

* **No Agda typechecking.** Agda is not installed. Every Agda-side statement in
  this report — the postulate-freedom of the closure, the classification table,
  the seven defects — rests on source reading. The one Agda edit made (the
  aggregate import in §5.1(g)) is syntactically minimal and non-`public`, but it
  has not been checked.
* Consequently the Agda side of the corpus carries **no verified status** here,
  positive or negative, and none is claimed.

---

## 6. Summary of what is actually proved

Everything in the following list is a Lean theorem that compiles, uses no
`sorry` and depends only on `propext`, `Classical.choice` and `Quot.sound`.

* The umami combination law is `c = g + n + g·n`, equivalently
  `1 + c = (1+g)(1+n)`; it is super-additive and is **not** additive in any
  reparametrisation.
* Neither valence nor safety is a function of the data the corresponding Agda
  records make available; two explicit witnesses realise both obstructions.
* The supplied mole route relation relates **every** pair of states and so
  proves nothing; a repaired route family makes the two cooking orders provably
  unmergeable.
* Sauce derivation is a partial order with two components.
* The promotion pipeline is fail-closed in a precise sense: no policy-generic
  promoter exists, and under a policy accepting no source the promoted-claim
  type is empty.
* The supplied publication assessment and carrying-capacity profile each admit a
  concrete inconsistent inhabitant; both repairs are exact (iff) and a
  fail-closed variant handles missing measurements.
* Provenance channels are not a function of the contribution.
* The `Bool` ledger idiom is contentless.
* The 22 atlas sources are distinct.
* The hyperfabric guard admits exactly one interpretive route; its triad
  vocabulary is separated only by naming and does not inject into any ternary or
  hexadic carrier; the facet of it the cuisine record stores is a singleton.
* The cuisine safety carrier and the `Synthesis` tone carrier are abstractly
  isomorphic and **no** tone structure transports between them.

And, negatively but just as firmly: the cuisine lane has **no** formal link to
the Monster, MDL, moonshine, cubical, supervoxel, trit-algebra or dialectic-loom
material in this repository.
