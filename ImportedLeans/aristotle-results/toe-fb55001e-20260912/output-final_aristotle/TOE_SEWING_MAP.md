# The TOE sewing round: inventory, provenance, classified relations, frontier

This is the prose companion to the machine-checked artefacts of this round:

| artefact | what it is |
|---|---|
| `Lean/Integration/SewingTaxonomy.lean` | the seven-class relation taxonomy and the provenance schema |
| `Lean/Integration/SewingRegistry.lean` | the classified rows, with meta-theorems: rows 1–24 from the earlier round, rows 25–44 the physical-biology and product-state tranche, rows 45–60 the decision/intervention/aggregation tranche, rows 61–69 the Level-II consolidation, rows 70–81 the Level-II discharge and stress-test tranche.  The row count and the per-class counts are **not maintained by hand**: they are `registry_length`, `kindCensus` and `census_total`, evaluated by the compiler |
| `TOE_PHYSICAL_BIOLOGY_TRANCHE.md` | the companion report for rows 25–44: what was sewn, how, and exactly what is still owed |
| `TOE_LEVEL_II_TRANCHE.md` | the companion report for rows 45–60: selective decisions, interventions, multi-objective outcomes, reachability, marginalisation and declared carriers |
| `TOE_LEVEL_II_SPINE.md` | the companion report for rows 61–69: the four Level-II owners, the arrows into them, and the eight welds |
| `Lean/Integration/ChemistryReachability.lean` | the discharged chemistry bridge: a proved reachability procedure with a checkable hypothesis |
| `Lean/Integration/TernaryHubClosure.lean` | the general ternary-hub theorem, and the refutation of coordinate uniqueness |
| `CORPUS_INVENTORY.md`, `corpus_index.json`, `corpus_lanes.csv` | the corpus inventory and index |
| `scripts/corpus_inventory.py` | the indexer that regenerates them |
| `PR_HEADS_STATUS.md` | what happened to the PR heads |

Everything asserted here as *proved* is proved in a Lean file that `lake build`
elaborates; everything asserted as *counted* comes from the indexer reading
source text. **No Agda typechecker was run in this environment**, so no Agda
module is claimed to compile — and the registry proves, row by row, that no row
claims otherwise (`no_row_claims_agda_typechecked`).

---

## 1. Inventory

13 255 source files were indexed: 9 903 Agda and 3 352 Lean.

* **3 052 Agda files are in the Yang–Mills / Navier–Stokes lanes** (matched by
  `yangmills|navier|stokes|balaban|clay` anywhere in the path, or by a basename
  prefixed `NS`/`YM`, which is how `DASHI/Physics` names the bulk of that
  material). They are counted so that the corpus size is honest, and **not
  opened**: no file in that set was read, imported, mirrored or cited.
* **6 851 Agda files were read.** Of those, **68 contain a `postulate` block**
  and must be read as interfaces rather than as established mathematics; the
  inventory lists them individually.
* On the Lean side, **235 files are in a `defaultTargets` library** and are
  therefore actually elaborated; **3 117 are an unbuilt archive**
  (`Lean/outputs/…`, `Lean/DASHI/…`, `Lean/docs/…`, plus the root aggregates the
  lakefile excludes). The archive contains 1 180 occurrences of the token
  `sorry`; **none of it is checked, and none of it may be read as a result.**
  The 45 occurrences inside build targets are all in docstrings.
* There is no `axiom` declaration and no `@[implemented_by]` anywhere in the
  Lean tree.

Lane sizes (Agda, read set) for the lanes this round touched:

| lane | files | lines | `data` | `record` | `Bool` fields |
|---|---:|---:|---:|---:|---:|
| `DASHI/Biology` | 537 | 101 958 | 925 | 1 538 | 3 279 |
| `DASHI/Cognition` | 257 | 33 828 | 421 | 793 | 729 |
| `DASHI/Governance` | 161 | 26 027 | 392 | 662 | 981 |
| `DASHI/Ontology` | 80 | 9 839 | 79 | 112 | 263 |
| `DASHI/Culture` (incl. Cuisine) | 37 | 11 737 | 152 | 175 | 280 |
| `DASHI/Education` | 27 | 4 379 | 117 | 51 | 197 |
| `DASHI/Chemistry` | 5 | 1 267 | 11 | 46 | 39 |

The ratio in the last column is the single most important structural fact about
the corpus outside Physics: **these lanes are overwhelmingly records of `Bool`
fields**, most of them pinned to a constant by an accompanying equality field.
A pinned flag is a genuine (if weak) theorem about the record; an unpinned one
constrains nothing. Distinguishing the two, per field, is most of what the
sewing pass does.

## 2. Provenance and source-vs-mirror

Three kinds of Lean text appear, and the taxonomy records which is which
(`Provenance.surface`):

* `agdaMirror` — a hand transcription of a named Agda module
  (`Lean/AgdaMirror/*`, and the mirrored fragments inside the new modules).
  These are *transcriptions*, checked as Lean, never as Agda.
* `leanAboutAgda` — Lean text *about* an Agda surface that it does not
  transcribe: for instance the finite model in `Integration.ObserverPlurality`,
  which models the *shape* of a record, not its contents.
* `leanSource` — Lean development with no Agda original (most of
  `Integration/*`, `Spine/*`, `Synthesis/*`).

Every row also records `modulePath`, `prRef`, `ancestry`, per-language
validation (`AgdaCheck`, `LeanCheck`) and a non-empty `claimBoundary`. Two
meta-theorems keep this honest: `every_row_has_boundary` and
`every_row_lean_built`.

**PR heads.** `prRef` is `none` on every row, and this is proved
(`no_branch_only_rows`), because the PR_HEADS metadata and patches described in
the handoff are not present in the material available to this round. See
`PR_HEADS_STATUS.md` for what was searched and what would close the gap. In
particular **no claim is made about which PR surfaces are already represented in
the tracked tree**: deciding that without the patches would be exactly the
vocabulary-based inference the handoff forbids.

## 3. The owner set

The round maps surfaces onto the existing small owner set rather than importing
the corpus into the kernel. The owners used are:

| owner | what it owns |
|---|---|
| `Integration.Levels` | the four-level scale, `Transport`, `NoTransport`, `Boundary`, `Socket` |
| `Integration.TernaryHub` | the balanced `ZMod 3` coordinate behind the corpus's ternary carriers |
| `Integration.LeastSufficient` | `Sufficient` / `Refines`: what an observer determines |
| `Integration.EquivarianceObstruction` | when no equivariant map or equivalence can exist |
| `Integration.ApproximateIntertwiner` | exact vs certified-approximate commuting squares |
| `Integration.Refinement`, `Integration.StructureMorphism` | resolution-indexed refinement; the commuting square |
| `Integration.SewingTaxonomy` | *new*: the seven-class relation taxonomy and provenance schema |

Two owners were extended rather than duplicated:

* `Integration.EquivarianceObstruction` gains the **map-level** obstruction
  `no_equivariant_map_of_fibre` — precisely,
  `no_equivariant_map_of_fixed_to_free`: if a self-map on the source has a fixed
  point and the target's self-map has none, there is no equivariant *function*
  at all. No bijectivity, finiteness or group structure is assumed. The
  existing `no_equivariant_of_free_and_fixed` refutes only equivalences.
* `Integration.ObserverPlurality` adds `not_refines_of_collapse`, the
  domain-neutral lemma that a collapse refutes refinement; every incomparability
  in the round is an instance of it.

## 4. The seven classes

`Integration.SewingTaxonomy.Relation` has one constructor per class, and each
constructor **carries the witness its class demands**, so a row cannot be filed
without one:

| class | witness the constructor demands |
|---|---|
| `exactInstance` | an `Integration.Levels.Transport`: a bijection proved to intertwine the two operations |
| `approximateInstance` | an `IsApproxIntertwiner` with an explicit `ε` in a (pseudo)metric target |
| `finiteShadow` | a surjection onto a finite carrier |
| `structuralAnalogue` | a predicate on types satisfied by both carriers, **and no map between them** |
| `candidateBridge` | a *proved implication* `hyp → concl`, with `hyp` left open |
| `negativeResult` | a proposition together with its refutation |
| `openSocket` | a proposition witnessing underdetermination, together with its proof |

Supporting theorems: `identifiesCarriers_iff` (only `exactInstance` asserts that
the two carriers are the same structure), `toBridgeLevel_eq_none_iff` (the three
non-transport classes carry no positive level at all), and `Relation.carrierEquiv`
(an `exactInstance` row really does yield an equivalence, extracted from the row).

## 5. The rows

`Integration.SewingRegistry.sewingRegistry`.  Every count below is a compiler
evaluation of `kindCensus`, not a hand-maintained number, and `census_total`
proves that the seven class counts sum to `registry_length`, so no row escapes
classification and none is counted twice.  At the close of this round the census
reads 3 `exactInstance`, 2 `approximateInstance`, 1 `finiteShadow`, 1
`structuralAnalogue`, 7 `candidateBridge`, 58 `negativeResult`, 9 `openSocket`
over 81 rows, of which 67 are negatives or sockets.
`negatives_and_sockets_majority` proves the robust form of the
headline: **refutations and deliberately open sockets are more than half the
registry**, which is the honest shape of the result.  The subsections below
describe rows 1–24; rows 25–44, 45–60, 61–69 and 70–81 are described in
`TOE_PHYSICAL_BIOLOGY_TRANCHE.md`, `TOE_LEVEL_II_TRANCHE.md`,
`TOE_LEVEL_II_SPINE.md` and `TOE_LEVEL_II_DISCHARGE.md`.

### 5.1 Ontology → the ternary hub (rows 1–3)

`Agda/DASHI/Ontology/EpistemicTrit.agda` introduces a *seventh* three-element
carrier with a nine-clause "consensus" operation, unrelated in the corpus to any
other ternary carrier.

* **exactInstance** `Integration.Ontology.epistemicHub` — the carrier *is* the
  balanced hub digit: the involution swapping the two determinate states becomes
  negation in `ZMod 3`. `epistemicHub_trit` composes this to
  `DASHI.Algebra.Trit`. Boundary: the Agda module declares no involution; the
  one transported here is supplied by us, and the constructor names
  `supported`/`contradicted` are labels.
* `agree_eq_ifEq` characterises the nine-clause table as
  `if x = y then x else unresolved`; every algebraic fact the Agda module proves
  clause-by-clause follows. `agree_polarity_equivariant` shows the consensus
  operation is compatible with the hub polarity.
* **negativeResult** `agree_not_add` (and `agree_not_mul`, `agree_no_identity`)
  — the carrier is shared, the algebra is not: consensus is neither ring
  operation and has no identity.
* **negativeResult** `no_polarity_equivariant_forcing` — **the result the Agda
  module does not state**. It records two "collisions" of two chosen binary
  policies; in fact *no* map into `Bool` is polarity-equivariant, because
  polarity fixes `unresolved` while Boolean negation has no fixed point. This is
  an instance of the new map-level obstruction owner.

### 5.2 Biology / DNA → the ternary hub (rows 4–6)

`Agda/DASHI/Biology/DNAChemistryTritQuotientBridge.agda` proves two round-trips
between a three-way chemistry margin and the SSP trit.

* **exactInstance** `Integration.DNAMarginTrit.marginHub` — an eighth carrier
  joins the hub. `marginPolarity_unique` shows the transported involution is the
  only one that could be transported, so the identification fixes the structure
  rather than choosing it. Boundary: exact *for the induced involution*; the
  Agda module supplies none.
* **negativeResult** `no_injection_arity_to_margin` — the module's own
  `AdmissibleFibreArity` has four elements and the margin three, so the ternary
  quotient **cannot** index the admissible fibre. This is the checkable content
  of its `ternaryRequiredAtEveryStep = false`.
* **openSocket** `sheetFlags_underdetermined` — `isCompleteChemistryCoordinate`
  is a free `Bool`. `sheetTrit_redundant` additionally shows the record's `trit`
  field is determined by its `margin` field.

### 5.3 Education (rows 7–10)

`Agda/DASHI/Education/RelationalEducationGateAlgebra.agda`.

* **negativeResult** `sixOfSeven_no_witness` — validity is the seven-fold
  product (`validEquivProduct`), and one empty gate carrier empties it
  (`isEmpty_of_gate_empty`). The counterexample makes it sharp: **six of seven
  gates inhabited still yields no valid relation**, so gate satisfaction does
  not aggregate as a count.
* **negativeResult** `metric_governance_fail_closed` — *every* inhabitant of the
  metric-governance record has all five identification flags `false`, not merely
  the canonical one. This is the record's entire formal content.
* **negativeResult** `rate_value_not_injective` — `FiniteRate` is a
  *presentation*, not a value: `21/10000` and `42/20000` are distinct records
  with equal value. `value_multiplyRate` shows the module's `multiplyRate` does
  compute the independence product, and `overlap_lt_marginals` that the
  second-order rate is strictly below both marginals.
* **approximateInstance** `overlapCount_approx` — the one certified-approximate
  square of the round, with the bound written out: adding one member to a
  population changes the *rounded* expected overlap count by the module's own
  rate `21/10000`, up to at most one whole unit. The square genuinely does not
  commute exactly; `1` is the rounding bound and nothing else.

### 5.4 Alice Brown corpus / multi-observer (rows 11–12)

`Agda/DASHI/Biology/ParentAllyshipMultiObserverBridge.agda`, re-exported through
`AliceBrownCorpusLoom.agda` and the governance bridge. Its substantive claims
are `Bool` fields pinned to `true`.

* **openSocket** `projectionRecordIsLabel` — **the record contains no
  projection.** `ObserverProjection ≃ ObserverFibre × String`: no field denotes
  a map out of any carrier, so the three pinned flags cannot constrain any
  projection. That is the precise sense in which the claims are sockets.
* **negativeResult** `student_parent_incomparable`, with
  `no_projection_faithful`, `pairwise_incomparable_core`,
  `model_incomparable_with_each`, `plurality_jointly_faithful` — what those
  fields would have to mean, proved on an explicit finite model whose carrier is
  `Bool × Bool × Bool`: no projection determines the whole; the situated fibres
  are pairwise non-refining; the machine proxy neither refines nor is refined by
  any single situated fibre; and yet the three single-aspect fibres *jointly*
  determine the situation — **plurality is not incompleteness**. Boundary: this
  is a statement about coordinate projections on a three-bit carrier, not about
  the corpus's own projections (which are not maps at all), and not about
  students, parents, teachers or institutions.

### 5.5 Governance (rows 13–14)

`Agda/DASHI/Governance/AliceBrownInstitutionalAgencyChoiceBridgeExact.agda`.

* **openSocket** `emptyPromotion_proves_everything` — the module's
  declared-empty promotion types (`data FormalOptionPromotesAgency : Set where`,
  eliminated by `()`) **carry no information**: an inhabitant of an empty type
  proves every proposition, so the eliminator is a fact about the declaration.
  Filing it as "formal availability does not imply agency" would be inferring a
  theorem from a constructor name. This is the sharpest negative-about-a-negative
  in the round.
* **negativeResult** `agency_not_determined_by_formalOption` — the honest
  replacement, on the module's own five-`Bool` record: the formal-option field
  does not determine the accessibility field. `surface_fields_independent`
  generalises it, and `boundary_record_unconstrained` shows the six-field
  boundary record's canonical values are a choice (all 64 assignments are
  inhabited), not a theorem.

### 5.6 Chemistry (rows 15–17)

`Agda/DASHI/Chemistry/TransitionKernel.agda`, 429 lines, almost all `String`
carriers and free `Bool` flags.

* **negativeResult** `kernel_fail_closed` — the four pinned flags are the
  theorem: no inhabitant of the kernel can assert measured parameters, accepted
  wet-lab validation, molecular-identity authority, or promoted conservation.
* **openSocket** `goalReachable_underdetermined` (also
  `obligationsDischarged_underdetermined`, `conservationChecked_underdetermined`)
  — for *any* transition-system value, both flag values are available, so the
  flag is not a function of the model it is attached to.
* **candidateBridge** `flag_determined_of_sound` — the only candidate bridge of
  the round, and its hypothesis is written out: given a decision procedure and
  `FlagSound` (the flag agrees with it on a class of problems), the flag becomes
  a function of the transition system. The implication is proved;
  `flagSound_not_automatic` shows the hypothesis is not free, so the bridge
  cannot be discharged by logic alone.

### 5.7 A shared shape with no map (row 18)

* **structuralAnalogue** — `EducationMetricGovernance` and
  `ChemistryTransitionKernel` both satisfy "there is a `Bool` field constantly
  `false`": the same fail-closed shape, arrived at independently in two lanes.
  The class is deliberately the weakest one: **no map between them is claimed,
  and none exists in the corpus.** This row exists precisely to demonstrate the
  class that must never be read as an identification.

### 5.8 The loom relation algebra (rows 19–21)

`Lean/AgdaMirror/LoomRelationAlgebra.lean` previously carried placeholder
theorems of the form `relationRootFor t = relationRootFor t := rfl`. Those are
now replaced by content, and three rows are filed from it.

* **finiteShadow** (row 19) — `relationRootFor` maps the nine relation labels
  onto the four coarse roots. `relationRootFor_surjective` licenses the row;
  `relationRootFor_not_injective` is why it is a shadow rather than an exact
  instance. This is the round's only `finiteShadow`.
* **negativeResult** (row 20) — the Agda record pins a `Bool` field
  `separatesRelationFromPromotion` to `true`. Row 20 is what that flag is
  *for*, as a theorem: two typed relations with the same relation type (hence
  the same root and bucket) and different promotion states.
* **openSocket** (row 21) — `typedRelationEquiv` proves the record's declared
  root and bucket fields are redundant, so a typed relation is exactly its type
  plus evidence status, promotion state and a note. Of those, evidence status is
  unconstrained by the corpus
  (`evidence_not_determined_by_relationType`).

Nothing here asserts anything about affidavits, evidence sufficiency, or legal
process: every carrier is a finite label type.

`finiteShadow` was unexercised in the first pass of this round; row 19 supplies
the one genuine instance found, and the count is proved rather than asserted.

### 5.9 The chemistry bridge, discharged (rows 22–23)

`Lean/Integration/ChemistryReachability.lean` supplies the side that row 17
left open.

* `reachB` is a bounded reachability procedure on a finite state type.
  `reachB_sound` proves everything it accepts is reachable;
  `reachB_complete_of_fixpoint` proves the converse **under an explicitly
  checkable hypothesis** — that one further iteration accepts nothing new.
  That hypothesis is a finite `Bool` identity, so it is discharged by kernel
  computation for any concrete graph. Together they give
  `reachB_iff_of_fixpoint`: at a fixpoint the procedure *decides* reachability.
* `cstep` is a concrete four-state graph (a three-cycle plus an isolated
  state); `cstepSaturates` discharges the fixpoint hypothesis for it.
* `cstep_not_reaches_three` (**row 22**, `negativeResult`) is a genuine
  non-reachability proof — not an unset flag.
* `chemistryFlagSound` is an actual inhabitant of
  `ChemistryKernelSocket.FlagSound`, so `chemistryFlag_determined` follows from
  `flag_determined_of_sound`: on correctly populated problems the reachability
  flag is a function of the transition system. `correctlyPopulated_nonempty`
  shows the class is not vacuous.
* `correctness_restriction_is_needed` (**row 23**, `negativeResult`) shows the
  restriction is load-bearing: over the *same* system, an incorrectly populated
  problem carries the opposite flag. Discharging the bridge does not close the
  socket in general.

Boundary: `V` is a finite label type and `step` is a `Bool`-valued relation on
it. "Reachability" and "transition system" are used in their graph-theoretic
sense only; nothing here concerns molecules, reactions or laboratory procedure.

### 5.10 The ternary hub, closed (row 24)

`Lean/Integration/TernaryHubClosure.lean` replaces eight hand-written hub
equivalences with one theorem and one correction.

* `BalancedInvolution A σ z` bundles four `decide`-able hypotheses: `A` has
  three elements, `σ` is self-inverse, `σ` fixes `z`, and `z` is its **only**
  fixed point.
* `ternaryHub_of_involution` produces a
  `Integration.Levels.Transport A (ZMod 3) σ zneg` sending `z` to `0`. Using it
  on a concrete carrier costs exactly four `by decide`s;
  `six_carriers_from_closure` collects six worked instantiations — `Trit`,
  `TriTruth`, `Digit369`, `SSPTrit`, `EpistemicTrit` and `ChemistryMargin`.
  `TritCode` (a dependent record) and `BTBranch` (no declared involution) are
  the two that stay hand-written, and the file says so.
* **Row 24, `negativeResult`.** The obligation as originally written asked for a
  *unique* balanced coordinate. That is false: `ternaryHub_two_coordinates`
  exhibits two, differing by an overall sign, and `ternaryHub_not_unique`
  refutes uniqueness outright. The correction is recorded as a row rather than
  quietly dropped.

## 6. Negatives, counterexamples and missing witnesses, collected

Treated as first-class results, in one place:

| result | what it refutes or exhibits |
|---|---|
| `Ontology.no_polarity_equivariant_forcing` | every binary forcing breaks the evidence polarity, not just the two named policies |
| `Ontology.agree_not_add`, `agree_not_mul`, `agree_no_identity` | a shared carrier does not transport the algebra |
| `Ontology.forcing_not_injective` | every binary policy collapses two states (cardinality) |
| `DNAMarginTrit.no_injection_arity_to_margin` | the ternary quotient cannot index a four-way fibre |
| `EducationGates.sixOfSeven_no_witness` | six of seven gates is not "nearly valid": there is no witness at all |
| `EducationGates.rate_value_not_injective` | the rate record is a presentation, not a value |
| `ObserverPlurality.no_projection_faithful` | no observer projection equals the whole |
| `ObserverPlurality.student_parent_incomparable`, `pairwise_incomparable_core`, `model_incomparable_with_each` | six pairwise non-refinements |
| `GovernanceAgency.emptyPromotion_proves_everything` | a declared-empty type refutes nothing |
| `GovernanceAgency.boundary_record_unconstrained` | canonical flag values are a choice, not a theorem |
| `ChemistryKernelSocket.flagSound_not_automatic` | the candidate bridge's hypothesis is genuinely missing |
| `Refinement.loom_root_not_product` (earlier round) | the loom is not a fibre bundle over its roots |
| `AgdaMirror.Loom.promotion_not_determined_by_relationType` | the loom's `separatesRelationFromPromotion` flag, restated as a refutation: promotion is not a function of the relation type |
| `AgdaMirror.Loom.relationRootFor_not_injective` | the root classifier is a shadow only — it has no inverse |
| `ChemistryReachability.cstep_not_reaches_three` | a proved non-reachability, obtained from the correctness of the decision procedure |
| `ChemistryReachability.correctness_restriction_is_needed` | discharging the bridge does not close the socket: the correctness class is load-bearing |
| `TernaryHubClosure.ternaryHub_not_unique` | the balanced ternary coordinate is not unique — it is fixed only up to an overall sign |

## 7. Coverage: what is reached and what is not

Before this round the Lean spine referenced 17 of the 76 `DASHI/*` lanes. It now
references 21: **Chemistry, Education, Governance and Ontology are newly
reached**, and Biology gains the DNA-margin surface.

Lanes with **no** Lean-side surface at all (largest first): `Crypto` (140),
`Reasoning` (91), `Promotion` (90), `Philosophy` (51), `Environment` (29),
`Combinatorics` (27), `Visualisation` (26), `Quantum` (14), `Empirical` (13),
`Dynamics` (13), `MDL` (9), `HME` (9), `Topology` (9), `Metric` (8), `Context`
(8), `Economics` (7), `Regulation` (6), and the remaining smaller lanes. `Agda/cubical`
(1 190 files) is a vendored library, not DASHI material.

## 8. Frontier: the highest-value next sewing obligations

Ordered by value/effort, with the exact obligation in each case.

1. ~~**Discharge the chemistry candidate bridge.**~~ **Done** — see §5.9.
   `Integration.ChemistryReachability.chemistryFlagSound` inhabits
   `ChemistryKernelSocket.FlagSound` for a concrete carrier and a decision
   procedure proved correct at a `decide`-able hypothesis. *Remaining
   obligation:* the corpus's own `ReachabilityProblem` values are still free
   `Bool`s (row 16 stays an `openSocket`); closing that needs the corpus to
   populate its flags from a system, not merely to admit that it could.
2. **Instantiate the observer model with the corpus's own projections.** Row 11
   is proved on a finite model because the Agda record supplies no maps (row 12).
   The obligation is to add projection *functions* to
   `ParentAllyshipMultiObserverBridge` — i.e. a carrier `W` and six maps out of
   it — at which point `not_refines_of_collapse` applies directly and the `Bool`
   fields become derivable rather than pinned. *Obligation:* a carrier and six
   maps, plus one separating pair per claimed incomparability.
3. **Sweep the pinned-versus-free flag census.** *Half done.*
   `scripts/corpus_inventory.py` now classifies every declared `... : Bool`
   field as **pinned** (the module also declares `f ≡ true` or `f ≡ false`) or
   **free**, and `CORPUS_INVENTORY.md` reports the per-lane split: 23 835 Bool
   fields in the read Agda set, 16 004 pinned and 7 831 free. A pinned flag is
   a `negativeResult` candidate and a free flag an `openSocket` candidate, so
   this is the row-generation frontier. *Remaining obligation:* emit the Lean
   rows. Note the count is **syntactic** — it matches source text and does not
   check that the companion field actually types.
4. ~~**The ternary hub is now eight carriers wide; close it.**~~ **Done** — see
   §5.10. `ternaryHub_of_involution` makes any three-element carrier with a
   self-inverse map having a single fixed point an automatic instance.
   *Correction to the obligation as originally stated:* the balanced coordinate
   is **not** unique. `ternaryHub_not_unique` refutes uniqueness, and
   `ternaryHub_two_coordinates` exhibits the two coordinates, which differ by an
   overall sign. `marginPolarity_unique` is not a special case of a uniqueness
   theorem — it fixes the *involution* given the coordinate, which is a
   different statement. `six_carriers_from_closure` re-derives six of the eight
   carriers (`Trit`, `TriTruth`, `Digit369`, `SSPTrit`, `EpistemicTrit`,
   `ChemistryMargin`) from the general theorem. *Remaining obligation:*
   `TritCode` is a dependent record rather than a flat enumeration, and the
   corpus declares no involution on `BTBranch`; both keep their hand-written
   treatment in `Integration.TernaryHub`.
5. **Agda-side validation.** Nothing in this repository has been typechecked by
   Agda. The single highest-value infrastructure obligation is a real Agda
   checker run over the read set, after which `AgdaCheck.agdaChecked` rows
   become fileable and `no_row_claims_agda_typechecked` should be *expected to
   fail* — that is what would make it informative.
6. **The `postulate` census.** 68 read Agda modules carry a `postulate` block.
   Each is an interface, and each is a candidate `openSocket` row. The
   obligation per module is a proof that the postulated statement is not derived
   elsewhere in the corpus — which needs (5) first.

## 9. Claim boundaries, restated

* Every carrier appearing in a witness in this round is a finite label type, a
  `Bool`-valued record, `ZMod 3`, `ℚ` or `ℝ`.
* Nothing here is a physical, chemical, biological, neural, educational,
  institutional or theory-of-everything claim, and nothing here bears on the
  Riemann hypothesis, Yang–Mills or Navier–Stokes. The Yang–Mills and
  Navier–Stokes lanes were excluded by path and basename filter and were not
  opened.
* Constructor names (`supported`, `contradicted`, `studentObserver`,
  `voiceGate`, `wetLabValidationAccepted`, …) are labels. Where a theorem is
  proved about a finite model of a record's *shape* rather than about the record
  itself, the row's `claimBoundary` says so, and so does this document.
* Citations appearing in the Agda sources (the Alice Brown papers and others)
  are reproduced as provenance strings only. Nothing in this round evaluates,
  endorses or formalises any cited finding.
