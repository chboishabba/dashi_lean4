# The Level-II spine: four owners, the arrows into them, and the welds

This is the prose companion to registry rows 61–69 and to the five Lean modules
added this round:

| module | what it owns |
|---|---|
| `Lean/Integration/RealisationAdequacy.lean` | consumer-indexed realisation and adequacy for the pipeline `S → R → X → O_c → Y_c` |
| `Lean/Integration/FactorisationCollision.lean` | projection loss, aggregation loss, scalarisation and marginalisation, as one theorem with four constructors |
| `Lean/Integration/SeparabilityContrast.lean` | coordinate separability, weighted contrasts, and contrast reversal as a proof of interaction |
| `Lean/Integration/LanguageReachability.lean` | reachability indexed by a declared action language |
| `Lean/Integration/LevelIIWelds.lean` | the seam: eight thin consumers sewn onto the four owners |

Everything asserted as *proved* below is elaborated by `lake build` and printed
by `Lean/Integration/AxiomAudit.lean`. **No Agda typechecker was run in this
environment**, and no statement here is a physical, biological, institutional or
theory-of-everything claim: every carrier is `ℕ`, `Bool`, `ℚ`, `Fin n`, a finite
label type, or an arbitrary type with no structure assumed.

---

## 0. What was not delivered to this environment

The task names an attachment — the net new content of the merged PR integration
branch `integrate/toe-consolidation-20260827`, based at `1ec4c33ba`, covering
PRs #583 and #602–#625. **No such bundle is present in this repository.** There
is no changed-file snapshot, no diff, no manifest, and no PR ref anywhere in the
tree or in git; the three archives in the repository root are prior-session
outputs, and a search of their file lists for the surfaces the task names
(provisioning, threshold-distance/Fanning, early-learning) returns nothing.
`PR_HEADS_STATUS.md` records the same finding from the previous round, and the
registry enforces it in Lean: `no_branch_only_rows` proves that no row cites a
PR head as provenance.

The consequence is recorded honestly rather than papered over. Two of the eight
welds — mediation/provisioning and threshold-distance — are filed as
**candidate bridges**: the implication is proved, and its hypothesis is exactly
the datum the missing surface would supply. Neither is filed as an instance, and
no naming resemblance was treated as an identification.

---

## 1. The principle

> **Completeness is over a declared carrier, and verification lifts to
> universality only with actual exhaustiveness evidence.**

Three consequences are theorems, not conventions:

* `Integration.DeclaredCarrier.determinesOn_not_determines` and its adequacy
  restatement `RealisationAdequacy.adequateOn_not_adequate` — sufficiency on a
  declared carrier does not transfer to the ambient type;
* `RealisationAdequacy.adequate_of_adequateOn_exhaustive` — the *only* licensed
  upgrade, whose second hypothesis is a record `Exhaustive D` carrying the proof
  `∀ s, D s`;
* `RealisationAdequacy.flag_does_not_give_exhaustive` — a `Bool` field asserting
  coverage is compatible with a carrier that is not exhaustive, so setting it is
  a declaration and never evidence. This is registry row 69, filed as an
  `openSocket`.

## 2. Owner one: consumer-indexed realisation and adequacy

The shape is a source `S`, a representation `R`, a realisation `X`, and — per
consumer `c` — an observation `observe : X → Obs c` and a question
`demand : S → Ans c`. Four notions are kept apart, and each is the existing
`Integration.CoordinateSufficiency.Determines` of a composite; no new
factorisation or determination notion is introduced.

| notion | meaning |
|---|---|
| `RepresentationAdequate P c` | the representation answers the question |
| `RealisationAdequate P c` | the realised state answers it — the *mediator* level |
| `AdequateFor P c` | the consumer's own observation of the realised state answers *its* question |
| `AdequateGlobally P cs` | every consumer in a declared family is adequate |

Proved:

* `adequate_chain` — adequacy propagates **upstream and only upstream**:
  consumer ⟹ realisation ⟹ representation;
* `representation_not_realisation`, `realisation_not_consumer` — both converses
  fail, with explicit witnesses, so the stages are genuinely distinct;
* `adequateFor_not_transfers` — **`AdequateFor c₁` does not imply
  `AdequateFor c₂`**: one pipeline, one observation, two consumers, one adequate
  and one not;
* `adequate_of_finer_observation` — refining the observation preserves adequacy;
* `adequateFor_of_exhaustiveFamily` — adequacy for a listed consumer family
  upgrades to adequacy for every consumer of interest exactly when the family is
  exhaustive of them, and `adequateGlobally_not_universal` shows that without
  that exhaustiveness it does not.

## 3. Owner two: the collision owner

`Collision P C` packages a separated collided pair: `left ≠ right`,
`P left = P right`, `C left ≠ C right`. Its theorem is stated once, in three
equivalent phrasings (`not_determines`, `not_refines`, `no_reading`), and is
closed under post-processing of the observation (`post`) and under injective
post-processing of the consumer (`mapConsumer`).

The four families the corpus had been proving separately are **constructions of
a `Collision`**, not four theorem families:

| family | construction | generality |
|---|---|---|
| aggregation | `sumCollision` | any additive commutative monoid |
| coordinate deletion | `Collision.ofEssential` | any dependent product; `essential_of_deleteCoord_collision` is the converse, so essentiality *is* deletion collision |
| scalarisation | `scalarCollision` | **every** weight vector: no choice of weights repairs it |
| marginalisation | `marginalCollision` | two joints with equal marginals |

`four_families_one_owner` collects the four conclusions; each component's proof
is the owner applied to the corresponding constructor.
`nonempty_collision_of_not_injective` shows that non-injectivity of the
observation is exactly the owner's hypothesis when the consumer is the state.

## 4. Owner three: separability and contrast

`marginal C w a = ∑ b, w b * C a b` and `contrast C w a a'` are defined for an
arbitrary first coordinate, an arbitrary finite second coordinate and values in
an arbitrary field; weightings are required only to sum to one, so signed
reweightings are covered too. Separability is the existing
`CoordinateSufficiency.Separable`.

* `separable_contrast_invariant` — **the owner theorem**: a separable consumer's
  contrast does not depend on the weighting;
* `not_separable_of_contrast_ne`, `not_separable_of_contrast_reversal` — the
  contrapositives; a sign reversal is a proof of interaction;
* `separable_no_reversal` — the positive companion;
* `separable_iff_rectangle` — the pointwise characterisation, so a lane may
  supply either a rectangle violation or a reversal;
* `marginalisation_contrast_is_instance`,
  `marginalisation_invariance_is_instance` — the existing `Bool`/`ℚ` convex
  development in `Integration.Marginalisation` is **identified as an instance**
  of the owner rather than left as a parallel family.

Three witnesses in three shapes — a Simpson-type pooled reversal, a trajectory
pair whose ordering flips with the horizon weighting, and a multiplicative
(contextual/intersectional) product — are all closed by the same theorem
(`three_shapes_one_owner`).

## 5. Owner four: language-indexed reachability

`ReachableIn S L` is *defined* as the existing
`Integration.ReachabilityBarrier.Reachable` of `restrict S L`, so there is no
second reachability relation in the tree.

* `reachableIn_mono` — `L₁ ⊆ L₂` and `Reachable_{L₁} x y` give
  `Reachable_{L₂} x y`, with the inclusion an explicit hypothesis;
* `not_reachableIn_of_invariant` — the only general route to a barrier, relative
  to the declared language;
* `unreachability_does_not_transfer` — **the retained negative**: the general
  transfer of *un*reachability, quantified over all systems and all inclusions,
  is false;
* `barrier_needs_the_language` — the invariant argument is itself
  language-relative: the same invariant fails once the language grows;
* `BarrierReport` — the honest packaging of a barrier claim: the record cannot
  be built without the language, the invariant and the preservation proof.

`LevelIIWelds.weld_counter_is_language_indexed` proves that the corpus's counter
system under a declared language *is* the owner's language-indexed reachability,
for every language and every pair of states, so registry rows 55 and 56 are
instances of this owner.

## 6. The welds

| # | consumer | owner | class | Lean |
|---|---|---|---|---|
| 61 | formalisation/reconstruction (the corpus's flattening) | consumer-indexed adequacy | `negativeResult` | `weld_reconstruction_instance`, `weld_reconstruction_loss_is_at_realisation` |
| 62 | mediation / provisioning | realisation (mediator) adequacy | `candidateBridge` | `weld_mediator_bridge`; in-tree instance `weld_mediator_instance` |
| 63 | threshold-distance / trajectory comparison | interaction | `candidateBridge` | `weld_threshold_bridge`; in-tree instances `weld_threshold_instance`, `weld_product_instance` |
| 64 | early-learning / counterfactual exposure | hidden-coordinate essentiality | `negativeResult` | `weld_hidden_coordinate_essential`, `weld_hidden_deletion` |
| 65 | Pareto planning | scalarisation collision and non-descent | `negativeResult` | `weld_pareto_scalarisation`, `weld_scalar_descent_is_not_dominance` |
| 66 | selective decision | action/readout non-invertibility | `negativeResult` | `weld_action_not_invertible`, `weld_action_readout` |
| 67 | atlases | declared-carrier completeness | `candidateBridge` | `weld_atlas_bridge`; negative `weld_atlas_flag_is_not_evidence` |
| 68 | admissible reachability | language-relative reachability | `negativeResult` | `weld_counter_is_language_indexed`, `weld_reachability_monotone`, `weld_unreachability_negative` |
| 69 | `Bool` coverage/exhaustiveness fields | exhaustiveness evidence | `openSocket` | `flag_does_not_give_exhaustive` |

Two details worth stating plainly:

* Weld 64 re-coordinatises the corpus's situated-exposure record onto a
  two-coordinate Boolean product, and the re-coordinatisation is **proved
  surjective** (`exposureOf_surjective`), so the encoding drops nothing; the
  intervention-label carrier has one element.
* Weld 66 is the same failure that row 45 states in the corpus's own vocabulary.
  It is filed again here because the *proof* is now the collision owner applied
  to a datum, and the mediator form — no reading of the action recovers the
  direction — comes with it for free.

`welds_are_owner_applications` collects the eight domain-lane facts whose proofs
are owner applications.

## 7. Dependency and provenance map

```
CoordinateSufficiency (Determines, Separable, Essential, FactorsOn)
   │
   ├── ContextIndexedRole ──────────────┐
   ├── DeclaredCarrier (DeterminesOn) ──┤
   │                                    ▼
   │                          RealisationAdequacy ◀── owner 1
   │                                    │
   ├── FactorisationCollision ◀── owner 2
   │        (aggregation, deletion, scalarisation, marginalisation)
   │
   ├── Marginalisation ──▶ SeparabilityContrast ◀── owner 3
   │
   └── ReachabilityBarrier ──▶ LanguageReachability ◀── owner 4
                                        │
   SelectiveDecision, CounterfactualEffect, ParetoOutcome
                                        │
                                        ▼
                                  LevelIIWelds ──▶ SewingRegistry rows 61–69
                                                     └─▶ Integration, AxiomAudit
```

No arrow in that diagram is a naming resemblance: each is an `import` plus a
theorem in the downstream module that consumes the upstream one.

## 8. Bookkeeping, rebuilt

* `Integration.lean` and `Integration/AxiomAudit.lean` import all five new
  modules; the audit prints the axiom dependencies of **every audited result**
  of the spine, and each one uses only `propext`, `Classical.choice`,
  `Quot.sound` (many use a strict subset). There is no project `axiom`, no
  `@[implemented_by]`, no `native_decide`, and no `sorry` in any build-target
  file.
* The registry census is now machine-checked rather than hand-maintained:
  `kindCensus` computes the per-class counts, `kinds_exercised` fixes them,
  `registry_length` the total, and `census_total` proves the class counts sum to
  the row count — so a row added without a class, or double-counted, breaks the
  build. `negatives_and_sockets_majority` states the headline in the robust
  form (a majority) rather than as a brittle hand count.
* `TOE_SEWING_MAP.md` §5 now quotes those compiler-evaluated numbers and points
  at this report for rows 61–69.

## 9. Frontier: the exact remaining obligations

1. **Discharge weld 62 from a corpus surface.** The bridge needs a
   `Collision P.state c.demand` for a provisioning pipeline in the tree. Owed:
   the surface itself. Status: absent from this repository.
2. **Discharge weld 63 from a corpus surface.** The bridge needs two weightings
   with opposite-signed contrasts for a threshold or trajectory consumer defined
   in the corpus. Owed: the surface. Status: absent.
3. **Discharge weld 67 for a named atlas.** The bridge needs
   `ExhaustiveOn l (fun _ => True)` for an actual atlas enumeration. The corpus
   atlases explicitly decline to claim it, so the honest expectation is that
   this obligation stays open and the atlases keep their disclaimers.
4. **Generalise the adequacy owner past `Type`.** `Pipeline`, `ConsumerSpec` and
   the `Determines` they reuse live in `Type`; nothing in the mathematics needs
   that, and a universe-polymorphic restatement would let the owner apply to
   dependent consumer families.
5. **A consumer index with genuine exhaustiveness evidence.** `ExhaustiveFamily`
   is stated and used, but no corpus lane yet supplies a family together with
   the proof that it lists every consumer of interest.
6. **Agda side.** No Agda checker ran here. Every Agda-side claim in the
   registry remains `agdaNotChecked`, proved row by row by
   `no_row_claims_agda_typechecked`.

## 10. Claim boundaries

Nothing in this round is a claim about people, institutions, provisioning,
learning, planning, markets, physics or biology. The owners are theorems about
functions between arbitrary types; the welds are theorems about finite label
types, Boolean products, `ℚ`-valued consumers and a counter on `ℕ`. Where a
domain word appears in a name it names a carrier, not a phenomenon, and the
claim boundary field of every registry row says so.
