# Evidence governance round: promotion receipts, drift, falsification, and prediction

**Round question.** Not "can we find a Level III?" but *can unsupported epistemic
promotion be made mechanically impossible, without mistaking the control system
for evidence itself?*

Semantic-owner invention was frozen for this round: **no fifth generic owner was
added**, and the four Level-II owners, the pipeline theorem, the sewing registry,
the obligation ledger and the Level-III probe files were not edited (verified by
`git diff` against the round's base commit). Everything below is new material
that sits *on top* of them.

Build status: full `lake build` succeeds (8 308 jobs, no errors); no `sorry`,
`admit`, project `axiom`, `@[implemented_by]` or `native_decide`; the axiom audit
(818 `#print axioms` checks) reports only `propext`, `Classical.choice`,
`Quot.sound`, many on strict subsets. No Yang–Mills or Navier–Stokes file was
read, referenced or modified.

One build fix was required before anything else: the `AgdaMirror` library glob
had regressed to `AgdaMirror.*`, which pulls in the root aggregate importing the
excluded Yang–Mills mirror. It is restored to `AgdaMirror.+`, matching its own
in-file comment.

---

## 0. The architectural centre

```
corpus source
  → mirror / exact carrier          (provenance + drift guard, §4)
  → Level-II owner                  (frozen)
  → weld                            (frozen)
  → registry obligation             (frozen)
  → evidence-gated promotion        (new, §2)
```

and, branching off the owner, the new prediction axis (§7):

```
Level-II owner → prediction envelope → epistemic status → propagation boundary
```

---

## 1. Lane 1 — Lean/Agda claim-transport reconciliation

**Finding, stated first: the cited Agda module is not in this cutset.** A
whole-tree case-insensitive search for `claimtransport`, and for the bridge
instance's name, returns no Agda file; the three archived tarballs contain none
either. Nothing was transcribed from it, and no claim is made about its
contents or whether it elaborates.

What *can* be done without the source is done in
`Lean/Integration/ClaimTransportGeometry.lean`: state the described geometry as
an **interface** and prove that any two developments satisfying it agree.

| statement | theorem |
|---|---|
| factorisation through the retained representation = determination | `factors_iff_determines` |
| non-descent blocks transport | `nonDescent_blocks_transport` |
| and non-descent is the *only* obstruction | `not_factors_iff_nonempty_collision` |
| the probe's warrant is this factorisation, pulled back | `warrant_iff_factors_pullback` |
| **any two formulations of the interface agree** | `two_formulations_agree` |
| …and so do their obstructions | `obstructions_agree` |
| the existing owners inhabit the interface | `leanGeometry`, `interface_is_the_existing_owner` |
| any interface-satisfying development reduces to determination | `other_formulation_reduces_to_determination` |
| an exactly commuting translation square gives **no** semantic soundness | `commuting_square_does_not_give_soundness` |
| soundness for one coordinate does not transfer to another | `soundness_does_not_transfer_between_coordinates` |
| the three coordinates are independent | `square_soundness_fidelity_independent` |
| the citation is recorded as absent | `cited_source_absent` |

This converts reconciliation from a transcription task into a single checkable
condition: *does the other development satisfy the interface?* If it does, the
verdicts coincide by theorem. If it does not, the mismatch is exactly the
failing interface field. Postcondition met: correspondence is explicit, and the
concrete mismatch (an unresolvable citation) is exposed rather than papered over.

## 2. Lane 2 — promotion evidence hardening

`Lean/Integration/PromotionEvidence.lean` makes positive promotion
**evidence-indexed**. `Receipt : EvidenceKind → Type 1` gives, for each evidence
kind, the object that kind of evidence *is*; an `EvidencedPromotion` cannot be
constructed without inhabiting it.

Each receipt is proved to do its class's work: `carrier_receipt_discharges`,
`enumeration_receipt_universalises` (and `enumeration_receipt_is_exhaustive`),
`field_receipt_determines`, `collision_receipt_refutes`. The three hollow kinds
(naming resemblance, Boolean coverage declaration, Agda checker result) have
singleton receipt types — `hollow_receipts_are_always_available` — which is the
formal reason the promotion table licenses nothing for them, and
`no_promotion_on_hollow_evidence` proves no promotion can carry one.

The separation the round asked for is `licensed_shape_without_receipt` together
with `no_carrier_receipt_for_refuted_hypothesis`: the transition *shape* can be
licensed while the receipt provably cannot exist.

**The gate.** `promotionEvidenceLedger` classifies the positive transition of
each of the sixteen open rows; `mayExecute` is the executable gate; and
`gate_refuses_every_open_row` proves by computation that it returns `false` on
all sixteen. `promotion_evidence_coverage`: 0 evidence-backed, 16 declared-only,
16 total. The gate is *satisfiable* rather than vacuously closed:
`sspPromotion` is a complete `EvidencedPromotion` built on the corpus's decided
fifteen-element enumeration — but it belongs to an already-closed row, which is
why it does not move the coverage number.

Hard invariant preserved: `negative_transitions_unchanged`.

## 3. Lane 3 — free-field and Boolean sink audit

`Lean/Integration/FreeFieldAudit.lean` gives the generic vocabulary — `Free`
(settable independently of the content it reports) and `Pinned` (constant) —
and proves it is the existing owner in disguise:
`free_is_a_collision`, hence `free_not_determined` and
`free_field_not_recoverable` (no downstream function recovers a free field).
`pinned_field_cannot_report` is the negative sufficiency result for tautology
flags.

The bridge to the gate is `fieldReceipt_field_is_not_free`: **a free field can
never be the receipt that closes its own socket.**

Audited fields, with the theorem establishing each verdict:

| field | verdict | theorem |
|---|---|---|
| `ProvenanceRow.permissionOrAuthorityClaimed` | free | `permission_field_free`, `permission_not_determined` |
| `CulturalBoundary.boundaryHolds` | pinned tautology | `boundaryHolds_pinned`, `boundaryHolds_cannot_report` |
| `Promotion.representationPromoted` | free | `representationPromoted_free`, `representationPromoted_not_determined` |
| `CoverageClaim.claimsExhaustiveCoverage` | free | `coverage_flag_free` |
| `CoverageDeclaration.claimsExhaustive` | free | `claimsExhaustive_free` |
| DNA sheet flags, chemistry reachability flags, loom evidence status, Pareto boundary fields | free | registry rows 5, 15, 20, 53 |

`audit_census`: 8 free, 1 pinned, **0 evidence-carrying**, 9 total.
`every_free_field_is_exposed` proves the postcondition: no field is classified
free without a named negative result exposing it.

## 4. Lane 4 — mirror drift and transcription integrity

`scripts/mirror_drift.py` + `MIRROR_DRIFT_MANIFEST.json` +
`Lean/Integration/MirrorDrift.lean`.

The sixteen (mirror, source) pairs the Level-II/III spine actually consumes —
`MonsterOntos`, `NonFactorabilityKernels` (×5), `FibreAveraging` (×2),
`InteractionTables` (×3), `AuthorityRoutes` (×3), `EntitlementRoutes`, plus the
absent claim-transport citation — each carry a pinned SHA-256 prefix of the
source file. The script recomputes them from disk (`--update`, default check),
and `--verify-lean` compares them against the Lean table, so the Lean table
itself cannot go stale unnoticed.

Proved of the table: `every_consumed_mirror_has_provenance`,
`present_rows_have_a_digest`, `absent_rows_have_no_digest`, `digests_distinct`,
`drift_coverage` (16 pairs; 15 pinned; 1 absent) and `absent_source_is_recorded`
(the single absent row is exactly the Lane-1 citation).

**Scope.** This answers only "did the source surface we transcribed change?"
It is not an Agda typecheck and not a faithfulness statement. Faithfulness
remains open; the name-level and signature-shape audits in
`MIRROR_PROVENANCE.md` / `MIRROR_SIGNATURES.md` remain the honest upper bound.

## 5. Lane 5 — frontier leverage queue

`Lean/Integration/FrontierPriority.lean` derives the queue mechanically from the
obligation ledger: a row's obstruction comes from its typed missing evidence and
its band from the size of that obstruction's cohort (`bandOf`), proved by
`band_is_derived_from_cohort_size`.

| obstruction | rows | size | band |
|---|---|---:|---|
| free record field | 5, 11, 12, 15, 20, 37, 38, 53, 68 | 9 | high |
| missing corpus carrier | 16, 31, 43, 55, 61, 62 | 6 | medium |
| enumeration completeness | 66 | 1 | low |

`cohorts_partition` checks the three cohorts exhaust the sixteen rows, and
`high_band_is_the_free_field_cohort` identifies the top band.

**Priority is advisory, never authority**: `high_priority_rows_are_still_refused`
and `no_band_passes_the_gate` prove that no band passes the promotion gate, so
re-ranking the queue cannot close a row. The leverage claim is stated as a
theorem about receipts, not about the queue:
`free_field_rows_need_a_pinning_theorem`.

## 6. Lane 6 — deliberate falsification

`Lean/Integration/TransportFalsification.lean` attacks the negative verdict by
looking for transports that are *not* ordinary total functions.

| shape | verdict | reduction |
|---|---|---|
| partial map `X → Option M` | reducible | `definedness_is_determined`, `undefined_states_collide`, `partial_map_pair_reading` |
| relation-valued consumer `X → Z → Prop` | awkward but reducible (needs `funext`/`propext`) | `relational_consumer_reduces`, `relational_collision` |
| nondeterministic stage `X → Set M` | reducible | `nondeterministic_answers_determined`, `nondeterministic_transport`, `nondeterministic_obstruction` |
| context-indexed admissibility `X → K → Z` | reducible pointwise | `context_indexed_reduces`, `context_determination_does_not_transfer` |
| stage defined only on a declared carrier | reducible to `DeterminesOn` | `declared_domain_reduces`, `declared_domain_gap_is_strict` |

`no_irreducible_shape_found` and `irreducible_count = 0` are statements about the
five probed rows, **not** a proof that no irreducible transport exists. The
admission rule for a future Level III is unchanged: three independent
source-exact lanes with the same irreducible obstruction.

## 7. The prediction axis

Two new modules make prediction a first-class object without creating a
`PredictionSystem` layer.

**`Lean/Integration/PredictionEnvelope.lean`** — when determination fails the
honest output is a set, `Pred O C y = { C x | O x = y }`. The organising
theorem is `determines_iff_envelope_subsingleton`: *the existing determination
theory is the theory of point-identifiable predictions*, and the envelope is its
proper generalisation. Then: `refinement_narrows_envelope` and
`joint_evidence_contracts` (tightening), `contraction_can_be_strict`,
`envelope_image`, `envelope_not_subsingleton_of_collision` and its converse,
`no_algorithm_recovers_from_this_representation` and `no_post_processing_repairs`
(structural impossibility predictions),
`relational_prediction_without_point_prediction` (a comparison predicted when
neither side is), `aggregation_must_erase` (an impossibility prediction proved
by counting), and `experiment_must_separate_the_pair` — the negative result
naming the measurement that would close the envelope.

**`Lean/Integration/PredictionStatus.lean`** — five tiers, with `rank` read as
*distance from evidence* and explicitly not as quality. Propagation may weaken
or preserve status; it may strengthen only on a step carrying a **non-hollow
`Receipt`**, the very object of Lane 2. Proved:
`propagate_never_strengthens_without_receipt`, `hollow_receipt_is_a_no_op`,
`chain_rank_monotone`, **`no_epistemic_laundering`** (no receipt-free chain takes
a speculative analogy to a model-conditional prediction),
`no_receipt_free_route_to_proof`, `analogy_step_is_permanent_without_a_receipt`,
and the discriminating positive `receipt_may_strengthen`. Support cones are
computed, not declared (`status_is_computed_not_declared`,
`dropping_a_step_changes_the_status`), and a refutation does not reject the whole
cone (`refutation_does_not_reject_the_whole_cone`).

Search predictions get their own status: `search_precondition_is_necessary`
(searching where the structural precondition fails is wasted) and
`search_precondition_is_not_sufficient` (so it is a place to look, not a claim
that the phenomenon is there).

The antipattern battery (§5 of that file) formalises eight tests as generic
negatives — resemblance is not identity; encoding does not identify mechanism;
local success does not globalise; established quantities must be recovered;
identifiability is envelope width; out-of-sample measurements discriminate;
scope must name its consumer; rejection does not propagate to the cone. **The
historical labels in the module's prose are labels only**: every theorem is
about observation maps and consumers, and asserts nothing historical, physical
or empirical.

---

## 8. Round metrics

| metric | baseline | this round | direction |
|---|---|---|---|
| M₁ evidence-backed positive promotion fraction | not measured (positives were undifferentiated declarations) | **0/16 backed, 16/16 explicitly classified**, gate proved closed | ↑ (classification), unchanged (backing) |
| M₂ Level-II/III mirror provenance + drift coverage | name-level census only, no drift condition | **16/16 pairs with pinned provenance and a machine-checkable drift guard** | ↑ |
| M₃ promotion-relevant free fields explicitly classified | ad-hoc negatives | **9/9 classified; 8 free, 1 pinned, 0 evidence-carrying** | ↑ |
| M₄ high-centrality frontier obligations remaining | 16 unranked | **16, partitioned 9 / 6 / 1 with the band derived** | unchanged in count, now ranked |
| M₅ new generic semantic owners | 4 | **4 (zero added)** | = 0 ✔ |
| M₆ irreducible transport counterexamples | 0 | **0 over five probed shapes** | reported, not minimised |

M₁'s numerator is honestly zero: no open row acquired evidence this round. What
changed is that a row can no longer *appear* promotable — the gate is a theorem,
not a convention.

## 9. Exact remaining obligations

1. **The sixteen open registry rows**, unchanged, now each with a band and an
   evidence classification. Nine need a theorem pinning a free field; six need a
   corpus carrier inhabiting a proved implication; one needs enumeration
   completeness.
2. **Agda elaboration** — no Agda toolchain exists here. No mirror is claimed to
   typecheck; the drift guard is a byte-level check only. The recorded
   transcription hazard (an education module whose clause heads are defined names
   rather than constructors) is still unresolved.
3. **The absent citation** — `FormalClaimTransportGeometryExact.agda` is cited in
   the surrounding correspondence and is not in this cutset. Until it is
   supplied, Lane 1's reconciliation stands as a conditional interface theorem.
4. **Faithfulness of the mirrors** — provenance and drift are covered;
   statement-level faithfulness is not, and cannot be here.
5. **Prediction axis, steps 3–6 of the stated progression** — probability,
   intervals and empirical updating are deliberately *not* added; the envelope
   geometry is in place and can carry them later without change.

## 10. Claim boundaries

Every theorem cited here is a Lean statement about Lean definitions over `ℕ`,
`Bool`, `ℚ`, `Set`, finite label types, or arbitrary types. Nothing here is a
physical, chemical, biological, educational, cultural, institutional, historical
or theory-of-everything claim; no registry row was promoted; no Agda module is
asserted to elaborate; and no result about Yang–Mills, Navier–Stokes or the
Riemann hypothesis is used or implied.
