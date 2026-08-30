# Level-III probe: claim transport, and why it did not create a fifth owner

**Tranche question.** Level II asks *what information does this representation
preserve?*  This tranche asked the next question — *when may a valid claim be
transported across representations, consumers, authorities or stages?* — under
a strict rule: **do not define Level III in advance**; search instead for
compositions of already-good Level-II objects that fail, and only introduce a
new generic object if at least three source-exact lanes require the same extra
structure.

**Verdict: outcome A.** Every composition failure reached in this tranche
reduces to the four frozen owners. The missing warrant is, in each lane, an
instance of the existing determination owner applied to the downstream
consumer's question pulled back along the upstream stage; its failure is
literally the existing `Collision` datum. **No fifth owner was added, no
`Licensed` relation was defined, and no Level-II definition was changed.**

One genuinely new *shape* did appear, and it is stated and proved rather than
generalised: **negative claims do not compose either**
(`barriers_do_not_compose`, with a source-exact instance).

Build status: full `lake build` succeeds (8300 jobs, no errors); no `sorry`;
every result in the axiom audit depends only on `propext`, `Classical.choice`,
`Quot.sound`. No Yang–Mills or Navier–Stokes material was read or referenced.

---

## 0. What was frozen

The four Level-II owners and the pipeline theorem were treated as fixed:

| owner | module |
|---|---|
| `RealisationAdequacy` | `Lean/Integration/RealisationAdequacy.lean` |
| `FactorisationCollision` | `Lean/Integration/FactorisationCollision.lean` |
| `SeparabilityContrast` | `Lean/Integration/SeparabilityContrast.lean` |
| `LanguageReachability` | `Lean/Integration/LanguageReachability.lean` |
| pipeline / repair dichotomy | `Lean/Integration/PipelineAdequacy.lean` |

None of these files was edited in this tranche. Nothing was added to the sewing
registry, so the census, the ledger and `ledger_covers_outstanding` are
unchanged.

---

## 1. The generic analysis — `Integration.ClaimTransport`

Two locally valid arrows `S --r₁--> M --r₂--> N`, an intermediate consumer with
question `q₁ : S → A₁`, a downstream consumer whose question `qM : M → A` is
stated in the *intermediate representation's own language*, and a final
question `q : S → A` about the source.

| statement | theorem |
|---|---|
| local adequacy does not compose | `local_claims_do_not_compose` |
| the missing piece, named | `Warrant r₁ qM q := Determines (qM ∘ r₁) q` |
| the warrant licenses the composite | `transport_of_warrant` |
| and is necessary when `qM` refines `r₂` | `warrant_of_transport_of_refining` |
| transport forces upstream preservation | `transport_forces_upstream` |
| upstream preservation is **not** sufficient | `upstream_determination_not_sufficient` |
| a warrant forces upstream preservation | `warrant_forces_upstream` |
| hence one first-stage collision kills *every* warrant | `no_warrant_of_not_upstream` |
| the warrant is a determination claim | `warrant_is_a_determination` |
| its failure is the collision datum | `warrant_failure_is_a_collision`, `no_collision_of_warrant` |
| the equivalence-relation reading | `sim`, `determines_iff_sim_le` |
| `x ∼_{C₁} y` while `x ≁_{C₂} y` | `sim_not_transitive_across_consumers` |
| **negative claims do not compose** | `barriers_do_not_compose` |
| the direction that *is* licensed | `barrier_transports_upstream` |
| three stages, one warrant per boundary | `three_stage_transport`, `three_stage_needs_every_warrant` |

The classification line is `warrant_is_a_determination`: the warrant is
*definitionally* `Integration.CoordinateSufficiency.Determines`. That is the
whole negative Level-III result — naming the warrant does not create an object.

---

## 2. Lane F — formalisation: source → mirror → checked theorem

**Specimen.** `Agda/DASHI/Education/EarlyLearningCounterfactualHeterogeneityExact.agda`,
the corpus's one recorded transcription hazard: `counterfactualRelativeEffect`
is written with left-hand sides that are *defined names*, not constructors.

The model in `Integration.ClaimTransportLanes` §1 keeps exactly the distinction
that matters: a `SourceText` is a visible clause table **plus** the scope status
of its left-hand-side head names; `transcribe` records only the former.

| statement | theorem |
|---|---|
| both readings present the same visible table | `transcription_forgets_head_status` |
| the readings are different objects | `hazard_readings_distinct` |
| a mirror cannot settle elaboration | `mirror_cannot_settle_elaboration` |
| the failure as the owner's datum | `elaboration_collision` |
| **A + B does not give C** | `A_and_B_do_not_give_C` |
| the same, unwrapped | `transcription_does_not_separate_the_readings` |
| no downstream consumer supplies the warrant | `no_warrant_in_the_formalisation_lane` |

`A_and_B_do_not_give_C` is stated as the independence it is: across the two
readings the Lean-side claims `A` (the mirror builds) and `B` (it presents the
visible surface) are *equivalent*, while `C` (the source elaborates) is not. The
hypothesis of the sensitive theorems is precisely the recorded hazard — that the
elaboration verdict depends on the scope status. **No Agda checker was run**,
and none of these theorems asserts what Agda does.

*Obstruction:* a determination failure. *Missing warrant:* a checker result —
an evidence-supplying arrow, not a theorem about the mirror.

---

## 3. Lane A — authority: content ≠ competence ≠ permission

**Specimens**, transcribed in the new mirror `Lean/AgdaMirror/AuthorityRoutes.lean`:

* `DASHI/Promotion/ExplanationAuthorityBoundaryCore.agda` — the six-row route
  table `canonicalExplanationRows` with its four use flags;
* `DASHI/Culture/CulturalProvenanceBoundaryCore.agda` — `ProvenanceRow`
  (including `permissionOrAuthorityClaimed`) and the `boundaryHolds` field with
  its companion pin;
* `DASHI/Philosophy/CulturalProvenanceAdapter.agda` — `CulturalApplicationPromotion`,
  three authority receipts next to a free `representationPromoted : Bool`.

Facts about the transcribed table (mirror side):

| statement | theorem |
|---|---|
| the table has one row per route | `canonicalRows_eq_map`, `canonicalRows_length` |
| no route licenses two of the three strong uses | `no_route_licenses_two_strong_uses` |
| each strong use has exactly one route | `strong_uses_are_single_route` |
| guiding and authority are incomparable | `guide_and_authority_are_incomparable` |
| **`x ∼_{guide} y` while `x ≁_{proof} y`** | `guide_agrees_proof_differs` |
| the permission flag is free of the content fields | `permission_flag_free` |
| `boundaryHolds` is pinned, hence constant | `boundaryHolds_constant` |
| and cannot report a violation | `boundaryHolds_does_not_summarise` |
| the canonical boundary has an empty row list | `canonicalBoundary_rows_empty` |
| receipts do not determine the promotion | `receipts_do_not_determine_promotion` |
| and may be vacuous | `vacuous_receipts_admit_promotion` |

Classification (Integration side, `ClaimTransportLanes` §2):

| statement | theorem |
|---|---|
| content ⇏ permission | `content_does_not_determine_permission` |
| the pinned flag determines nothing | `boundaryHolds_determines_nothing` |
| receipts ⇏ promotion | `receipts_do_not_determine_promotion` |
| a licence does not transport between uses | `guide_licence_does_not_transport_to_proof` |
| the licence is a **declared** coordinate | `status_determines_the_licences` |
| and the four statuses are distinguishable by it | `licences_separate_the_statuses` |
| the lane, summarised | `authority_lane_is_a_table_plus_collisions` |

**Is an irreducible `Licensed(a, c, u)` forced?** No. What the corpus supplies
is a table indexed by a *declared status*: `status_determines_the_licences`
shows the whole licence vector is a function of that declared field, and
nothing about the content of a claim enters. Every negative in the lane is a
determination failure, i.e. the existing collision owner. So the honest reading
is: authority here is **declared licence data plus Level-II collisions**, not a
new relation. `Licensed` was therefore *not* defined.

---

## 4. Lane E — empirical: measurement → aggregate → outcome

**Specimen.** `DASHI.Core.SocioEcologicalFeedbackExact`, via the existing mirror
(`AgdaMirror.NonFactorabilityKernels.SocioEcologicalFeedback`) and the existing
weld (`Integration.SourceExactWelds.Provisioning`).

| statement | theorem |
|---|---|
| the measurement answers its own question | `measurement_adequate_for_its_own_consumer` |
| every aggregate answers its own question | `aggregate_adequate_for_its_own_consumer` |
| **no rule on the plan score predicts the outcome** | `no_policy_rule_on_the_plan_score_predicts_the_outcome` |
| the obstruction, as the owner's datum | `empirical_collision` |
| no downstream consumer supplies the warrant | `no_warrant_in_the_empirical_lane` |

*Obstruction:* a determination failure, already owned; the repair is
representational, never computational (`PipelineAdequacy.repair_dichotomy`).

---

## 5. Lane N — entitlement: transporting a *negative* claim

**Specimen.** `DASHI/Education/EarlyLearningEntitlementRouteSeparationExact.agda`,
transcribed in the new mirror `Lean/AgdaMirror/EntitlementRoutes.lean`. The Agda
module proves two non-factorability results in a row and stops:

* the entitlement reading does not determine the delivery route;
* the delivery route does not determine the professional floor.

The tempting global inference — *therefore the entitlement reading does not
determine the professional floor* — is **false on the module's own carrier**:

| statement | theorem |
|---|---|
| barrier 1 (the corpus's own) | `entitlement_does_not_determine_route` |
| barrier 2 (the corpus's own) | `route_does_not_determine_floor` |
| the two readings are the same function | `entitlement_eq_floor` (mirror) |
| hence the composite claim is refuted | `entitlement_determines_the_floor` |
| the three together | `corpus_barriers_do_not_compose` |
| every field of the boundary record is pinned | `boundary_fields_are_pinned` (mirror) |

This is the sharpest specimen of the tranche: a *refutation* is a claim, and
chaining refutations across a stage boundary is not licensed. The only always-
licensed direction is `barrier_transports_upstream` (a barrier survives
composition **downstream**, never upstream).

---

## 6. The registry as a transition system — `Integration.PromotionDiscipline`

The frontier extractor already says what each open row is waiting for. This
module adds *which evidence permits which transition*, and proves the negative
entries rather than declaring them.

`EvidenceKind.mayPromoteTo`, the declared table:

| evidence | may promote to |
|---|---|
| `namingResemblance` | *nothing* |
| `sharedShapePredicate` | `structuralAnalogue` |
| `booleanCoverageDeclaration` | *nothing* |
| `exactSourceCarrier` | `exactInstance` |
| `inhabitingTheorem` | `exactInstance` |
| `enumerationCompleteness` | `exactInstance` |
| `collisionWitness` | `negativeResult` |
| `agdaTypecheckResult` | *nothing* (changes validation status, not class) |

| statement | theorem |
|---|---|
| a shared shape gives no equivalence of carriers | `shared_shape_gives_no_transport` |
| hence no `Transport` | `shared_shape_gives_no_transport_structure` |
| **naming resemblance cannot reach `exactInstance`** | `naming_resemblance_cannot_promote_to_exactInstance` |
| a shared shape stops at `structuralAnalogue` | `shared_shape_reaches_only_structuralAnalogue` |
| **a Boolean coverage declaration discharges no exhaustiveness obligation** | `coverage_flag_cannot_discharge_exhaustiveness`, `coverage_flag_promotes_nothing` |
| the contrasting positive: a decided enumeration does | `enumeration_completeness_does_promote` |
| promotion never lands in an open class | `promotion_never_lands_in_an_open_class` |
| an Agda checker result promotes nothing | `agda_typecheck_promotes_nothing` |
| **every live ledger entry names a licensed transition** | `ledger_transitions_are_licensed` |
| and every entry is actionable | `ledger_evidence_is_actionable` |

`ledger_transitions_are_licensed` is machine-checked against the live
`obligationLedger`: a ledger entry claiming an unlicensed promotion breaks the
build.

---

## 7. Dependency / provenance map

Each arrow is a Lean `import` plus a named theorem.

```
Agda/DASHI/Promotion/ExplanationAuthorityBoundaryCore.agda   (read-only source)
Agda/DASHI/Culture/CulturalProvenanceBoundaryCore.agda       (read-only source)
Agda/DASHI/Philosophy/CulturalProvenanceAdapter.agda         (read-only source)
        │  transcription (no Agda check)
        ▼
Lean/AgdaMirror/AuthorityRoutes.lean
        │  import
        ▼
Lean/Integration/ClaimTransportLanes.lean  §2  ── content_does_not_determine_permission
        ▲                                          guide_licence_does_not_transport_to_proof
        │  import                                  status_determines_the_licences
Lean/Integration/ClaimTransport.lean       ── Warrant, no_warrant_of_not_upstream
        ▲  import
Lean/Integration/PipelineAdequacy.lean     (frozen owner: collisions, repair dichotomy)

Agda/DASHI/Education/EarlyLearningEntitlementRouteSeparationExact.agda
        │  transcription (no Agda check)
        ▼
Lean/AgdaMirror/EntitlementRoutes.lean ──▶ ClaimTransportLanes §4 ── corpus_barriers_do_not_compose

Agda/DASHI/Education/EarlyLearningCounterfactualHeterogeneityExact.agda
        │  clause table only (the hazard)
        ▼
ClaimTransportLanes §1 ── A_and_B_do_not_give_C

AgdaMirror.NonFactorabilityKernels.SocioEcologicalFeedback
        │  existing mirror, existing weld
        ▼
Integration.SourceExactWelds.Provisioning ──▶ ClaimTransportLanes §3

Integration.SewingRegistry → Integration.OutstandingObligations
        │  import
        ▼
Integration.PromotionDiscipline ── ledger_transitions_are_licensed
```

Aggregates updated: `Lean/Integration.lean` (item 49) and
`Lean/Integration/AxiomAudit.lean` (+63 `#print axioms` lines).

---

## 8. Honest frontier: exactly what remains

1. **The elaboration hypothesis is a hypothesis.** Every theorem in lane F that
   mentions elaboration takes `hsens` — that the verdict differs between the two
   readings — as an assumption. Discharging it requires an Agda toolchain, which
   this environment does not have. Nothing here asserts that the Agda module
   does or does not elaborate.
2. **The authority licence table is data.** `status_determines_the_licences` is a
   fact about the transcribed table, not a derivation of any licence. If a corpus
   surface ever *derives* a licence from evidence (rather than declaring it),
   that would be the first genuine candidate for a `Licensed` relation. None was
   found.
3. **`representationPromoted` and `permissionOrAuthorityClaimed` remain free
   `Bool` fields** in the corpus. The Lean side proves they are free; pinning
   them needs a corpus theorem, which does not exist.
4. **`MayPromote`'s positive entries are declarations.** Only the three negative
   entries are proved (§6). A positive entry says the evidence is *of the kind*
   the target class demands; the witness must still be supplied.
5. **16 registry rows remain open**, unchanged by this tranche; the ledger and
   its proofs are untouched, and now additionally checked against the promotion
   table.
6. **The `Type → Type u` generalisation of the owners** was again not needed and
   not done.

**Not claimed.** No physical, empirical, educational, cultural, institutional or
policy claim; no theory-of-everything claim; no statement about what any Agda
module does. Every carrier in the new modules is a finite label type, `Bool`,
`String`, `ℕ` or `Prop`.

---

## 9. Stop condition

The tranche was to end in one of three outcomes:

* **A — all apparent composition problems reduce to Level II.** ← *this one.*
* B — a common claim-transport obstruction appears in 3+ independent lanes and
  is not expressible by the owners.
* C — different lanes exhibit genuinely different obstructions.

Four lanes were tested. Three (formalisation, authority, empirical) exhibit the
*same* obstruction — a `Collision` at the first boundary
(`three_lanes_one_obstruction`) — and in each of them no downstream consumer
supplies the warrant (`every_lane_lacks_a_warrant`). Because that common
obstruction *is* an existing owner, this is outcome A and not outcome B: the
recurrence strengthens Level II rather than justifying a Level-III owner.

The fourth lane adds a shape Level II had not previously stated — that a
refutation also needs a warrant to travel — but it, too, is expressed entirely
in the determination vocabulary (`barriers_do_not_compose`,
`barrier_transports_upstream`), so it is a new *theorem*, not a new owner.
