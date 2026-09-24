import Integration.ClaimTransport
import Integration.SourceExactWelds
import Integration.CounterfactualEffect
import AgdaMirror.AuthorityRoutes
import AgdaMirror.EntitlementRoutes

/-!
# Three lanes of claim transport, tested against the four frozen owners

`Integration.ClaimTransport` shows, generically, that two locally valid arrows
need a **warrant** before their composite is valid, and that the warrant is
itself a `Determines` claim.  This file runs that test on three deliberately
different corpus lanes and asks, in each, whether the obstruction is anything
the four Level-II owners cannot already express.

| lane | stages | the composite claim under test |
|---|---|---|
| formalisation | Agda source → Lean mirror → checked theorem | "the Agda source elaborates" |
| authority | explanation route → licensed use → downstream reuse | "this content may be used here" |
| empirical | measurement → aggregate → realised outcome | "the plan score predicts the outcome" |
| entitlement | entitlement → delivery route → professional floor | "entitlement cannot fix the floor" |

## Findings

* **Formalisation.** `transcription_forgets_head_status`: the visible clause
  table of the corpus's one recorded transcription hazard is *literally the
  same* under both readings of its left-hand sides, so the mirror attests to
  both.  Hence `mirror_cannot_settle_elaboration`: for any elaboration verdict
  that is sensitive to the reading, the transcription does not determine it, and
  the failure is a `Collision`.  The three claims — the Lean object typechecks,
  it transcribes the visible surface, the Agda source elaborates — are separated
  by `A_and_B_do_not_give_C`.  *Obstruction: a determination failure.*
* **Authority.** `content_does_not_determine_permission`,
  `boundaryHolds_determines_nothing`, `receipts_do_not_determine_promotion` and
  `guide_licence_does_not_transport_to_proof` are all determination failures on
  transcribed corpus fields.  What the corpus adds beyond Level II is not a
  theorem but *data*: a six-by-four table of which route licenses which use.
  `authority_lane_is_a_table_plus_collisions` records exactly that split.
  *Obstruction: a determination failure, plus declared licence data.*
* **Empirical.** `no_policy_rule_on_the_plan_score_predicts_the_outcome`: for
  **every** rule reading the corpus's declared plan score, the realised outcome
  is not predicted.  *Obstruction: a determination failure.*
* **Entitlement (a fourth lane, and the sharpest one).** The corpus proves two
  non-factorability results in a row and stops.  `corpus_barriers_do_not_compose`
  shows that chaining them would produce a *false* claim: on the module's own
  carrier the entitlement reading and the professional-floor reading are the
  same function.  So a refutation is a claim that needs a warrant to travel
  too, and the only direction that is always licensed is
  `ClaimTransport.barrier_transports_upstream`.
* **Comparison.** `three_lanes_one_obstruction` exhibits the same datum — a
  `Collision` at the first boundary — in all three of the positive lanes, and
  `every_lane_lacks_a_warrant` states that in each of them *no* downstream
  consumer supplies the missing warrant.  **No lane required an
  object the frozen owners cannot express**, so this tranche does not create a
  Level-III owner.

Nothing here is a claim about education, culture, policy, ecology, or about
whether any Agda module typechecks.  Carriers are finite label types, `Bool`
and `Prop`.
-/

namespace Integration.ClaimTransportLanes

open Integration.CoordinateSufficiency
open Integration.FactorisationCollision
open Integration.ClaimTransport

/-! ## §1 The formalisation lane: source → mirror → checked theorem

The corpus's one recorded transcription hazard is
`DASHI/Education/EarlyLearningCounterfactualHeterogeneityExact.agda`, whose
`counterfactualRelativeEffect` is written with left-hand sides that are *defined
names*, not constructors:

```agda
counterfactualRelativeEffect higherCounterfactualExposure = adverseDirection
counterfactualRelativeEffect lowerCounterfactualExposure  = beneficialDirection
counterfactualRelativeEffect _                            = adverseDirection
```

The model below keeps exactly the distinction that matters: a source text is a
visible clause table **plus** the scope status of the head names in its
left-hand sides, and a transcription records only the former. -/

/-- The two readings a left-hand-side head name can have. -/
inductive HeadStatus
  /-- The name resolves to a constructor, so the clause is a real pattern. -/
  | constructorHead
  /-- The name is a defined name, so the clause's left-hand side is a variable
  binder. -/
  | definedNameHead
  deriving DecidableEq, Repr

open Integration.CounterfactualEffect in
/-- The visible clause table: the pairs (left-hand-side name, right-hand-side
value) a reader — or a transcriber — can see. -/
abbrev ClauseTable := List (String × EffectDirection)

open Integration.CounterfactualEffect in
/-- The three clauses of the corpus function, transcribed literally. -/
def hazardClauses : ClauseTable :=
  [ ("higherCounterfactualExposure", .adverseDirection)
  , ("lowerCounterfactualExposure", .beneficialDirection)
  , ("_", .adverseDirection) ]

/-- A source text: what is visible, plus the datum that decides how it
elaborates. -/
structure SourceText where
  /-- The visible clauses. -/
  table : ClauseTable
  /-- The scope status of the left-hand-side head names. -/
  heads : HeadStatus
  deriving DecidableEq

/-- What a mirror can record: the visible clauses only. -/
def transcribe (t : SourceText) : ClauseTable := t.table

/-- The corpus text read as if its heads were constructors — the reading the
Lean mirror `Integration.CounterfactualEffect` implements. -/
def hazardAsConstructors : SourceText := ⟨hazardClauses, .constructorHead⟩

/-- The same visible text with its heads read as defined names. -/
def hazardAsDefinedNames : SourceText := ⟨hazardClauses, .definedNameHead⟩

/-- **The transcription forgets the scope status.**  Both readings present the
same visible clause table, so a faithful transcription of the visible surface
attests to both. -/
theorem transcription_forgets_head_status :
    transcribe hazardAsConstructors = transcribe hazardAsDefinedNames := rfl

/-- The two source texts are nevertheless different objects. -/
theorem hazard_readings_distinct : hazardAsConstructors ≠ hazardAsDefinedNames := by decide

/-- **The mirror cannot settle elaboration.**  For any elaboration verdict that
depends on the scope status — which is precisely the recorded hazard — the
transcription does not determine it.  The hypothesis is the hazard; the
conclusion is that no theorem about the transcription can discharge it. -/
theorem mirror_cannot_settle_elaboration (elaborates : SourceText → Bool)
    (hsens : elaborates hazardAsConstructors ≠ elaborates hazardAsDefinedNames) :
    ¬ Determines transcribe elaborates :=
  not_determines_of_collision (x₁ := hazardAsConstructors) (x₂ := hazardAsDefinedNames)
    transcription_forgets_head_status hsens

/-- And the failure is the collision datum the owner uses. -/
def elaboration_collision (elaborates : SourceText → Bool)
    (hsens : elaborates hazardAsConstructors ≠ elaborates hazardAsDefinedNames) :
    Collision transcribe elaborates where
  left := hazardAsConstructors
  right := hazardAsDefinedNames
  distinct := hazard_readings_distinct
  collide := transcription_forgets_head_status
  separate := hsens

/-- The three claims that must not be conflated. -/
structure Attestation where
  /-- `A`: the Lean object typechecks. -/
  leanChecks : Prop
  /-- `B`: the Lean object transcribes the visible Agda surface. -/
  transcribesSurface : Prop
  /-- `C`: the Agda source itself elaborates. -/
  agdaElaborates : Prop

/-- The attestation a reading of the corpus text receives here: the Lean mirror
of this project builds (`A`), it presents the visible clause table (`B`), and
the source elaborates (`C`). -/
def attestation (elaborates : SourceText → Bool) (s : SourceText) : Attestation where
  leanChecks := True
  transcribesSurface := transcribe s = hazardClauses
  agdaElaborates := elaborates s = true

/-- **`A + B` does not give `C`.**  Stated as the independence it is: the two
readings of the corpus text receive the *same* `A` and the *same* `B` — the
mirror builds and presents the visible surface either way — while `C` differs.
So no proof can lead from `A ∧ B` to `C`. -/
theorem A_and_B_do_not_give_C (elaborates : SourceText → Bool)
    (hsens : elaborates hazardAsConstructors ≠ elaborates hazardAsDefinedNames) :
    ((attestation elaborates hazardAsConstructors).leanChecks ↔
        (attestation elaborates hazardAsDefinedNames).leanChecks) ∧
      ((attestation elaborates hazardAsConstructors).transcribesSurface ↔
        (attestation elaborates hazardAsDefinedNames).transcribesSurface) ∧
      ¬ ((attestation elaborates hazardAsConstructors).agdaElaborates ↔
        (attestation elaborates hazardAsDefinedNames).agdaElaborates) := by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  intro h
  refine hsens ?_
  cases hc : elaborates hazardAsConstructors <;> cases hd : elaborates hazardAsDefinedNames <;>
    simp_all [attestation]

/-- The same fact without the record wrapper: the transcription does not
separate the two readings, and the elaboration verdict does. -/
theorem transcription_does_not_separate_the_readings (elaborates : SourceText → Bool)
    (hsens : elaborates hazardAsConstructors ≠ elaborates hazardAsDefinedNames) :
    ∃ s t : SourceText,
      transcribe s = transcribe t ∧ elaborates s ≠ elaborates t :=
  ⟨hazardAsConstructors, hazardAsDefinedNames, transcription_forgets_head_status, hsens⟩

/-- **No warrant exists in this lane, for any downstream consumer.**  Whatever
question a downstream consumer asks of the transcription, it cannot license the
elaboration claim: the warrant would force the transcription to determine the
verdict, which the hazard refutes.  The warrant can therefore only be supplied
by running a checker — an *evidence-supplying arrow*, not a theorem about the
mirror. -/
theorem no_warrant_in_the_formalisation_lane (elaborates : SourceText → Bool)
    (hsens : elaborates hazardAsConstructors ≠ elaborates hazardAsDefinedNames)
    (qM : ClauseTable → Bool) : ¬ Warrant transcribe qM elaborates :=
  no_warrant_of_not_upstream (mirror_cannot_settle_elaboration elaborates hsens) qM

/-! ## §2 The authority lane: route → licensed use → downstream reuse -/

open AgdaMirror.AuthorityRoutes

/-- **Content does not determine permission.**  On the corpus's own
`ProvenanceRow`, the source name, the provenance kind and the replaceability of
the contribution leave the `permissionOrAuthorityClaimed` field free. -/
theorem content_does_not_determine_permission :
    ¬ Determines
        (fun p : ProvenanceRow => (p.sourceName, p.kind, p.replaceableByFormalEncoding))
        (fun p : ProvenanceRow => p.permissionOrAuthorityClaimed) := by
  obtain ⟨p, q, hn, hk, hr, hp⟩ := permission_flag_free
  refine not_determines_of_collision (x₁ := p) (x₂ := q) ?_ hp
  simp [hn, hk, hr]

/-- **The pinned boundary flag reports nothing.**  `boundaryHolds` is forced to
`true` by its own companion field, so it cannot distinguish a boundary that
forbids extraction from one that does not. -/
theorem boundaryHolds_determines_nothing :
    ¬ Determines (fun b : CulturalBoundary => b.boundaryHolds)
        (fun b : CulturalBoundary => b.noExtraction) := by
  refine not_determines_of_collision (x₁ := canonicalBoundary) (x₂ := permissiveBoundary)
    boundaryHolds_does_not_summarise.1 boundaryHolds_does_not_summarise.2

/-- **The receipts do not determine the promotion.**  The corpus's promotion
record places three authority receipts next to a free `Bool` verdict. -/
theorem receipts_do_not_determine_promotion :
    ¬ Determines
        (fun p : Promotion =>
          (p.adapter, p.sourceAuthorityReceipt, p.communityAuthorityReceipt,
            p.adaptationBoundaryReceipt))
        (fun p : Promotion => p.representationPromoted) := by
  obtain ⟨p, q, ha, hs, hc, hb, hr⟩ := AgdaMirror.AuthorityRoutes.receipts_do_not_determine_promotion
  refine not_determines_of_collision (x₁ := p) (x₂ := q) ?_ hr
  simp [ha, hs, hc, hb]

/-- **A licence does not transport between uses.**  Two routes of the corpus
table that agree on the guide licence disagree on the typed-proof licence, so
"may guide" carries no information about "is a typed proof". -/
theorem guide_licence_does_not_transport_to_proof :
    ¬ Determines (fun r : Route => licenses r .guide) (fun r : Route => licenses r .typedProof) :=
  not_determines_of_collision (x₁ := .narrativeGuide) (x₂ := .typedStructure)
    guide_agrees_proof_differs.1 guide_agrees_proof_differs.2

/-- **The licence is a declared coordinate, not a derived one.**  Across the
corpus's six-row table the declared `rowStatus` determines the whole licence
vector: nothing about the content of a claim enters.  Together with
`content_does_not_determine_permission` this is the honest answer to "is there
an irreducible `Licensed(a, c, u)` here?" — the corpus supplies a *table*
indexed by a declared status, and derives no licence from anything else. -/
theorem status_determines_the_licences :
    Determines (fun r : Route => (rowOf r).status) (fun r : Route => licenses r) := by
  unfold Determines; decide

/-- And the table is not degenerate: the four declared statuses give four
different licence vectors. -/
theorem licences_separate_the_statuses :
    Determines (fun r : Route => licenses r) (fun r : Route => (rowOf r).status) := by
  unfold Determines; decide

/-- **What the authority lane actually contains.**  Three determination failures
on transcribed corpus fields — each an instance of the collision owner — plus a
declared table of which route licenses which use, which is *data*, not a
theorem.  In particular the corpus never derives a licence from content; it
lists licences. -/
theorem authority_lane_is_a_table_plus_collisions :
    (¬ Determines
        (fun p : ProvenanceRow => (p.sourceName, p.kind, p.replaceableByFormalEncoding))
        (fun p : ProvenanceRow => p.permissionOrAuthorityClaimed)) ∧
    (¬ Determines (fun b : CulturalBoundary => b.boundaryHolds)
        (fun b : CulturalBoundary => b.noExtraction)) ∧
    (¬ Determines (fun r : Route => licenses r .guide)
        (fun r : Route => licenses r .typedProof)) ∧
    (∀ r : Route, ¬ ((licenses r .typedProof ∧ licenses r .empiricalSupport) ∨
      (licenses r .typedProof ∧ licenses r .institutionalAuthority) ∨
      (licenses r .empiricalSupport ∧ licenses r .institutionalAuthority))) :=
  ⟨content_does_not_determine_permission, boundaryHolds_determines_nothing,
    guide_licence_does_not_transport_to_proof, no_route_licenses_two_strong_uses⟩

/-! ## §3 The empirical lane: measurement → aggregate → realised outcome -/

open AgdaMirror.NonFactorabilityKernels.SocioEcologicalFeedback
open Integration.SourceExactWelds.Provisioning
open Integration.PipelineAdequacy

/-- The measurement stage of the corpus's socio-ecological surface: the declared
plan score. -/
abbrev measurement : World → StaticPlanScore := resourceObserver

/-- The realised outcome, the claim the policy lane wants. -/
abbrev outcome : World → Outcome := realisedOutcome

/-- The measurement stage is adequate for its *own* consumer: it answers the
question "what is the declared plan score?" exactly. -/
theorem measurement_adequate_for_its_own_consumer : Determines measurement measurement :=
  fun _ _ h => h

/-- Every aggregate rule downstream of the measurement is adequate for its own
consumer, too. -/
theorem aggregate_adequate_for_its_own_consumer {A : Type} (f : StaticPlanScore → A) :
    Determines f f := fun _ _ h => h

/-- **And the composite fails, for every rule.**  No function of the declared
plan score — no aggregate, no index, no policy rule — predicts the realised
outcome.  This is `no_computation_repair` applied to the corpus collision. -/
theorem no_policy_rule_on_the_plan_score_predicts_the_outcome :
    ¬ ComputationRepair measurement outcome :=
  no_computation_repair resourceCollision

/-- The empirical lane's obstruction, as the owner's datum. -/
def empirical_collision : Collision measurement outcome := resourceCollision

/-- **No warrant exists in the empirical lane either.**  For every downstream
consumer question about the plan score, the composite claim is unlicensed. -/
theorem no_warrant_in_the_empirical_lane (qM : StaticPlanScore → Outcome) :
    ¬ Warrant measurement qM outcome :=
  no_warrant_of_not_upstream (not_determines_of_collision empirical_collision.collide
    empirical_collision.separate) qM

/-! ## §4 A fourth lane: transporting a *negative* claim

`DASHI/Education/EarlyLearningEntitlementRouteSeparationExact.agda` proves two
non-factorability results in a row — the entitlement reading does not determine
the route reading, and the route reading does not determine the professional
floor — and stops there.  Chaining them is the tempting global inference, and it
is invalid on the module's own carrier. -/

/-- The corpus's `universalEntitlementCannotDetermineDeliveryRoute`. -/
theorem entitlement_does_not_determine_route :
    ¬ Determines AgdaMirror.EntitlementRoutes.universalEntitlement
      AgdaMirror.EntitlementRoutes.parallelFamilyRoute :=
  not_determines_of_collision
    (x₁ := AgdaMirror.EntitlementRoutes.Architecture.universalProfessional)
    (x₂ := AgdaMirror.EntitlementRoutes.Architecture.universalPlusParallelFamily)
    AgdaMirror.EntitlementRoutes.same_entitlement_different_routes.1
    AgdaMirror.EntitlementRoutes.same_entitlement_different_routes.2

/-- The corpus's `parallelFamilyOptionCannotDetermineProfessionalFloor`. -/
theorem route_does_not_determine_floor :
    ¬ Determines AgdaMirror.EntitlementRoutes.parallelFamilyRoute
      AgdaMirror.EntitlementRoutes.professionalFloor :=
  not_determines_of_collision
    (x₁ := AgdaMirror.EntitlementRoutes.Architecture.universalPlusParallelFamily)
    (x₂ := AgdaMirror.EntitlementRoutes.Architecture.substitutionaryExit)
    AgdaMirror.EntitlementRoutes.same_route_different_floor.1
    AgdaMirror.EntitlementRoutes.same_route_different_floor.2

/-- **And the composite claim is false.**  On the module's own three-element
carrier the entitlement reading *does* determine the professional floor — the
two readings are literally the same function. -/
theorem entitlement_determines_the_floor :
    Determines AgdaMirror.EntitlementRoutes.universalEntitlement
      AgdaMirror.EntitlementRoutes.professionalFloor := by
  rw [AgdaMirror.EntitlementRoutes.entitlement_eq_floor]
  exact fun _ _ h => h

/-- **A source-exact instance of `barriers_do_not_compose`.**  Two valid corpus
refutations whose composition is a refuted claim.  So a barrier is not
transported by chaining: the negative results of the corpus may be composed only
in the direction `barrier_transports_upstream` licenses. -/
theorem corpus_barriers_do_not_compose :
    ¬ Determines AgdaMirror.EntitlementRoutes.universalEntitlement
        AgdaMirror.EntitlementRoutes.parallelFamilyRoute ∧
      ¬ Determines AgdaMirror.EntitlementRoutes.parallelFamilyRoute
        AgdaMirror.EntitlementRoutes.professionalFloor ∧
      Determines AgdaMirror.EntitlementRoutes.universalEntitlement
        AgdaMirror.EntitlementRoutes.professionalFloor :=
  ⟨entitlement_does_not_determine_route, route_does_not_determine_floor,
    entitlement_determines_the_floor⟩

/-! ## §5 Comparison: is there anything Level II cannot say? -/

/-- **One obstruction, three lanes.**  In each lane the composite claim fails
for the same reason and with the same datum: a `Collision` of the first stage
against the final question.  The formalisation lane's collision is conditional
on the recorded hazard, which is the honest form — no checker was run. -/
theorem three_lanes_one_obstruction (elaborates : SourceText → Bool)
    (hsens : elaborates hazardAsConstructors ≠ elaborates hazardAsDefinedNames) :
    Nonempty (Collision transcribe elaborates) ∧
    Nonempty (Collision (fun r : Route => licenses r .guide)
      (fun r : Route => licenses r .typedProof)) ∧
    Nonempty (Collision measurement outcome) :=
  ⟨⟨elaboration_collision elaborates hsens⟩,
    ⟨{ left := .narrativeGuide
       right := .typedStructure
       distinct := by decide
       collide := guide_agrees_proof_differs.1
       separate := guide_agrees_proof_differs.2 }⟩,
    ⟨empirical_collision⟩⟩

/-- **And in every lane the missing warrant is a determination claim, which
fails.**  This is the negative Level-III result of this tranche: the warrant
that would license each composition is an instance of the existing owner —
the downstream consumer's question pulled back along the upstream stage — and
in each lane *no* choice of downstream consumer supplies it.  No lane produced
a warrant of a different shape. -/
theorem every_lane_lacks_a_warrant (elaborates : SourceText → Bool)
    (hsens : elaborates hazardAsConstructors ≠ elaborates hazardAsDefinedNames) :
    (∀ qM : ClauseTable → Bool, ¬ Warrant transcribe qM elaborates) ∧
    (∀ qM : Bool → Bool,
      ¬ Warrant (fun r : Route => licenses r .guide) qM (fun r : Route => licenses r .typedProof)) ∧
    (∀ qM : StaticPlanScore → Outcome, ¬ Warrant measurement qM outcome) :=
  ⟨no_warrant_in_the_formalisation_lane elaborates hsens,
    fun qM => no_warrant_of_not_upstream guide_licence_does_not_transport_to_proof qM,
    no_warrant_in_the_empirical_lane⟩

end Integration.ClaimTransportLanes
