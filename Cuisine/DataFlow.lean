import Mathlib
import Cuisine.Surfaces

/-!
# Cuisine layer 4: the promotion pipeline is fail-closed

Lean mirror of the promotion block of
`DASHI.Culture.Cuisine.CuisineDataFlowCore`: `SourceReceipt`, `SurfaceClaim`,
`ClaimRelation`, `PromotionPolicy`, `PromotionEvidence`, `PromotedClaim`,
`promote`, `recoverPromotionEvidence`.

The Agda header says "Promotion is proof-bearing and fail-closed".  The module
makes promotion proof-*bearing* — `PromotedClaim` carries its evidence — but it
never states or proves the fail-closed half.

New content proved here:

* `recover_promote` / `promotedSurfaceClaim_promote` — promotion loses no
  evidence (the round-trip laws);
* `isEmpty_promotedClaim_of_no_accepted_source` — under a policy that accepts no
  source, the type of promoted claims is *empty*: nothing can be promoted;
* `no_uniform_promoter` — the fail-closed statement in its strongest form: there
  is no policy-generic function producing a promoted claim from a bare claim.
  Promotion is therefore not derivable from the claim alone;
* `promotion_depends_on_policy` — both extremes are realised, so the pipeline is
  neither vacuous nor automatic.
-/

namespace Cuisine.DataFlow

open Cuisine.Surfaces

/-! ## Carriers -/

inductive EvidenceLane
  | cookbookLane | archiveLane | oralHistoryLane | practitionerLane
  | communityLane | sensoryPanelLane | instrumentalLane | nutritionDatabaseLane
  | agriculturalLane | scholarlyLane | dinerMemoryLane
  deriving DecidableEq, Fintype, Repr

structure SourceReceipt where
  receiptId : String
  title : String
  locator : String
  date : String
  evidenceLane : EvidenceLane
  licence : String

inductive PredicateRole
  | containsRole | excludesRole | derivesFromRole | transformsRole | evokesRole
  | hasProfileRole | hasNutrientRole | sourcedFromRole | variantOfRole
  | belongsToMovementRole
  deriving DecidableEq, Fintype, Repr

structure PredicateAtom where
  subject : String
  predicate : PredicateRole
  object : String
  sourceId : String

structure NormalizedAtom where
  rawAtom : PredicateAtom
  normalizedSubject : String
  normalizedObject : String
  ontologyLocator : String

structure SurfaceClaim where
  surface : SurfaceKind
  atom : NormalizedAtom
  claimText : String

inductive RelationBetweenClaims
  | agrees | refines | contextualizes | conflicts | unresolvedRelation
  deriving DecidableEq, Fintype, Repr

structure ClaimRelation where
  leftClaim : SurfaceClaim
  rightClaim : SurfaceClaim
  relation : RelationBetweenClaims
  note : String

/-- The Agda `PromotionPolicy`: three proof obligations, left abstract. -/
structure PromotionPolicy where
  AcceptsSource : SurfaceClaim → SourceReceipt → Prop
  NormalizationValid : SurfaceClaim → Prop
  ContradictionsResolved : SurfaceClaim → List ClaimRelation → Prop

/-- The Agda `PromotionEvidence`. -/
structure PromotionEvidence (policy : PromotionPolicy) (claim : SurfaceClaim) where
  sourceReceipt : SourceReceipt
  relatedClaims : List ClaimRelation
  sourceAccepted : policy.AcceptsSource claim sourceReceipt
  normalizationChecked : policy.NormalizationValid claim
  contradictionsHandled : policy.ContradictionsResolved claim relatedClaims

/-- The Agda `PromotedClaim`. -/
structure PromotedClaim (policy : PromotionPolicy) where
  promotedSurfaceClaim : SurfaceClaim
  promotionEvidence : PromotionEvidence policy promotedSurfaceClaim

/-- The Agda `promote`. -/
def promote (policy : PromotionPolicy) (claim : SurfaceClaim)
    (evidence : PromotionEvidence policy claim) : PromotedClaim policy :=
  ⟨claim, evidence⟩

/-- The Agda `recoverPromotionEvidence`. -/
def recoverPromotionEvidence {policy : PromotionPolicy} (p : PromotedClaim policy) :
    PromotionEvidence policy p.promotedSurfaceClaim := p.promotionEvidence

/-! ## Proof-bearing: nothing is lost by promotion -/

@[simp] theorem promotedSurfaceClaim_promote (policy : PromotionPolicy) (claim : SurfaceClaim)
    (e : PromotionEvidence policy claim) :
    (promote policy claim e).promotedSurfaceClaim = claim := rfl

@[simp] theorem recover_promote (policy : PromotionPolicy) (claim : SurfaceClaim)
    (e : PromotionEvidence policy claim) :
    recoverPromotionEvidence (promote policy claim e) = e := rfl

/-- Promotion is the *only* way to build a promoted claim: every inhabitant is
`promote` applied to its own evidence. -/
theorem eq_promote {policy : PromotionPolicy} (p : PromotedClaim policy) :
    p = promote policy p.promotedSurfaceClaim (recoverPromotionEvidence p) := rfl

/-! ## Fail-closed -/

/-- The policy that accepts nothing. -/
def rejectingPolicy : PromotionPolicy where
  AcceptsSource _ _ := False
  NormalizationValid _ := True
  ContradictionsResolved _ _ := True

/-- The policy that accepts everything. -/
def permissivePolicy : PromotionPolicy where
  AcceptsSource _ _ := True
  NormalizationValid _ := True
  ContradictionsResolved _ _ := True

/-- **Fail-closed, local form.**  If no source is accepted for a claim, that
claim cannot be promoted. -/
theorem isEmpty_evidence_of_no_accepted_source (policy : PromotionPolicy)
    (claim : SurfaceClaim) (h : ∀ r, ¬ policy.AcceptsSource claim r) :
    IsEmpty (PromotionEvidence policy claim) :=
  ⟨fun e => h e.sourceReceipt e.sourceAccepted⟩

/-- **Fail-closed, global form.**  Under a policy that accepts no source at all,
the type of promoted claims is empty: the pipeline produces nothing rather than
defaulting to acceptance. -/
theorem isEmpty_promotedClaim_of_no_accepted_source (policy : PromotionPolicy)
    (h : ∀ c r, ¬ policy.AcceptsSource c r) : IsEmpty (PromotedClaim policy) :=
  ⟨fun p => h _ _ p.promotionEvidence.sourceAccepted⟩

theorem isEmpty_rejecting : IsEmpty (PromotedClaim rejectingPolicy) :=
  isEmpty_promotedClaim_of_no_accepted_source _ fun _ _ h => h

/-- **No uniform promoter.**  There is no function that, for every policy and
every claim, returns a promoted claim.  Promotion cannot be synthesised from the
claim alone; it always consumes policy-specific evidence.  This is the precise
content of the Agda header's "fail-closed". -/
theorem no_uniform_promoter :
    ¬ Nonempty ((policy : PromotionPolicy) → SurfaceClaim → PromotedClaim policy) := by
  rintro ⟨f⟩
  exact isEmpty_rejecting.false
    (f rejectingPolicy
      { surface := .identitySurface
        atom :=
          { rawAtom := ⟨"", .containsRole, "", ""⟩
            normalizedSubject := ""
            normalizedObject := ""
            ontologyLocator := "" }
        claimText := "" })

/-- Both extremes occur: under the permissive policy every claim is promotable,
under the rejecting policy none is.  So the promotion layer is a genuine
policy-parametrised gate, neither vacuous nor automatic. -/
theorem promotion_depends_on_policy :
    (∀ claim : SurfaceClaim,
        ∃ p : PromotedClaim permissivePolicy, p.promotedSurfaceClaim = claim) ∧
      IsEmpty (PromotedClaim rejectingPolicy) := by
  refine ⟨fun claim => ⟨promote permissivePolicy claim ?_, rfl⟩, isEmpty_rejecting⟩
  exact
    { sourceReceipt := ⟨"", "", "", "", .cookbookLane, ""⟩
      relatedClaims := []
      sourceAccepted := trivial
      normalizationChecked := trivial
      contradictionsHandled := trivial }

end Cuisine.DataFlow
