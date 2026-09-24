import Mathlib

/-!
# Lean mirror of `LoomRelationAlgebra.agda` (genuine, fully proved)

Faithful transcription of `LoomRelationAlgebra.agda`: an "affidavit-style" finite
relation algebra for loom reconciliation.  It comprises a finite enumeration of
relation *types*, their coarse *roots* and display *buckets* (each given by a
total classifier function), an evidence-status enumeration, a separate
promotion-state enumeration, and a `LoomTypedRelation` record bundling a relation
type together with *proofs* that its declared root and bucket are the derived
ones.  The top-level `LoomRelationAlgebra` record fixes the canonical
enumerations and two canonical (non-promoting) witnesses.

All the Agda `refl` equality obligations are genuine decidable facts and are
proved here (`rfl`/`decide`).  Nothing is postulated; the module is axiom-clean.

## Honesty boundary (preserved)

As in the Agda original, this models only the *classifier shape* of the
affidavit lane: a support relation can remain review-only and non-promoting, and
promotion requires a separate guarded contract — it is never implied by bucket
assignment.  The `separatesRelationFromPromotion` flag records exactly this.
-/

namespace AgdaMirror.Loom

/-- Finite relation labels. -/
inductive LoomRelationType
  | exactSupport | equivalentSupport | explicitDispute | implicitDispute
  | partialOverlap | adjacentEvent | substitution | proceduralNonanswer | unrelated
  deriving DecidableEq, Repr, Fintype

/-- Canonical precedence ordering of relation types. -/
def canonicalRelationPrecedence : List LoomRelationType :=
  [.exactSupport, .explicitDispute, .equivalentSupport, .implicitDispute,
   .partialOverlap, .adjacentEvent, .substitution, .proceduralNonanswer, .unrelated]

/-- Coarse relation roots. -/
inductive LoomRelationRoot
  | supports | invalidates | nonResolving | unanswered
  deriving DecidableEq, Repr, Fintype

/-- Total root classifier. -/
def relationRootFor : LoomRelationType → LoomRelationRoot
  | .exactSupport => .supports
  | .equivalentSupport => .supports
  | .explicitDispute => .invalidates
  | .implicitDispute => .invalidates
  | .partialOverlap => .supports
  | .adjacentEvent => .nonResolving
  | .substitution => .nonResolving
  | .proceduralNonanswer => .nonResolving
  | .unrelated => .unanswered

/-- Display buckets. -/
inductive LoomBucket
  | supportedBucket | disputedBucket | partialSupportBucket | adjacentEventBucket
  | substitutionBucket | nonSubstantiveResponseBucket | missingBucket
  deriving DecidableEq, Repr

/-- Total bucket classifier. -/
def bucketFor : LoomRelationType → LoomBucket
  | .exactSupport => .supportedBucket
  | .equivalentSupport => .supportedBucket
  | .explicitDispute => .disputedBucket
  | .implicitDispute => .disputedBucket
  | .partialOverlap => .partialSupportBucket
  | .adjacentEvent => .adjacentEventBucket
  | .substitution => .substitutionBucket
  | .proceduralNonanswer => .nonSubstantiveResponseBucket
  | .unrelated => .missingBucket

/-- Evidence status. -/
inductive LoomEvidenceStatus
  | reviewOnly | witnessed | blocked | boundaryOnly | unresolved
  deriving DecidableEq, Repr

/-- Promotion state (kept separate from relation typing). -/
inductive LoomPromotionState
  | promotionFalse | promotionPending | promotionBlocked | promotedBySeparateContract
  deriving DecidableEq, Repr

/-- A typed relation: a relation type together with *proofs* that its declared
root and bucket are the derived ones, plus evidence/promotion/note data. -/
structure LoomTypedRelation where
  relationType : LoomRelationType
  relationRoot : LoomRelationRoot
  relationRootIsDerived : relationRoot = relationRootFor relationType
  bucket : LoomBucket
  bucketIsDerived : bucket = bucketFor relationType
  evidenceStatus : LoomEvidenceStatus
  promotionState : LoomPromotionState
  relationNote : String

/-- The relation algebra bundle, fixing the canonical enumerations and two
canonical non-promoting witnesses. -/
structure LoomRelationAlgebra where
  relationTypes : List LoomRelationType
  relationTypesAreAffidavitStyle :
    relationTypes =
      [.exactSupport, .equivalentSupport, .explicitDispute, .implicitDispute,
       .partialOverlap, .adjacentEvent, .substitution, .proceduralNonanswer, .unrelated]
  relationPrecedence : List LoomRelationType
  relationPrecedenceIsCanonical : relationPrecedence = canonicalRelationPrecedence
  relationRoots : List LoomRelationRoot
  relationRootsAreCanonical :
    relationRoots = [.supports, .invalidates, .nonResolving, .unanswered]
  evidenceStatuses : List LoomEvidenceStatus
  evidenceStatusesAreCanonical :
    evidenceStatuses = [.reviewOnly, .witnessed, .blocked, .boundaryOnly, .unresolved]
  promotionStates : List LoomPromotionState
  promotionStatesAreCanonical :
    promotionStates =
      [.promotionFalse, .promotionPending, .promotionBlocked, .promotedBySeparateContract]
  supportDoesNotPromote : LoomTypedRelation
  boundaryDoesNotPromote : LoomTypedRelation
  separatesRelationFromPromotion : Bool
  separatesRelationFromPromotionIsTrue : separatesRelationFromPromotion = true
  formalismBoundary : List String

/-- Canonical support relation: a comparison relation only, non-promoting. -/
def canonicalSupportRelation : LoomTypedRelation where
  relationType := .equivalentSupport
  relationRoot := .supports
  relationRootIsDerived := rfl
  bucket := .supportedBucket
  bucketIsDerived := rfl
  evidenceStatus := .witnessed
  promotionState := .promotionFalse
  relationNote := "Support is a comparison relation only; it is not theorem promotion."

/-- Canonical boundary relation: relation-bearing while promotion stays blocked. -/
def canonicalBoundaryRelation : LoomTypedRelation where
  relationType := .proceduralNonanswer
  relationRoot := .nonResolving
  relationRootIsDerived := rfl
  bucket := .nonSubstantiveResponseBucket
  bucketIsDerived := rfl
  evidenceStatus := .boundaryOnly
  promotionState := .promotionFalse
  relationNote := "Boundary-only material may be relation-bearing while promotion remains blocked."

/-- The canonical relation algebra. -/
def canonicalLoomRelationAlgebra : LoomRelationAlgebra where
  relationTypes :=
    [.exactSupport, .equivalentSupport, .explicitDispute, .implicitDispute,
     .partialOverlap, .adjacentEvent, .substitution, .proceduralNonanswer, .unrelated]
  relationTypesAreAffidavitStyle := rfl
  relationPrecedence := canonicalRelationPrecedence
  relationPrecedenceIsCanonical := rfl
  relationRoots := [.supports, .invalidates, .nonResolving, .unanswered]
  relationRootsAreCanonical := rfl
  evidenceStatuses := [.reviewOnly, .witnessed, .blocked, .boundaryOnly, .unresolved]
  evidenceStatusesAreCanonical := rfl
  promotionStates :=
    [.promotionFalse, .promotionPending, .promotionBlocked, .promotedBySeparateContract]
  promotionStatesAreCanonical := rfl
  supportDoesNotPromote := canonicalSupportRelation
  boundaryDoesNotPromote := canonicalBoundaryRelation
  separatesRelationFromPromotion := true
  separatesRelationFromPromotionIsTrue := rfl
  formalismBoundary :=
    ["This relation algebra mirrors the affidavit-lane classifier shape, not legal sufficiency.",
     "A support relation can remain review-only and non-promoting.",
     "Promotion requires a separate guarded contract and is not implied by bucket assignment."]

/-! ## What the record actually says

The Agda original proves the derived-field equalities by `refl` and records the
relation/promotion separation as a `Bool` pinned to `true`.  The four results
below say what those two devices amount to.
-/

/-- The declared root and bucket of a typed relation are its derived ones, so a
typed relation is exactly a relation type together with evidence, promotion and
a note: **the two derived fields carry no information**. -/
def typedRelationEquiv :
    LoomTypedRelation ≃
      (LoomRelationType × LoomEvidenceStatus × LoomPromotionState × String) where
  toFun r := (r.relationType, r.evidenceStatus, r.promotionState, r.relationNote)
  invFun p := ⟨p.1, relationRootFor p.1, rfl, bucketFor p.1, rfl, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv := by rintro ⟨t, _, rfl, _, rfl, e, s, n⟩; rfl
  right_inv _ := rfl

/-- The positive half: the relation type determines both coarser classifiers. -/
theorem classifiers_determined (r s : LoomTypedRelation)
    (h : r.relationType = s.relationType) :
    r.relationRoot = s.relationRoot ∧ r.bucket = s.bucket := by
  refine ⟨?_, ?_⟩
  · rw [r.relationRootIsDerived, s.relationRootIsDerived, h]
  · rw [r.bucketIsDerived, s.bucketIsDerived, h]

/-- **The relation/promotion separation, as a theorem rather than a flag.**  The
Agda record asserts `separatesRelationFromPromotion ≡ true`; what that is *for*
is that the promotion state is not a function of the relation type.  Here are
two typed relations with the same relation type — hence the same root and the
same bucket — and different promotion states. -/
theorem promotion_not_determined_by_relationType :
    ∃ r s : LoomTypedRelation,
      r.relationType = s.relationType ∧ r.promotionState ≠ s.promotionState :=
  ⟨canonicalSupportRelation,
   { canonicalSupportRelation with promotionState := .promotionPending },
   rfl, by decide⟩

/-- Likewise the evidence status is not a function of the relation type: a
support relation can be witnessed or merely review-only. -/
theorem evidence_not_determined_by_relationType :
    ∃ r s : LoomTypedRelation,
      r.relationType = s.relationType ∧ r.evidenceStatus ≠ s.evidenceStatus :=
  ⟨canonicalSupportRelation,
   { canonicalSupportRelation with evidenceStatus := .reviewOnly },
   rfl, by decide⟩

/-- The canonical precedence list is a genuine reordering of the canonical
relation-type list: duplicate-free and complete. -/
theorem precedence_is_permutation :
    canonicalRelationPrecedence.Nodup ∧
    ∀ t : LoomRelationType, t ∈ canonicalRelationPrecedence := by
  refine ⟨by decide, ?_⟩
  intro t
  cases t <;> decide

/-- **The root classifier is a genuine finite shadow.**  Every coarse root is
realised by some relation type, so the four-element root enumeration is a
faithful image of the nine-element relation-type enumeration. -/
theorem relationRootFor_surjective : Function.Surjective relationRootFor := by
  intro b
  cases b
  · exact ⟨.exactSupport, rfl⟩
  · exact ⟨.explicitDispute, rfl⟩
  · exact ⟨.adjacentEvent, rfl⟩
  · exact ⟨.unrelated, rfl⟩

/-- ...and it is only a shadow: it has no section-free inverse, because it is
not injective (`exactSupport` and `equivalentSupport` share a root). -/
theorem relationRootFor_not_injective : ¬ Function.Injective relationRootFor := by
  intro h
  exact absurd (h (a₁ := .exactSupport) (a₂ := .equivalentSupport) rfl) (by decide)

/-- The canonical witnesses are genuinely non-promoting. -/
theorem canonical_witnesses_nonPromoting :
    canonicalSupportRelation.promotionState = .promotionFalse ∧
    canonicalBoundaryRelation.promotionState = .promotionFalse := ⟨rfl, rfl⟩

end AgdaMirror.Loom
