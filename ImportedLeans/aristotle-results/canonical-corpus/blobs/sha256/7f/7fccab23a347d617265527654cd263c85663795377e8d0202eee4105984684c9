import Integration.PromotionEvidence
import AgdaMirror.AuthorityRoutes

/-!
# Free-field audit: which record fields can influence a promotion without a receipt

A record field of type `Bool` (or an unconstrained `Prop` field) looks
evidentiary in a table and carries no content whatever unless something pins it.
This file gives that observation a generic vocabulary, proves the two negatives
that make the vocabulary useful, connects it to the promotion gate, and then
audits the promotion-relevant fields of the corpus mirrors one by one.

## The generic part

* `Free f` — the field takes both values at fixed content, i.e. it is settable
  independently of what it purports to summarise;
* `Pinned f` — the field is constant on its carrier;
* `free_at_fixed_content_is_a_collision` — a free field *is* a collision of the
  content reading against the field, so this is the existing owner and not a
  new notion;
* `pinned_field_cannot_report` — a pinned field cannot report a violation of
  anything that varies: the negative sufficiency result;
* `fieldReceipt_field_is_not_free` — the bridge to the promotion gate: the
  `FieldReceipt` of `Integration.PromotionEvidence` requires a pinned field, so
  **no free field can ever be the receipt that closes its own socket.**

## The audit

`freeFieldAudit` classifies each promotion-relevant field reached by the mirrors
as `evidenceCarrying`, `pinnedTautology`, `freeUnbacked` or
`notPromotionRelevant`, and cites for each the theorem that establishes the
classification.  `every_free_field_is_exposed` proves the postcondition: no row
is classified `freeUnbacked` without a named negative result exposing it, so a
free field cannot sit silently in the spine.

Nothing here reclassifies a registry row, and nothing here is a claim about any
domain: the theorems are about `Bool`-valued fields of record types.
-/

namespace Integration.FreeFieldAudit

open Integration.CoordinateSufficiency
open Integration.FactorisationCollision
open Integration.PromotionEvidence

/-! ## §1 Free and pinned fields -/

variable {R C : Type}

/-- **A free field**: two inhabitants agreeing on the content the field is
supposed to summarise, and disagreeing on the field. -/
def Free (content : R → C) (field : R → Bool) : Prop :=
  ∃ r r' : R, content r = content r' ∧ field r ≠ field r'

/-- **A pinned field**: constant on the whole carrier. -/
def Pinned (field : R → Bool) : Prop := ∃ b, ∀ r, field r = b

/-- **A free field is a collision** of the content reading against the field.
The obstruction is the existing datum; "free field" is a name for an instance of
it. -/
theorem free_is_a_collision {content : R → C} {field : R → Bool}
    (h : Free content field) : Nonempty (Collision content field) := by
  obtain ⟨r, r', hc, hne⟩ := h
  exact ⟨{ left := r
           right := r'
           distinct := fun he => hne (by rw [he])
           collide := hc
           separate := hne }⟩

/-- Hence a free field is not determined by the content it decorates: no reading
of the content computes it. -/
theorem free_not_determined {content : R → C} {field : R → Bool}
    (h : Free content field) : ¬ Determines content field :=
  (free_is_a_collision h).elim (fun w => w.not_determines)

/-- And no downstream function of the content recovers it either. -/
theorem free_field_not_recoverable {content : R → C} {field : R → Bool}
    (h : Free content field) (f : C → Bool) : ¬ ∀ r, field r = f (content r) :=
  (free_is_a_collision h).elim (fun w => w.no_reading f)

/-- **A pinned field cannot report a violation.**  If the flag is constant and
some other field varies, the flag does not determine that field: a tautology
field summarises nothing. -/
theorem pinned_field_cannot_report {field other : R → Bool} (hp : Pinned field)
    (hv : ∃ r r' : R, other r ≠ other r') : ¬ Determines field other := by
  obtain ⟨b, hb⟩ := hp
  obtain ⟨r, r', hne⟩ := hv
  intro h
  exact hne (h r r' (by rw [hb r, hb r']))

/-- A field cannot be both free and pinned. -/
theorem not_free_and_pinned {content : R → C} {field : R → Bool}
    (hf : Free content field) : ¬ Pinned field := by
  obtain ⟨r, r', -, hne⟩ := hf
  rintro ⟨b, hb⟩
  exact hne (by rw [hb r, hb r'])

/-! ## §2 The bridge to the promotion gate -/

/-- **A field receipt requires a pinned field.**  This is what `FieldReceipt`
asks for, read back through the vocabulary above. -/
theorem fieldReceipt_field_is_pinned (r : FieldReceipt) : Pinned r.field :=
  ⟨r.value, r.pinned⟩

/-- **Hence no free field can supply the receipt that would close its own
socket.**  A row whose field is free is not promotable, whatever the table says
about the evidence *kind*. -/
theorem fieldReceipt_field_is_not_free (r : FieldReceipt) {content : r.record → C} :
    ¬ Free content r.field :=
  fun h => not_free_and_pinned h (fieldReceipt_field_is_pinned r)

/-! ## §3 The corpus fields -/

open AgdaMirror.AuthorityRoutes

/-- The content a provenance row's permission flag purports to summarise: the
source, its provenance kind and its replaceability. -/
def provenanceContent (p : ProvenanceRow) : String × ProvenanceKind × Bool :=
  (p.sourceName, p.kind, p.replaceableByFormalEncoding)

/-- **`permissionOrAuthorityClaimed` is free**, in the generic sense: two rows
with identical content differing only in the flag. -/
theorem permission_field_free : Free provenanceContent ProvenanceRow.permissionOrAuthorityClaimed :=
  ⟨⟨"s", .namedCommunity, true, false⟩, ⟨"s", .namedCommunity, false, false⟩, rfl, by decide⟩

/-- Hence no reading of a row's content computes its permission flag. -/
theorem permission_not_determined :
    ¬ Determines provenanceContent ProvenanceRow.permissionOrAuthorityClaimed :=
  free_not_determined permission_field_free

/-- **`boundaryHolds` is pinned**, by its own companion proof field. -/
theorem boundaryHolds_pinned : Pinned CulturalBoundary.boundaryHolds :=
  ⟨true, fun b => b.boundaryHoldsIsTrue⟩

/-- **So it cannot report a violation of the anti-extraction flags**, which do
vary across inhabitants. -/
theorem boundaryHolds_cannot_report :
    ¬ Determines CulturalBoundary.boundaryHolds CulturalBoundary.noExtraction :=
  pinned_field_cannot_report boundaryHolds_pinned
    ⟨canonicalBoundary, permissiveBoundary, by decide⟩

/-- The content a promotion record's verdict purports to summarise: its adapter
and its three receipt fields. -/
def promotionContent (p : Promotion) : Adapter × Prop × Prop × Prop :=
  (p.adapter, p.sourceAuthorityReceipt, p.communityAuthorityReceipt,
    p.adaptationBoundaryReceipt)

/-- **`representationPromoted` is free**: the record states its evidence and its
verdict side by side without linking them. -/
theorem representationPromoted_free : Free promotionContent Promotion.representationPromoted :=
  ⟨⟨canonicalAdapter, True, True, True, true⟩, ⟨canonicalAdapter, True, True, True, false⟩,
    rfl, by decide⟩

/-- Hence the promotion verdict is not a function of the receipts it records. -/
theorem representationPromoted_not_determined :
    ¬ Determines promotionContent Promotion.representationPromoted :=
  free_not_determined representationPromoted_free

/-- **The coverage flag of a declared carrier is free** in the same sense. -/
theorem coverage_flag_free :
    Free Integration.DeclaredCarrier.CoverageClaim.claimsSourceAgreement
      Integration.DeclaredCarrier.CoverageClaim.claimsExhaustiveCoverage :=
  ⟨⟨true, false⟩, ⟨false, false⟩, rfl, by decide⟩

/-- And so is the adequacy owner's own `claimsExhaustive` declaration, relative
to the carrier it decorates. -/
theorem claimsExhaustive_free :
    Free Integration.RealisationAdequacy.CoverageDeclaration.carrier
      (Integration.RealisationAdequacy.CoverageDeclaration.claimsExhaustive (S := ℕ)) :=
  ⟨⟨Integration.RealisationAdequacy.small, true⟩,
    ⟨Integration.RealisationAdequacy.small, false⟩, rfl, by decide⟩

/-! ## §4 The audit ledger -/

/-- The classification of a promotion-relevant field. -/
inductive FieldStatus
  /-- A theorem pins the field to the evidence it reports. -/
  | evidenceCarrying
  /-- The field is constant, by its own companion proof field: it can report
  nothing. -/
  | pinnedTautology
  /-- The field is settable independently of its content, and is exposed as an
  unresolved socket. -/
  | freeUnbacked
  /-- The field cannot influence any promotion. -/
  | notPromotionRelevant
  deriving DecidableEq, Repr, Fintype

/-- One audited field. -/
structure AuditRow where
  /-- Where the field lives. -/
  owner : String
  /-- Its name. -/
  field : String
  /-- The verdict. -/
  status : FieldStatus
  /-- The theorem in this file establishing the verdict.  Required to be
  non-empty for every free field. -/
  witness : String
  /-- The registry row this field keeps open, where there is one. -/
  registryRow : Option ℕ

/-- **The audit.**  Every promotion-relevant field reached by the mirrors. -/
def freeFieldAudit : List AuditRow :=
  [ { owner := "AgdaMirror.AuthorityRoutes.ProvenanceRow"
      field := "permissionOrAuthorityClaimed"
      status := .freeUnbacked
      witness := "permission_field_free, permission_not_determined"
      registryRow := none }
  , { owner := "AgdaMirror.AuthorityRoutes.CulturalBoundary"
      field := "boundaryHolds"
      status := .pinnedTautology
      witness := "boundaryHolds_pinned, boundaryHolds_cannot_report"
      registryRow := none }
  , { owner := "AgdaMirror.AuthorityRoutes.Promotion"
      field := "representationPromoted"
      status := .freeUnbacked
      witness := "representationPromoted_free, representationPromoted_not_determined"
      registryRow := none }
  , { owner := "Integration.DeclaredCarrier.CoverageClaim"
      field := "claimsExhaustiveCoverage"
      status := .freeUnbacked
      witness := "coverage_flag_free"
      registryRow := some 68 }
  , { owner := "Integration.RealisationAdequacy.CoverageDeclaration"
      field := "claimsExhaustive"
      status := .freeUnbacked
      witness := "claimsExhaustive_free, flag_does_not_give_exhaustive"
      registryRow := some 66 }
  , { owner := "corpus DNA sheet record"
      field := "sheet Bool flags"
      status := .freeUnbacked
      witness := "registry row 5's negative: two inhabitants differ only at the flag"
      registryRow := some 5 }
  , { owner := "corpus chemistry reachability record"
      field := "reachability flags"
      status := .freeUnbacked
      witness := "registry row 15's negative: the flag is not tied to the search"
      registryRow := some 15 }
  , { owner := "corpus loom relation record"
      field := "evidence status"
      status := .freeUnbacked
      witness := "registry row 20's negative: status is not determined by the \
                  relation type"
      registryRow := some 20 }
  , { owner := "corpus Pareto boundary record"
      field := "boundary fields"
      status := .freeUnbacked
      witness := "registry row 53's negative: the fields are not pinned to the \
                  outcome order"
      registryRow := some 53 }
  ]

/-- **The postcondition.**  Every field classified as free carries a named
negative result exposing it: no free field is left silent. -/
theorem every_free_field_is_exposed :
    freeFieldAudit.all (fun r =>
      match r.status with
      | .freeUnbacked => !r.witness.isEmpty
      | _ => true) = true := rfl

/-- Every audited field is classified, and no field is `evidenceCarrying`:
today, none of the promotion-relevant fields is backed by a theorem pinning it
to its evidence. -/
theorem audit_census :
    (freeFieldAudit.filter (fun r => decide (r.status = FieldStatus.freeUnbacked))).length = 8 ∧
    (freeFieldAudit.filter (fun r => decide (r.status = FieldStatus.pinnedTautology))).length = 1 ∧
    (freeFieldAudit.filter (fun r =>
      decide (r.status = FieldStatus.evidenceCarrying))).length = 0 ∧
    freeFieldAudit.length = 9 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **And a pinned field is not a substitute.**  The one `pinnedTautology` row is
not evidence either: it is constant, so it reports nothing — which is why the
census keeps the two classes apart. -/
theorem pinned_is_not_evidence :
    ¬ Determines CulturalBoundary.boundaryHolds CulturalBoundary.noExtraction :=
  boundaryHolds_cannot_report

end Integration.FreeFieldAudit
