import Integration.PromotionDiscipline

/-!
# Promotion evidence: separating "the transition is licensed" from "this row has the receipt"

`Integration.PromotionDiscipline` models reclassification as a transition system
and proves the three transitions that must never fire.  Its positive entries,
however, are **declarations**: `EvidenceKind.mayPromoteTo` says only that
evidence *of that kind* would be the right kind for the target class.  Nothing
in that file requires the row to actually possess such evidence, so a worker
could satisfy the table by asserting a kind.

This file closes that hole by making positive promotion **evidence-indexed**.

## The two-step gate

1. `MayPromote source e target` — the transition *shape* exists (declaration).
2. `Receipt e` — the **object** that kind of evidence consists of, as a type.
   An `EvidencedPromotion` cannot be constructed without inhabiting it.

`licensed_shape_without_receipt` is the separation: a licensed shape whose
hypothesis is refutable, so the shape exists and the receipt cannot.

## What the receipts are made to prove

Each non-trivial receipt is shown to *do the work its class claims*:

* `carrier_receipt_discharges` — an exact source carrier turns the row's proved
  implication into its conclusion;
* `enumeration_receipt_universalises` — an enumeration receipt turns a check on
  the list into a statement about the ambient type;
* `field_receipt_determines` — a field-inhabiting theorem makes the field a
  function of *anything*, i.e. it really closes the socket;
* `collision_receipt_refutes` — a collision receipt refutes determination.

And the two hollow ones are shown to be hollow: `Receipt .namingResemblance` and
`Receipt .booleanCoverageDeclaration` are singletons
(`hollow_receipts_are_always_available`), so they are available to every row and
therefore separate nothing — which is why the table gives them no transition.

## The current census, and the invariant

`promotionEvidenceLedger` classifies the positive transition of each of the
sixteen open registry rows as `evidenceBacked` or `declaredOnly`.  Today every
one is `declaredOnly`, and this is proved (`gate_refuses_every_open_row`), not
claimed: the executable gate `mayExecute` returns `false` on all sixteen.  The
single `EvidencedPromotion` that *can* be built here (`sspPromotion`) belongs to
an already-closed row, and is included precisely so that the gate is known to be
satisfiable rather than vacuously closed.

`negative_transitions_unchanged` re-checks that the three proved negatives of
`PromotionDiscipline` still hold after this refinement.

Nothing here reclassifies a registry row.
-/

namespace Integration.PromotionEvidence

open Integration.SewingTaxonomy
open Integration.OutstandingObligations
open Integration.PromotionDiscipline
open Integration.Levels
open Integration.RealisationAdequacy
open Integration.CoordinateSufficiency
open Integration.FactorisationCollision

/-! ## §1 The receipts -/

/-- The receipt for `exactSourceCarrier`: the row's proved implication together
with a corpus object inhabiting its hypothesis. -/
structure CarrierReceipt : Type 1 where
  /-- The implication's hypothesis. -/
  hyp : Prop
  /-- Its conclusion. -/
  concl : Prop
  /-- The proved bridge. -/
  bridge : hyp → concl
  /-- The carrier that inhabits the hypothesis.  This is the missing half. -/
  carrier : hyp

/-- The receipt for `inhabitingTheorem`: a proof that a corpus field is pinned
to a value rather than freely settable. -/
structure FieldReceipt : Type 1 where
  /-- The record type carrying the field. -/
  record : Type
  /-- The field. -/
  field : record → Bool
  /-- The value it is pinned to. -/
  value : Bool
  /-- The theorem pinning it. -/
  pinned : ∀ r, field r = value

/-- The receipt for `enumerationCompleteness`: a list and a proof that it
exhausts its ambient type. -/
structure EnumerationReceipt : Type 1 where
  /-- The ambient type. -/
  carrier : Type
  /-- The enumeration. -/
  enumeration : List carrier
  /-- Its completeness, which must be proved. -/
  complete : ∀ x : carrier, x ∈ enumeration

/-- The receipt for `collisionWitness`: the existing `Collision` datum. -/
structure CollisionReceipt : Type 1 where
  /-- The state space. -/
  state : Type
  /-- The observation's target. -/
  observed : Type
  /-- The consumer's target. -/
  answer : Type
  /-- The observation. -/
  obs : state → observed
  /-- The consumer. -/
  consumer : state → answer
  /-- The witness. -/
  witness : Collision obs consumer

/-- The receipt for `sharedShapePredicate`: two carriers satisfying a common
predicate, and *no map between them* — which is the whole point. -/
structure ShapeReceipt : Type 1 where
  /-- The shared shape. -/
  shape : Type → Prop
  /-- One carrier. -/
  left : Type
  /-- The other. -/
  right : Type
  /-- The shape holds on the left. -/
  holdsLeft : shape left
  /-- And on the right. -/
  holdsRight : shape right

/-- **The evidence a promotion must carry**, as a type indexed by the evidence
kind.  The three kinds the table licenses nothing for get `PUnit`: a receipt of
that kind is always available and therefore says nothing. -/
def Receipt : EvidenceKind → Type 1
  | .namingResemblance => PUnit
  | .sharedShapePredicate => ShapeReceipt
  | .booleanCoverageDeclaration => PUnit
  | .exactSourceCarrier => CarrierReceipt
  | .inhabitingTheorem => FieldReceipt
  | .enumerationCompleteness => EnumerationReceipt
  | .collisionWitness => CollisionReceipt
  | .agdaTypecheckResult => PUnit

/-! ## §2 Each receipt does the work its class claims -/

/-- An exact source carrier turns the row's proved implication into its
conclusion.  This is what "the bridge is discharged" means. -/
theorem carrier_receipt_discharges (r : CarrierReceipt) : r.concl := r.bridge r.carrier

/-- An enumeration receipt lifts a check on the list to the ambient type. -/
theorem enumeration_receipt_universalises (r : EnumerationReceipt)
    (P : r.carrier → Prop) (h : ∀ x ∈ r.enumeration, P x) : ∀ x, P x :=
  fun x => h x (r.complete x)

/-- Hence it is genuine `Exhaustive` evidence in the sense of the adequacy
owner. -/
def enumeration_receipt_is_exhaustive (r : EnumerationReceipt) :
    Exhaustive (fun x : r.carrier => x ∈ r.enumeration) where
  covers := r.complete

/-- A field-inhabiting theorem makes the field a function of *any* observation:
the socket is closed, whatever the consumer reads. -/
theorem field_receipt_determines (r : FieldReceipt) {Y : Type} (o : r.record → Y) :
    Determines o r.field :=
  fun x y _ => by rw [r.pinned x, r.pinned y]

/-- A collision receipt refutes determination — the existing owner theorem. -/
theorem collision_receipt_refutes (r : CollisionReceipt) :
    ¬ Determines r.obs r.consumer :=
  r.witness.not_determines

/-- A shape receipt: `Unit` and `Bool` are both nonempty. -/
def unitBoolShapeReceipt : ShapeReceipt where
  shape := fun T => Nonempty T
  left := Unit
  right := Bool
  holdsLeft := ⟨()⟩
  holdsRight := ⟨true⟩

/-- A shape receipt still yields no map between the carriers, so it cannot be
upgraded past `structuralAnalogue`.  (The witness is the existing one.) -/
theorem shape_receipt_gives_no_transport :
    unitBoolShapeReceipt.shape unitBoolShapeReceipt.left ∧
      unitBoolShapeReceipt.shape unitBoolShapeReceipt.right ∧
      IsEmpty (Transport unitBoolShapeReceipt.left unitBoolShapeReceipt.right id id) :=
  ⟨⟨()⟩, ⟨true⟩, shared_shape_gives_no_transport_structure⟩

/-- **The hollow receipts.**  For the three kinds the table licenses nothing
for, the receipt type is a singleton: every row has one, so possessing one is
not evidence.  This is the formal reason those table rows are `false`. -/
theorem hollow_receipts_are_always_available :
    Nonempty (Receipt .namingResemblance) ∧ Nonempty (Receipt .booleanCoverageDeclaration) ∧
      Nonempty (Receipt .agdaTypecheckResult) ∧
      ∀ r r' : Receipt .namingResemblance, r = r' :=
  ⟨⟨PUnit.unit⟩, ⟨PUnit.unit⟩, ⟨PUnit.unit⟩, fun _ _ => rfl⟩

/-! ## §3 Evidenced promotion -/

/-- **A promotion that may actually be executed.**  Both halves are required:
the table must license the transition, *and* the receipt object must be
supplied. -/
structure EvidencedPromotion : Type 1 where
  /-- The row's current class. -/
  source : Kind
  /-- The kind of evidence acquired. -/
  evidence : EvidenceKind
  /-- The class it moves to. -/
  target : Kind
  /-- The table licenses it. -/
  licensed : MayPromote source evidence target
  /-- And the evidence object exists. -/
  receipt : Receipt evidence

/-- An executed promotion always closes the row. -/
theorem evidenced_promotion_closes (p : EvidencedPromotion) :
    p.target.isOpenObligation = false :=
  promotion_never_lands_in_an_open_class _ _ _ p.licensed

/-- **No promotion can be executed on a hollow receipt.**  Naming resemblance, a
Boolean coverage declaration and an Agda checker result each license no
transition, so no `EvidencedPromotion` carries one — the singleton receipt
cannot be laundered into a class change. -/
theorem no_promotion_on_hollow_evidence (p : EvidencedPromotion) :
    p.evidence ≠ .namingResemblance ∧ p.evidence ≠ .booleanCoverageDeclaration ∧
      p.evidence ≠ .agdaTypecheckResult := by
  have h := p.licensed.2
  revert h
  cases p.evidence <;> cases p.target <;> simp [EvidenceKind.mayPromoteTo]

/-- **The separation.**  The transition shape can exist while the receipt cannot:
here the licensed evidence kind is `exactSourceCarrier`, the bridge is proved,
and its hypothesis is refutable, so no `CarrierReceipt` for it exists.  A row in
this state is *not* promotable, however green the table looks. -/
theorem licensed_shape_without_receipt :
    EvidenceKind.mayPromoteTo .exactSourceCarrier Kind.exactInstance = true ∧
      ∃ (hyp concl : Prop) (_ : hyp → concl), ¬ hyp :=
  ⟨rfl, (0 : ℕ) = 1, True, fun _ => trivial, by omega⟩

/-- Spelled out on the receipt type: there is no `CarrierReceipt` with that
hypothesis. -/
theorem no_carrier_receipt_for_refuted_hypothesis :
    ¬ ∃ r : CarrierReceipt, r.hyp = ((0 : ℕ) = 1) := by
  rintro ⟨r, hr⟩
  have := r.carrier
  rw [hr] at this
  omega

/-! ## §4 The one executable promotion in this repository -/

/-- The corpus's fifteen-element supersingular-prime enumeration, as a receipt:
its completeness is decided, not declared. -/
def sspEnumerationReceipt : EnumerationReceipt where
  carrier := AgdaMirror.MonsterOntos.SSP
  enumeration := Integration.SourceExactWelds.SSPAdequacy.sspEnumeration
  complete := Integration.SourceExactWelds.SSPAdequacy.sspEnumeration_complete

/-- **A fully evidenced promotion.**  The gate below is therefore satisfiable:
it is closed on the sixteen open rows because they lack receipts, not because
nothing can pass it. -/
def sspPromotion : EvidencedPromotion where
  source := .openSocket
  evidence := .enumerationCompleteness
  target := .exactInstance
  licensed := ⟨rfl, rfl⟩
  receipt := sspEnumerationReceipt

/-- And it closes its row. -/
theorem sspPromotion_closes : sspPromotion.target.isOpenObligation = false :=
  evidenced_promotion_closes sspPromotion

/-! ## §5 The census over the open rows -/

/-- Whether a row's positive transition is backed by a receipt or merely
declared. -/
inductive PromotionEvidenceStatus
  /-- A `Receipt` of the required kind exists in this repository for this row. -/
  | evidenceBacked
  /-- The transition shape is licensed; no receipt exists here. -/
  | declaredOnly
  deriving DecidableEq, Repr

/-- One row of the promotion-evidence census. -/
structure PromotionEvidenceRow where
  /-- The registry row index, matching `obligationLedger`. -/
  rowIndex : ℕ
  /-- Its evidence status. -/
  status : PromotionEvidenceStatus
  /-- Why. -/
  note : String

/-- **The census.**  One entry per open registry row, in the ledger's order. -/
def promotionEvidenceLedger : List PromotionEvidenceRow :=
  [ { rowIndex := 5, status := .declaredOnly
      note := "No theorem pins the DNA sheet flags; two inhabitants still differ \
               only at the flag, so no FieldReceipt exists." }
  , { rowIndex := 11, status := .declaredOnly
      note := "The projection record's fields remain independently settable; no \
               FieldReceipt." }
  , { rowIndex := 12, status := .declaredOnly
      note := "The declared emptiness is asserted by the record, not derived \
               from the carrier; no FieldReceipt." }
  , { rowIndex := 15, status := .declaredOnly
      note := "The reachability flags are not tied to the bounded search they \
               report; no FieldReceipt." }
  , { rowIndex := 16, status := .declaredOnly
      note := "The bridge is proved but no corpus reaction graph inhabits its \
               hypothesis, so no CarrierReceipt." }
  , { rowIndex := 20, status := .declaredOnly
      note := "The loom evidence-status field is not determined by the relation \
               type; the existing result is the negative." }
  , { rowIndex := 31, status := .declaredOnly
      note := "The adapter implication is proved; the corpus supplies no \
               instance of its hypothesis." }
  , { rowIndex := 37, status := .declaredOnly
      note := "The mode-selection witness record constrains nothing; no \
               FieldReceipt." }
  , { rowIndex := 38, status := .declaredOnly
      note := "The holonomy frame is a deliberately open socket; no theorem \
               supplies it." }
  , { rowIndex := 43, status := .declaredOnly
      note := "The sampling bridge is proved; no corpus surface supplies the \
               sampling datum." }
  , { rowIndex := 53, status := .declaredOnly
      note := "The Pareto boundary record's fields are not pinned to the \
               outcome order." }
  , { rowIndex := 55, status := .declaredOnly
      note := "Monotonicity under language enlargement is proved; the corpus \
               declares no inclusion to apply it to." }
  , { rowIndex := 61, status := .declaredOnly
      note := "Row 71 meets the obligation on a different carrier; this row's \
               own hypothesis over ℕ has no inhabitant." }
  , { rowIndex := 62, status := .declaredOnly
      note := "No corpus surface supplies two weightings with opposite-signed \
               contrasts; row 72 shows the provisioning surface cannot." }
  , { rowIndex := 66, status := .declaredOnly
      note := "The SSP receipt (sspPromotion) belongs to row 76, not to this \
               row: the corpus atlases still decline the exhaustiveness claim." }
  , { rowIndex := 68, status := .declaredOnly
      note := "A coverage flag is a hollow receipt; only an EnumerationReceipt \
               closes this, and none exists for these carriers." }
  ]

/-- **The census covers exactly the open rows**, in order.  A new open row, or a
row that changes class, breaks this proof. -/
theorem promotion_census_covers_obligations :
    promotionEvidenceLedger.map (fun r => r.rowIndex) =
      obligationLedger.map (fun o => o.rowIndex) := rfl

/-- **The executable gate.**  A promotion may be executed only on a row whose
transition is receipt-backed.  This is the mechanical refusal: a worker
asserting "this looks exact" does not move the row. -/
def mayExecute (r : PromotionEvidenceRow) : Bool :=
  decide (r.status = PromotionEvidenceStatus.evidenceBacked)

/-- **The gate is closed on every open row today.**  Proved by computation over
the census, not asserted. -/
theorem gate_refuses_every_open_row :
    ∀ r ∈ promotionEvidenceLedger, mayExecute r = false := by decide

/-- The metric: evidence-backed positive transitions, and declared-only ones.
Coverage is currently `0 / 16`, and — the point of this file — the sixteen are
now *classified* rather than silently positive. -/
theorem promotion_evidence_coverage :
    (promotionEvidenceLedger.filter (fun r =>
      decide (r.status = PromotionEvidenceStatus.evidenceBacked))).length = 0 ∧
    (promotionEvidenceLedger.filter (fun r =>
      decide (r.status = PromotionEvidenceStatus.declaredOnly))).length = 16 ∧
    promotionEvidenceLedger.length = 16 :=
  ⟨rfl, rfl, rfl⟩

/-- Every row is classified: the status field admits no third value and no row
is left unset. -/
theorem every_open_row_is_classified :
    ∀ r ∈ promotionEvidenceLedger,
      r.status = PromotionEvidenceStatus.evidenceBacked ∨
        r.status = PromotionEvidenceStatus.declaredOnly := by
  intro r _
  cases r.status
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ## §6 The hard invariant -/

/-- **The proved negatives are unchanged.**  Naming resemblance still promotes
nothing, a coverage flag still promotes nothing, and an Agda checker result
still changes no class — after, as before, the evidence indexing. -/
theorem negative_transitions_unchanged :
    (∀ k : Kind, EvidenceKind.mayPromoteTo .namingResemblance k = false) ∧
    (∀ k : Kind, EvidenceKind.mayPromoteTo .booleanCoverageDeclaration k = false) ∧
    (∀ k : Kind, EvidenceKind.mayPromoteTo .agdaTypecheckResult k = false) ∧
    ¬ MayPromote .candidateBridge .namingResemblance .exactInstance := by
  refine ⟨by decide, coverage_flag_promotes_nothing, agda_typecheck_promotes_nothing, by decide⟩

end Integration.PromotionEvidence
