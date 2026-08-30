import Integration.MirrorDrift
import Integration.TransportFalsification

/-!
# Frontier priority: an evidence-acquisition queue, derived and advisory

`Integration.OutstandingObligations` lists the sixteen open registry rows and
what each is waiting for.  A list is not a plan: some evidence would remove a
single uncertainty and some would remove a whole cohort's.  This file derives a
priority partition from the ledger **mechanically** — the band of a row is a
function of the cohort its obstruction belongs to — and then proves the property
that keeps the queue honest.

## The cohorts

Every open row is waiting on one of three obstructions:

| obstruction | rows | size |
|---|---|---:|
| a record field that is free rather than derived | 5, 11, 12, 15, 20, 37, 38, 53, 68 | 9 |
| a corpus instance inhabiting a proved implication | 16, 31, 43, 55, 61, 62 | 6 |
| completeness of an enumeration | 66 | 1 |

The bands are computed from those sizes by `bandOf`, and
`band_is_derived_from_cohort_size` proves that no row's band was set by hand.

## The invariant that matters

**Priority is advisory metadata, never proof authority.**
`high_priority_rows_are_still_refused` proves that every row in the top band is
still refused by the promotion gate of `Integration.PromotionEvidence`: moving a
row up the queue does not move it out of `declaredOnly`.  A worker that
optimises the queue therefore cannot thereby close a row.

## Leverage, honestly stated

The largest cohort is the free-field one, and
`Integration.FreeFieldAudit.fieldReceipt_field_is_not_free` says exactly why a
declaration cannot close any of those rows: each needs a *theorem pinning the
field to the content it reports*.  That is the highest-leverage evidence class,
and this file says so as metadata rather than as a claim that any such theorem
exists.
-/

namespace Integration.FrontierPriority

open Integration.OutstandingObligations
open Integration.PromotionEvidence

/-! ## §1 Obstructions and bands -/

/-- The obstruction a row is waiting on. -/
inductive Obstruction
  /-- A record field that is settable independently of what it reports. -/
  | freeField
  /-- A proved implication with no corpus instance of its hypothesis. -/
  | missingCarrier
  /-- An enumeration whose completeness is not proved. -/
  | enumeration
  deriving DecidableEq, Repr, Fintype

/-- Priority bands. -/
inductive Band
  /-- The obstruction blocks a large cohort. -/
  | high
  /-- It blocks several rows. -/
  | medium
  /-- It blocks one. -/
  | low
  deriving DecidableEq, Repr, Fintype

/-- **The band is a function of the cohort size.**  Nothing else feeds into
it. -/
def bandOf (cohortSize : ℕ) : Band :=
  if 7 ≤ cohortSize then .high else if 2 ≤ cohortSize then .medium else .low

/-- The obstruction of a row, read off its typed missing evidence. -/
def obstructionOf : MissingEvidence → Obstruction
  | .exactSourceCarrier _ => .missingCarrier
  | .theoremInhabitingField _ => .freeField
  | .collisionWitness _ => .missingCarrier
  | .enumerationCompleteness _ => .enumeration
  | .agdaTypecheckResult => .missingCarrier

/-- The cohort of an obstruction: the open rows waiting on it. -/
def cohort (o : Obstruction) : List ℕ :=
  (obligationLedger.filter (fun ob => decide (obstructionOf ob.missing = o))).map
    (fun ob => ob.rowIndex)

/-- The cohort sizes, computed from the live ledger. -/
theorem cohort_census :
    (cohort .freeField).length = 9 ∧ (cohort .missingCarrier).length = 6 ∧
      (cohort .enumeration).length = 1 :=
  ⟨rfl, rfl, rfl⟩

/-- The cohorts partition the frontier: their sizes sum to the ledger length. -/
theorem cohorts_partition :
    (cohort .freeField).length + (cohort .missingCarrier).length +
      (cohort .enumeration).length = obligationLedger.length := rfl

/-! ## §2 The derived queue -/

/-- One row of the priority queue. -/
structure PriorityRow where
  /-- The registry row. -/
  rowIndex : ℕ
  /-- What blocks it. -/
  obstruction : Obstruction
  /-- Its band. -/
  band : Band
  deriving DecidableEq, Repr

/-- **The queue, derived from the obligation ledger.**  Each row's obstruction
comes from its typed missing evidence and its band from the cohort size. -/
def priorityQueue : List PriorityRow :=
  obligationLedger.map (fun ob =>
    { rowIndex := ob.rowIndex
      obstruction := obstructionOf ob.missing
      band := bandOf (cohort (obstructionOf ob.missing)).length })

/-- **The queue covers exactly the open rows**, in the ledger's order. -/
theorem queue_covers_ledger :
    priorityQueue.map (fun r => r.rowIndex) = obligationLedger.map (fun ob => ob.rowIndex) := by
  simp [priorityQueue]

/-- **Every band is derived, none is asserted.** -/
theorem band_is_derived_from_cohort_size :
    ∀ r ∈ priorityQueue, r.band = bandOf (cohort r.obstruction).length := by
  intro r hr
  simp only [priorityQueue, List.mem_map] at hr
  obtain ⟨ob, -, rfl⟩ := hr
  rfl

/-- The band census: nine high, six medium, one low. -/
theorem band_census :
    (priorityQueue.filter (fun r => decide (r.band = Band.high))).length = 9 ∧
    (priorityQueue.filter (fun r => decide (r.band = Band.medium))).length = 6 ∧
    (priorityQueue.filter (fun r => decide (r.band = Band.low))).length = 1 ∧
    priorityQueue.length = 16 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The top of the queue, as a list of registry rows. -/
def highPriorityRows : List ℕ :=
  (priorityQueue.filter (fun r => decide (r.band = Band.high))).map (fun r => r.rowIndex)

/-- And it is exactly the free-field cohort — the queue is the cohort structure,
not a separate opinion. -/
theorem high_band_is_the_free_field_cohort : highPriorityRows = cohort .freeField := rfl

/-! ## §3 Priority is not authority -/

/-- **The top band is still refused.**  Every high-priority row is
`declaredOnly` and the promotion gate returns `false` on it: raising a row's
priority does not raise its evidence. -/
theorem high_priority_rows_are_still_refused :
    ∀ p ∈ promotionEvidenceLedger, p.rowIndex ∈ highPriorityRows → mayExecute p = false := by
  intro p hp _
  exact gate_refuses_every_open_row p hp

/-- More sharply: no row of any band passes the gate today, so the queue cannot
be gamed into a promotion. -/
theorem no_band_passes_the_gate :
    ∀ r ∈ priorityQueue, ∀ p ∈ promotionEvidenceLedger,
      r.rowIndex = p.rowIndex → mayExecute p = false := by
  intro _ _ p hp _
  exact gate_refuses_every_open_row p hp

/-- **What the top band actually needs.**  Each free-field row is waiting for a
theorem pinning its field, and a free field can never supply that receipt
itself.  This is the leverage statement, and it is a theorem about receipts, not
about the queue. -/
theorem free_field_rows_need_a_pinning_theorem (r : FieldReceipt) {C : Type}
    {content : r.record → C} : ¬ Integration.FreeFieldAudit.Free content r.field :=
  Integration.FreeFieldAudit.fieldReceipt_field_is_not_free r

end Integration.FrontierPriority
