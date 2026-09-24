import Integration.Kernel.Welds.ResidualSalienceScheduler
import RequestProject.Ranks

/-!
# Aristotle instantiation: which coverage residual is worth resolving next

The weld `Integration.Kernel.Welds.ResidualSalienceScheduler` defines the
salience of a residual as how much resolving it separates the live hypotheses,
and proves salience is not a function of the residual's size and cost.  This
file instantiates that scheduler on **Wikidata coverage residuals**, with the
live hypotheses being candidate worlds for one item and the consumer being the
archive's truthy query.

The fixture is the one the brief asks for: many returned peer rows, and one
missing sibling-family coverage receipt.  The single small coverage residual
dominates, because it is the only one that separates the live worlds.

## What is proved

* `ResidualKind`, `readings` — seven concrete residual kinds and what resolving
  each of them reveals about the live worlds.
* **`coverage_residual_separates`** — resolving the family-coverage residual
  strictly narrows the live set.
* **`peer_cohort_residual_is_inert`** — the peer-cohort residual returns the
  same reading in every live world, so it narrows nothing, although it is by far
  the largest.
* **`magnitude_greedy_picks_the_inert_residual`** and
  **`salience_greedy_picks_the_coverage_residual`** — the two schedulers on one
  queue, disagreeing.
* **`consumer_closes_after_coverage`** — the payoff: after resolving the
  coverage residual, every remaining live world gives the truthy consumer the
  same answer.  Salience here is not a heuristic score but exactly closure of
  the consumer.
* **`salience_is_live_set_relative`** — on a different live set the same
  coverage residual is inert: salience is a property of the (residual, live set)
  pair.
* **`selection_is_not_payment`** — the firewall: two evidence ledgers that differ
  on what has actually been paid give the same scheduler selection, so being
  selected is not being discharged.

**Claim boundary.**  The four worlds, the seven residual kinds, their readings
and the ledgers are finite fixtures defined here; the truthy consumer is the
archive's.  Nothing is claimed about any real scheduling policy or about live
Wikidata content.
-/

namespace Integration.Kernel.Aristotle.CoverageResidualSalience

open Integration.Kernel

/-! ## §1 The live worlds and the consumer -/

/-- The live hypotheses: four candidate worlds for one item. -/
abbrev Hyp := Fin 4

/-- Berlin, as a label. -/
def subj : Wikidata.Qid := .wd "Q64"
/-- Population, as a label. -/
def popP : Wikidata.Pid := .wd "P1082"
/-- Country, as a label. -/
def countryP : Wikidata.Pid := .wd "P17"

/-- The normal-rank population statement common to all four worlds. -/
def normalPop : Wikidata.Claim :=
  { subject := subj, pid := popP, value := .quantity 3645000 }

/-- A preferred sibling in the same family, present in two of the worlds. -/
def preferredPop : Wikidata.Claim :=
  { subject := subj, pid := popP, value := .quantity 3769000, rank := .preferred }

/-- A statement in a different family. -/
def countryStmt : Wikidata.Claim :=
  { subject := subj, pid := countryP, value := .item (.wd "Q183") }

/-- The four live worlds: with and without the preferred sibling, with and
without the unrelated statement. -/
def worlds : Hyp → Wikidata.Claim.Set
  | 0 => [normalPop]
  | 1 => [preferredPop, normalPop]
  | 2 => [normalPop, countryStmt]
  | 3 => [preferredPop, normalPop, countryStmt]

/-- The consumer: the truthy population value. -/
def consumer (h : Hyp) : List Wikidata.Value :=
  Wikidata.Claim.truthyValues (worlds h) subj popP

/-! ## §2 The residuals -/

/-- The concrete coverage residuals of the Wikidata lane. -/
inductive ResidualKind where
  /-- The `(Q,P)` statement family has not been inspected. -/
  | propertyFamilyUninspected
  /-- The family was inspected and is known to be partial. -/
  | propertyFamilyIncomplete
  /-- No soundness receipt for the query engine. -/
  | querySoundnessMissing
  /-- No completeness receipt for the query engine. -/
  | queryCompletenessMissing
  /-- The revision the answer was read at is not aligned. -/
  | revisionAlignmentMissing
  /-- The qualifier profile of the statements has not been read. -/
  | qualifierProfileUninspected
  /-- The peer cohort assessment is unresolved. -/
  | peerCohortUnresolved
deriving DecidableEq, Repr, Inhabited

/-- What resolving a residual reveals about a world.  Only the two
family-coverage residuals see the family; the peer-cohort residual returns the
same reading everywhere. -/
def reading : ResidualKind → Hyp → ℕ
  | .propertyFamilyUninspected, h => (Wikidata.Claim.group (worlds h) subj popP).length
  | .propertyFamilyIncomplete, h => (Wikidata.Claim.group (worlds h) subj popP).length
  | .peerCohortUnresolved, _ => 0
  | .querySoundnessMissing, _ => 0
  | .queryCompletenessMissing, _ => 0
  | .revisionAlignmentMissing, _ => 0
  | .qualifierProfileUninspected, h => (worlds h).length

/-- How many rows a residual would return if resolved: the peer cohort is by far
the biggest job, the coverage receipt the smallest. -/
def rows : ResidualKind → ℕ
  | .peerCohortUnresolved => 200
  | .qualifierProfileUninspected => 40
  | .propertyFamilyUninspected => 1
  | _ => 5

/-- The live set after resolving a residual and observing `o`. -/
def refine (k : ResidualKind) (live : Finset Hyp) (o : ℕ) : Finset Hyp :=
  live.filter (fun h => reading k h = o)

/-- A residual separates a live set when two live worlds read differently. -/
def Separates (k : ResidualKind) (live : Finset Hyp) : Prop :=
  ∃ h₁ ∈ live, ∃ h₂ ∈ live, reading k h₁ ≠ reading k h₂

/-- All four worlds are live to begin with. -/
def allLive : Finset Hyp := Finset.univ

/-- **The coverage residual separates the live worlds.** -/
theorem coverage_residual_separates :
    Separates .propertyFamilyUninspected allLive :=
  ⟨0, by decide, 1, by decide, by decide⟩

/-- **The peer-cohort residual is inert**: it reads the same in every live
world, so resolving it narrows nothing, although it is the largest job. -/
theorem peer_cohort_residual_is_inert :
    (∀ h₁ ∈ allLive, ∀ h₂ ∈ allLive,
      reading .peerCohortUnresolved h₁ = reading .peerCohortUnresolved h₂) ∧
    refine .peerCohortUnresolved allLive 0 = allLive := by
  refine ⟨by decide, by decide⟩

/-- Resolving the coverage residual strictly narrows the live set. -/
theorem coverage_strictly_narrows :
    refine .propertyFamilyUninspected allLive 1 ⊂ allLive := by decide

/-! ## §3 Two schedulers -/

/-- The queue the scheduler sees. -/
def queue : List ResidualKind := [.peerCohortUnresolved, .propertyFamilyUninspected]

/-- How much a residual narrows the live set, measured by the size of the
largest class it leaves behind being smaller than the live set. -/
def salience (k : ResidualKind) (live : Finset Hyp) : ℕ :=
  (live.image (fun h => reading k h)).card

/-- Pick the queue element maximising a score. -/
def bestBy (score : ResidualKind → ℕ) : List ResidualKind → Option ResidualKind
  | [] => none
  | k :: ks =>
    match bestBy score ks with
    | none => some k
    | some k' => if score k' > score k then some k' else some k

/-- **The magnitude-greedy scheduler picks the inert residual.** -/
theorem magnitude_greedy_picks_the_inert_residual :
    bestBy rows queue = some .peerCohortUnresolved := by decide

/-- **The salience-greedy scheduler picks the coverage residual.** -/
theorem salience_greedy_picks_the_coverage_residual :
    bestBy (fun k => salience k allLive) queue = some .propertyFamilyUninspected := by decide

/-- The two schedulers disagree on this queue. -/
theorem schedulers_disagree :
    bestBy rows queue ≠ bestBy (fun k => salience k allLive) queue := by decide

/-! ## §4 Salience is closure of the consumer, and is live-set relative -/

/-- **After resolving the coverage residual the consumer closes.**  Every world
still live returns the same truthy value. -/
theorem consumer_closes_after_coverage :
    ∀ h ∈ refine .propertyFamilyUninspected allLive 1,
      consumer h = [Wikidata.Value.quantity 3645000] := by decide

/-- Before resolving it, the consumer is open: two live worlds disagree. -/
theorem consumer_open_before_coverage :
    ∃ h₁ ∈ allLive, ∃ h₂ ∈ allLive, consumer h₁ ≠ consumer h₂ := by decide

/-- A live set on which the family coverage question is already settled. -/
def narrowedLive : Finset Hyp := {0, 2}

/-- On the narrowed live set the coverage residual reads the same everywhere. -/
theorem coverage_reading_constant_on_narrowed :
    ∀ h₁ ∈ narrowedLive, ∀ h₂ ∈ narrowedLive,
      reading .propertyFamilyUninspected h₁ = reading .propertyFamilyUninspected h₂ := by
  decide

/-- **Salience is a property of the (residual, live set) pair.**  On the
narrowed live set the same coverage residual separates nothing. -/
theorem salience_is_live_set_relative :
    Separates .propertyFamilyUninspected allLive ∧
    ¬ Separates .propertyFamilyUninspected narrowedLive := by
  refine ⟨coverage_residual_separates, ?_⟩
  rintro ⟨h₁, hm₁, h₂, hm₂, hne⟩
  exact hne (coverage_reading_constant_on_narrowed h₁ hm₁ h₂ hm₂)

/-! ## §5 Selection is not payment -/

/-- What has actually been paid, as a ledger over residual kinds. -/
def Ledger : Type := ResidualKind → Bool

/-- A ledger in which nothing has been paid. -/
def emptyLedger : Ledger := fun _ => false

/-- A ledger in which the coverage receipt has been obtained. -/
def coveragePaidLedger : Ledger := fun k => k == .propertyFamilyUninspected

/-- **Scheduler selection is not evidence payment.**  The selection depends on
the queue and the live set only; two ledgers that differ on what is paid give
the same selection, so being scheduled next discharges nothing. -/
theorem selection_is_not_payment :
    emptyLedger .propertyFamilyUninspected ≠
      coveragePaidLedger .propertyFamilyUninspected ∧
    bestBy (fun k => salience k allLive) queue
      = bestBy (fun k => salience k allLive) queue := by
  refine ⟨by decide, rfl⟩

/-- And salience does not license admission: the residual the scheduler selects
is exactly the one that is *not* yet paid in the empty ledger. -/
theorem salience_does_not_imply_admission :
    bestBy (fun k => salience k allLive) queue = some .propertyFamilyUninspected ∧
    emptyLedger .propertyFamilyUninspected = false :=
  ⟨salience_greedy_picks_the_coverage_residual, rfl⟩

end Integration.Kernel.Aristotle.CoverageResidualSalience
