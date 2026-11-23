import RequestProject.Slr.GwbHyperfabricTransport
import RequestProject.Slr.DocumentQuerySound

/-!
GWB P4 — positive, real-receipt, source-relative consumer certificate.

This module does NOT create a second SLR interpretation engine. It exposes
queries on the ORIGINAL source-bound typed Rust rows, and proves that those
queries factor through that exact observation even when identity, occurrence
and temporal interpretations remain unresolved.

The real source receipt is checked in GwbNativeFibreReceipt, decoded without
dropping any candidate/alternative/residual in GwbTypedSemanticFibre, and
source-indexed by GwbHyperfabricTransport. The universal query licence
below is then applied to that SAME source object.

The result is a positive SourceQueryLicence for *source-only* claims. It
does not certify who an actor was, whether an event occurred, an event date,
a clause interpretation, or all production-live semantic readings.
-/

namespace Wikidata
namespace Slr
namespace GwbP4

open GwbTypedFibre
open GwbHyperfabric
open Lean

/-- Source-only questions expressible from the checked original rows.
    Kind labels are SLR-produced syntactic classifications; no actor
    identity or historical claim is introduced by asking for a count. -/
inductive SourceQuery where
  | sentences
  | candidates
  | alternatives
  | residuals
  | candidateKind (kind : String)
  | residualKind (kind : String)
  deriving Repr, DecidableEq

private def countCandidates (rows : List SentenceObservation) : Nat :=
  rows.foldl (fun n row => n + row.candidates.size) 0

private def countAlternatives (rows : List SentenceObservation) : Nat :=
  rows.foldl (fun n row => n + row.alternatives.size) 0

private def countResiduals (rows : List SentenceObservation) : Nat :=
  rows.foldl (fun n row => n + row.residuals.size) 0

private def countCandidateKind
    (rows : List SentenceObservation) (kind : String) : Nat :=
  rows.foldl (fun n row =>
    n + (row.candidates.toList.filter (fun c => c.kind == kind)).length) 0

private def countResidualKind
    (rows : List SentenceObservation) (kind : String) : Nat :=
  rows.foldl (fun n row =>
    n + (row.residuals.toList.filter (fun r => r.kind == kind)).length) 0

/-- Real typed-row consumer, not a hand-entered answer. -/
def sourceAnswer (rows : List SentenceObservation) : SourceQuery → Nat
  | .sentences => rows.length
  | .candidates => countCandidates rows
  | .alternatives => countAlternatives rows
  | .residuals => countResiduals rows
  | .candidateKind kind => countCandidateKind rows kind
  | .residualKind kind => countResidualKind rows kind

/-- Abstract unresolved semantic coordinates. These are intentionally
    independent of original SLR source observations and are NOT reviewed
    interpretations of the GWB article. -/
structure Reading where
  originalRows : List SentenceObservation
  identityPending : Bool
  eventPending : Bool
  timePending : Bool

/-- A source-observer model for the original typed SLR product. All
    compatible interpretations are kept live: the source-only query is
    independent of the three unresolved semantic coordinates. -/
def sourceModel : DocumentQueryModel
    (List SentenceObservation) (List SentenceObservation)
    Reading SourceQuery Nat where
  observe := id
  live := fun source reading => reading.originalRows = source
  documentAnswer := sourceAnswer
  readingAnswer := fun reading => sourceAnswer reading.originalRows

/-- Positive consumer licence. No finite enumeration or unique semantic
    interpretation is assumed, hence there is no fake coverage Boolean. -/
def sourceOnlyLicence (rows : List SentenceObservation) (query : SourceQuery) :
    SourceQueryLicence sourceModel rows query where
  observation := rows
  sameProducedObservation := rfl
  chosenReading := ⟨rows, false, false, false⟩
  chosenIsLive := rfl
  consumerFactorises := by
    intro otherSource h
    exact congrArg (fun s => sourceAnswer s query) h
  consumerClosed := by
    intro reading h
    exact congrArg (fun s => sourceAnswer s query) h

/-- For every query, the original source-observed answer is licensed
    independently of unresolved actor/event/time choices. -/
theorem sourceOnlyAnswerSound
    (rows : List SentenceObservation) (query : SourceQuery) :
    sourceModel.documentAnswer rows query = sourceAnswer rows query := by
  exact slrJmdDocumentQuerySound
    (sourceOnlyLicence rows query) (sourceAnswer rows query) rfl

/-- Two distinct unresolved semantic states remain live on exactly the
    same original rows and have the same licensed *source-only* answer.
    This is not a claim about what those states mean in the world. -/
theorem unresolvedAxesDoNotChangeSourceAnswer
    (rows : List SentenceObservation) (query : SourceQuery) :
    let x : Reading := ⟨rows, false, false, false⟩
    let y : Reading := ⟨rows, true, true, true⟩
    sourceModel.live rows x ∧ sourceModel.live rows y ∧
    x.identityPending ≠ y.identityPending ∧
    sourceModel.readingAnswer x query =
      sourceModel.readingAnswer y query := by
  simp [sourceModel]

/-- The positive licence consumes original, completely decoded and
    source-checked GWB rows, not a toy list fabricated for the theorem. -/
def checkedSourceLicence
    {article : String} {slr projection receipt : Json}
    (checked : CheckedRows article slr projection receipt)
    (query : SourceQuery) :
    SourceQueryLicence sourceModel checked.rows.toList query :=
  sourceOnlyLicence checked.rows.toList query

/-- A source-indexed hyperfabric fragment can be queried without losing
    original row ancestry. Joining fragments is source-preserving, not a
    semantic actor identity or event-equivalence operation. -/
def fragmentSourceLicence
    {article : String} {slr projection receipt : Json}
    {checked : CheckedRows article slr projection receipt}
    (fragment : Fragment checked) (query : SourceQuery) :
    SourceQueryLicence sourceModel fragment.rows query :=
  sourceOnlyLicence fragment.rows query

/-- This is the P4 same-object maximum-cut theorem: the original GWB Rust
    receipt remains checked, hyperfabric row provenance is retained, and
    a positive consumer-specific document result follows. -/
theorem checkedGwbP4SourceLicenceSound
    {article : String} {slr projection receipt : Json}
    (checked : CheckedRows article slr projection receipt)
    (fragment : Fragment checked) (query : SourceQuery) :
    GwbNativeFibre.checkRealGwbNativeFibreReceipt
      article slr projection receipt = true ∧
    (∀ row ∈ fragment.rows, row ∈ checked.rows.toList) ∧
    sourceModel.documentAnswer fragment.rows query =
      sourceAnswer fragment.rows query := by
  exact ⟨anyFragmentRetainsOriginalReceipt fragment,
    fragment.allRowsFromOriginal,
    slrJmdDocumentQuerySound
      (fragmentSourceLicence fragment query)
      (sourceAnswer fragment.rows query) rfl⟩

/-- Positive source consumer persists after two original fragments join;
    the proof does NOT identify their actors/events. -/
theorem joinedFragmentHasPositiveLicence
    {article : String} {slr projection receipt : Json}
    {checked : CheckedRows article slr projection receipt}
    (left right : Fragment checked) (query : SourceQuery) :
    sourceModel.documentAnswer (join left right).rows query =
      sourceAnswer (join left right).rows query :=
  (checkedGwbP4SourceLicenceSound checked
    (join left right) query).2.2

end GwbP4
end Slr
end Wikidata
