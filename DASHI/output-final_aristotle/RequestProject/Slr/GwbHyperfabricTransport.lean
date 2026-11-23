import RequestProject.Slr.GwbTypedSemanticFibre

/-!
Source-indexed GWB discourse/hyperfabric fragment algebra.

This is a Lean parity cut for the existing Agda
SensibLawPersistentStatementObservationEventSpineExact,
SensibLawAntecedentIdentityRefinementBidiExact and
ConsumerDescentMinimalObserverExact owners.

A fragment may be stitched with another fragment ONLY when both are
indexed by the same ORIGINAL checked source receipt. Its members are
proof-relevant subsets of rows already verified by native SLR/GWB checks.
The algebra does not infer who a pronoun refers to, that events coincide,
or that an event historically occurred.
-/

namespace Wikidata
namespace Slr
namespace GwbHyperfabric

open GwbTypedFibre
open Lean

/-- A discourse fragment is a list of ORIGINAL certified sentence rows,
not merely an arbitrary list carrying an asserted revision string. -/
structure Fragment
    {article : String} {slr projection receipt : Json}
    (checked : CheckedRows article slr projection receipt) where
  rows : List SentenceObservation
  allRowsFromOriginal :
    ∀ row ∈ rows, row ∈ checked.rows.toList

/-- Full article semantic-observation carrier. -/
def whole
    {article : String} {slr projection receipt : Json}
    (checked : CheckedRows article slr projection receipt) :
    Fragment checked where
  rows := checked.rows.toList
  allRowsFromOriginal := by
    intro row h
    exact h

/-- A source-faithful operation: one fragment cannot acquire sentences
from a different parser revision through concatenation. -/
def join
    {article : String} {slr projection receipt : Json}
    {checked : CheckedRows article slr projection receipt}
    (left right : Fragment checked) : Fragment checked where
  rows := left.rows ++ right.rows
  allRowsFromOriginal := by
    intro row h
    rcases List.mem_append.mp h with hl | hr
    · exact left.allRowsFromOriginal row hl
    · exact right.allRowsFromOriginal row hr

/-- Restriction keeps only original rows; the predicate selects rows for
a consumer, not new evidence or semantic authority. -/
def restrict
    {article : String} {slr projection receipt : Json}
    {checked : CheckedRows article slr projection receipt}
    (fragment : Fragment checked)
    (predicate : SentenceObservation → Bool) : Fragment checked where
  rows := fragment.rows.filter predicate
  allRowsFromOriginal := by
    intro row h
    exact fragment.allRowsFromOriginal row (List.mem_filter.mp h).1

theorem joinRetainsLeft
    {article : String} {slr projection receipt : Json}
    {checked : CheckedRows article slr projection receipt}
    (left right : Fragment checked)
    (row : SentenceObservation) (h : row ∈ left.rows) :
    row ∈ (join left right).rows := by
  exact List.mem_append.mpr (Or.inl h)

theorem joinRetainsRight
    {article : String} {slr projection receipt : Json}
    {checked : CheckedRows article slr projection receipt}
    (left right : Fragment checked)
    (row : SentenceObservation) (h : row ∈ right.rows) :
    row ∈ (join left right).rows := by
  exact List.mem_append.mpr (Or.inr h)

/-- Commuting restriction/aggregation square, using the SAME checked source.
    A duplicate row remains duplicated: this is provenance accumulation,
not semantic identity-based deduplication. -/
theorem restrictionCommutesWithJoin
    {article : String} {slr projection receipt : Json}
    {checked : CheckedRows article slr projection receipt}
    (left right : Fragment checked)
    (predicate : SentenceObservation → Bool) :
    (restrict (join left right) predicate).rows =
      (join (restrict left predicate) (restrict right predicate)).rows := by
  simp [restrict, join, List.filter_append]

/-- The full source certificate is never weakened by local restriction
or by a source-preserving cross-sentence join. -/
theorem anyFragmentRetainsOriginalReceipt
    {article : String} {slr projection receipt : Json}
    {checked : CheckedRows article slr projection receipt}
    (fragment : Fragment checked) :
    GwbNativeFibre.checkRealGwbNativeFibreReceipt
      article slr projection receipt = true :=
  GwbTypedFibre.typedRowsRemainSourceBound checked

/-- Agda identity-refinement parity: candidate narrowing does NOT silently
close the distinct semantic-identity coordinate. -/
structure MentionFibre where
  mentionRef : String
  candidateReferents : List String
  candidateHistory : List (List String)
  resolvedIdentity : Option String
  deriving Repr

/-- Refinement retains the previous candidate state as provenance. -/
def narrowMention (before : MentionFibre)
    (retains : String → Bool) : MentionFibre :=
  { before with
    candidateReferents := before.candidateReferents.filter retains
    candidateHistory := before.candidateReferents :: before.candidateHistory }

theorem narrowingPreservesIdentity (before : MentionFibre)
    (retains : String → Bool) :
    (narrowMention before retains).resolvedIdentity =
      before.resolvedIdentity := rfl

theorem narrowingIntroducesNoReferent (before : MentionFibre)
    (retains : String → Bool) (candidate : String)
    (h : candidate ∈ (narrowMention before retains).candidateReferents) :
    candidate ∈ before.candidateReferents := by
  exact (List.mem_filter.mp h).1

theorem narrowingRetainsOldCandidateHistory (before : MentionFibre)
    (retains : String → Bool) :
    before.candidateReferents ∈
      (narrowMention before retains).candidateHistory := by
  simp [narrowMention]

end GwbHyperfabric
end Slr
end Wikidata
