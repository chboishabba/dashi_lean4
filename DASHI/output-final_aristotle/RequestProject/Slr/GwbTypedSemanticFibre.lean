import RequestProject.Slr.GwbNativeFibreReceipt

/-!
Typed, source-indexed consumer view of the original GWB SLR Rust receipt.

This is a decoder of the EXISTING original candidate/alternative/residual
records, not a new semantic parser or a claim that emitted alternatives
exhaust possible readings. Source and parser authority remain in the
imported GwbNativeFibre.checkRealGwbNativeFibreReceipt proof.

The decoder fails on any unrecognised/missing required structural field;
it never filters away failed rows to make a partial result appear total.
-/

namespace Wikidata
namespace Slr
namespace GwbTypedFibre

open Lean

private def str? (j : Json) (key : String) : Option String :=
  (j.getObjValAs? String key).toOption
private def nat? (j : Json) (key : String) : Option Nat :=
  (j.getObjValAs? Nat key).toOption
private def bool? (j : Json) (key : String) : Option Bool :=
  (j.getObjValAs? Bool key).toOption
private def arr? (j : Json) (key : String) : Option (Array Json) :=
  (j.getObjValAs? (Array Json) key).toOption

structure Candidate where
  ordinal : Nat
  sourceStart : Nat
  sourceStop : Nat
  kind : String
  sourceRevision : Nat
  candidateOnly : Bool
  deriving Repr

structure Alternative where
  ordinal : Nat
  sentenceIndex : Nat
  choices : Array String
  semanticAdmissionPaid : Bool
  deriving Repr

structure Residual where
  ordinal : Nat
  sentenceIndex : Nat
  kind : String
  consumerClosed : Bool
  deriving Repr

structure SentenceObservation where
  sentenceIndex : Nat
  candidates : Array Candidate
  alternatives : Array Alternative
  residuals : Array Residual
  deriving Repr

private def decodeCandidate? (j : Json) : Option Candidate := do
  let ordinal ← nat? j "token_ordinal"
  let span ← arr? j "source_span"
  if span.size != 2 then none else do
    let start ← span[0]!.getNat?.toOption
    let stop ← span[1]!.getNat?.toOption
    let kind ← str? j "kind"
    let revision ← nat? j "source_revision"
    let candidateOnly ← bool? j "candidate_only"
    if !candidateOnly || start >= stop then none
    else some ⟨ordinal, start, stop, kind, revision, candidateOnly⟩

private def decodeAlternative? (j : Json) : Option Alternative := do
  let ordinal ← nat? j "token_ordinal"
  let sentence ← nat? j "sentence_index"
  let choices ← (j.getObjValAs? (Array String) "alternatives").toOption
  let paid ← bool? j "semantic_admission_paid"
  if paid || choices.isEmpty then none
  else some ⟨ordinal, sentence, choices, paid⟩

private def decodeResidual? (j : Json) : Option Residual := do
  let ordinal ← nat? j "token_ordinal"
  let sentence ← nat? j "sentence_index"
  let kind ← str? j "kind"
  let closed ← bool? j "consumer_closed"
  if closed then none
  else some ⟨ordinal, sentence, kind, closed⟩

private def decodeSentence? (j : Json) : Option SentenceObservation := do
  let sentence ← nat? j "sentence_index"
  let rawCandidates ← arr? j "candidates"
  let rawAlternatives ← arr? j "alternative_fibres"
  let rawResiduals ← arr? j "residuals"
  let candidates ← rawCandidates.mapM decodeCandidate?
  let alternatives ← rawAlternatives.mapM decodeAlternative?
  let residuals ← rawResiduals.mapM decodeResidual?
  if !(alternatives.all fun a => a.sentenceIndex == sentence) ||
     !(residuals.all fun r => r.sentenceIndex == sentence) then none
  else some ⟨sentence, candidates, alternatives, residuals⟩

/-- Preserve every original array element or reject the whole proof view. -/
def decodeObservations? (receipt : Json) :
    Option (Array SentenceObservation) := do
  let observations ← arr? receipt "sentence_observations"
  observations.mapM decodeSentence?

/-- Source-bound typed view, still expressly *candidate-only*. -/
structure CheckedRows
    (article : String) (slr projection receipt : Json) where
  sourceProof : GwbNativeFibre.CheckedRealGwbNativeFibre
    article slr projection receipt
  rows : Array SentenceObservation
  extractedExactly : decodeObservations? receipt = some rows

/-- The real GWB checker is a necessary premise for typed extraction.
    No review licence is constructed here. -/
def decodeCheckedRows?
    {article : String} {slr projection receipt : Json}
    (sourceProof : GwbNativeFibre.CheckedRealGwbNativeFibre
      article slr projection receipt) :
    Option (CheckedRows article slr projection receipt) :=
  match h : decodeObservations? receipt with
  | some rows =>
      some { sourceProof := sourceProof, rows := rows, extractedExactly := h }
  | none => none

theorem typedRowsRemainSourceBound
    {article : String} {slr projection receipt : Json}
    (checked : CheckedRows article slr projection receipt) :
    GwbNativeFibre.checkRealGwbNativeFibreReceipt
      article slr projection receipt = true :=
  GwbNativeFibre.checkedGwbFibreObservationsRetainResiduals
    checked.sourceProof

/-- Totals are computed from *all* typed rows and can be compared with
    original Rust counters without dropping any undecodable residual. -/
def totals (rows : Array SentenceObservation) : Nat × Nat × Nat :=
  rows.foldl (fun (c, a, r) row =>
    (c + row.candidates.size,
     a + row.alternatives.size,
     r + row.residuals.size)) (0, 0, 0)

end GwbTypedFibre
end Slr
end Wikidata
