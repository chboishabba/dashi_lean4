import RequestProject.Slr.WikipediaArticleProof

/-!
# Actual GWB source-backed counterexample to flat scope consumer sufficiency

This is deliberately NOT another NLP interpreter, identity resolver or
semantic-fibre producer. It checks the ORIGINAL saved dependency rows and
the lossily projected scope labels for the same supplied article.
The counterexample is to a FLAT OBSERVER ONLY; SLR's full graph may retain
the distinctions and is not refuted by this result.
-/

namespace Wikidata
namespace Slr
namespace GwbRealSource

open Lean

structure ScopeWitness where
  sentenceIndex : Nat
  predicateIndex : Nat
  predicateSurface : String
  parentSurface : String
  sourceEventRef : String
  scopeLabel : String
  parentEmbedded : Bool
  deriving Repr

private def str? (j : Json) (key : String) : Option String :=
  (j.getObjValAs? String key).toOption

private def nat? (j : Json) (key : String) : Option Nat :=
  (j.getObjValAs? Nat key).toOption

private def arr? (j : Json) (key : String) : Option (Array Json) :=
  (j.getObjValAs? (Array Json) key).toOption

private def parentEmbed? (raw : Json) : Option Bool := do
  let kind ← str? raw "dep"
  if (["acl", "relcl", "ccomp", "xcomp", "advcl"].contains kind) then
    some true
  else if kind == "ROOT" then
    some false
  else
    none

/-- Exact parser-parent evidence for a projected source event. A label
    on its own is never allowed to construct a parent-embedding witness. -/
def witness? (slr event : Json) : Option ScopeWitness := do
  let sentences ← arr? slr "pnf_candidates"
  let idx ← nat? event "sentence_index"
  let cid ← str? event "slr_claim_candidate_id"
  let sourceEventRef ← str? event "event_candidate_ref"
  let scopeLabel ← str? event "scope"
  let predicate ← (event.getObjVal? "predicate").toOption
  let i ← nat? predicate "i"
  let candidate ← sentences.toList.find? (fun x =>
    nat? x "sentence_index" == some idx &&
    str? x "claim_candidate_id" == some cid)
  let rows ← arr? candidate "dependency_rows"
  let row ← rows.toList.find? (fun x =>
    nat? x "i" == some i &&
    str? x "text" == str? predicate "surface" &&
    nat? x "idx" == nat? predicate "start_char" &&
    str? x "dep" == some "conj")
  let head ← nat? row "head_i"
  let parent ← rows.toList.find? (fun x => nat? x "i" == some head)
  let embedded ← parentEmbed? parent
  let predicateSurface ← str? row "text"
  let parentSurface ← str? parent "text"
  some ⟨idx, i, predicateSurface, parentSurface,
    sourceEventRef, scopeLabel, embedded⟩

/-- Find a *source backed* pair of events with one flat scope label, but
    distinct answers to q='is its syntactic parent an embedded predicate?'. -/
def collision? (slr projection : Json) :
    Option (ScopeWitness × ScopeWitness) := do
  let events ← arr? projection "event_candidates"
  let witnesses := events.toList.filterMap (witness? slr)
  witnesses.findSome? (fun a =>
    witnesses.findSome? (fun b =>
      if a.scopeLabel == b.scopeLabel &&
          a.parentEmbedded != b.parentEmbedded then
        some (a, b)
      else none))

/-- The consumer cannot factor through the flattened scope label for any
    such pair. This makes the same-observation/different-answer failure an
    actual proved impossibility, rather than a heuristic annotation. -/
theorem flatScopeCannotAnswerEmbeddedParent
    (a b : ScopeWitness)
    (same : a.scopeLabel = b.scopeLabel)
    (different : a.parentEmbedded ≠ b.parentEmbedded) :
    ¬ ∃ (consumer : String → Bool),
        consumer a.scopeLabel = a.parentEmbedded ∧
        consumer b.scopeLabel = b.parentEmbedded := by
  intro h
  cases h with
  | intro consumer evidence =>
    exact different
      (evidence.1.symm.trans ((congrArg consumer same).trans evidence.2))

/-- Checked only if the complete original article projection was source
    verified by the separately kernel-checked WikipediaArticleProof module. -/
def sourceBoundCollision? (article : String) (slr projection : Json) :
    Option (ScopeWitness × ScopeWitness) :=
  if ArticleProof.checkProjection article slr projection then
    collision? slr projection
  else none

end GwbRealSource
end Slr
end Wikidata
