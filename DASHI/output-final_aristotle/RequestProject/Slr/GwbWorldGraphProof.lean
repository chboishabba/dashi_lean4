import RequestProject.Slr.Proof
import RequestProject.Cli.Fetch

/-!
Source-checked GWB Wikimedia world graph → JMD item-property proofs.

Input: the ORIGINAL SLR gwb-wikimedia-world-graph.json
(schema slr-wikimedia-world-follow-v1), not a novel generated ontology.
For each graph edge, independently reopen JMD's original cached
Special:EntityData QID JSON and re-import its item-valued claims.
The native SLR graph explicitly does not preserve Wikidata statement
context, so it is never taken as a property proof.

A supported result is only relative to the independently imported
JMD snapshot. No assertion of historical truth, synchronous multi-QID
snapshot, paragraph meaning, same-actor identity, or world occurrence.

Original JMD importer/getter/property theorem: meta-introspector.
SLR GWB world follow and Agda roadmap: chboishabba.
-/

namespace Wikidata
namespace Slr
namespace GwbWorldGraph

open Lean

private def str? (j : Json) (field : String) : Option String :=
  (j.getObjValAs? String field).toOption

private def bool? (j : Json) (field : String) : Option Bool :=
  (j.getObjValAs? Bool field).toOption

private def nat? (j : Json) (field : String) : Option Nat :=
  (j.getObjValAs? Nat field).toOption

private def arr? (j : Json) (field : String) : Option (Array Json) :=
  (j.getObjValAs? (Array Json) field).toOption

/-- The exact limited SLR world-follow ABI. These rows are acquisition
candidates, not checked statements in the JMD KB. -/
def checkCandidateWorldGraph (graph : Json) : Bool :=
  let nodes := (arr? graph "nodes").getD #[]
  let edges := (arr? graph "item_property_edges").getD #[]
  let summary := (graph.getObjVal? "summary").toOption.getD Json.null
  let ids := nodes.toList.map (fun node => str? node "node_id")
  str? graph "schema" == some "slr-wikimedia-world-follow-v1" &&
  bool? graph "candidate_only" == some true &&
  bool? graph "semantic_promotion" == some false &&
  !nodes.isEmpty && !edges.isEmpty &&
  ids.all (fun id => id.isSome && !(id.getD "").isEmpty) &&
  decide ids.Nodup &&
  nodes.toList.all (fun node =>
    bool? node "identity_coordinate_only" == some true) &&
  edges.toList.all (fun edge =>
    (match str? edge "source", str? edge "property_id",
           str? edge "target" with
     | some source, some property, some target =>
         ids.contains (some source) &&
         source.startsWith "Q" && property.startsWith "P" &&
         target.startsWith "Q"
     | _, _, _ => false) &&
    bool? edge "semantic_promotion" == some false &&
    bool? edge "native_statement_context_retained" == some false) &&
  nat? summary "qid_node_count" == some nodes.size &&
  nat? summary "item_property_edge_count" == some edges.size

structure CheckedCandidateWorldGraph (graph : Json) where
  checked : checkCandidateWorldGraph graph = true

theorem candidateWorldGraphNeverClaimsNativeStatementContext
    {graph : Json} (receipt : CheckedCandidateWorldGraph graph) :
    checkCandidateWorldGraph graph = true :=
  receipt.checked

/-- The JMD native imported PKB is constructed from item-valued,
nondeprecated properties in the exact independently fetched EntityData
responses; it is NOT constructed from the acquisition graph edges.
The public JMD property proof checks every positive relation below. -/
def pkbFromImportedEntities (entities : List Cli.Entity) : PKB :=
  let statements := entities.flatMap fun entity =>
    entity.claims.map fun (p, target) =>
      (Pid.wd p, Qid.wd entity.id, Qid.wd target)
  { base := Cli.kbOfEntities "GWB independently checked Wikidata snapshots" entities
    props := (statements.map fun item => item.1).dedup
    stmts := statements }

/-- Proof-relevant positive result for an imported JMD KB. -/
structure CheckedWorldProperty where
  pkb : PKB
  property : Pid
  subject : Qid
  object : Qid
  supported : pkb.supportsB property subject object = true

theorem checkedWorldPropertySound (witness : CheckedWorldProperty) :
    ∃ p, (p, witness.subject, witness.object) ∈ witness.pkb.stmts ∧
      witness.pkb.isSubPropertyOf p witness.property = true :=
  PKB.supportsB_iff.mp witness.supported

/-- This separately checks the original JMD getter identity: the actual
returned EntityData is not accepted merely because it was stored as QID.json.
The getter can use its existing offline/cache path. -/
def jsonEntityMatchesQid (qid : String) (json : Json) : Bool :=
  let entities := Cli.entitiesOfJson json
  entities.length == 1 &&
  entities.any (fun e => e.id == qid)

/-- A graph edge is a proved JMD relation only when the independent PKB
derived from EntityData supports it. Never attach this certificate merely
because the SLR world-follow graph contains the same triple. -/
def proofForEdge? (kb : PKB) (edge : Json) :
    Option CheckedWorldProperty := do
  let src ← str? edge "source"
  let property ← str? edge "property_id"
  let target ← str? edge "target"
  let p := Pid.wd property
  let s := Qid.wd src
  let o := Qid.wd target
  if h : kb.supportsB p s o = true then
    some ⟨kb, p, s, o, h⟩
  else
    none

/-- The local source-object validator is kernel-auditable. -/
theorem propertyOfCheckedEdgeSound
    {kb : PKB} {edge : Json} {w : CheckedWorldProperty}
    (h : proofForEdge? kb edge = some w) :
    ∃ p, (p, w.subject, w.object) ∈ w.pkb.stmts ∧
      w.pkb.isSubPropertyOf p w.property = true :=
  checkedWorldPropertySound w

/-- Report individual supported and still-unverified graph edges. A missing
target or changed live statement is a research obligation, NOT refutation. -/
def checkGraphAgainstImportedKB (graph : Json) (kb : PKB) :
    Array (Json × Option CheckedWorldProperty) :=
  ((arr? graph "item_property_edges").getD #[]).map
    (fun edge => (edge, proofForEdge? kb edge))

/-- The entire edge inventory remains accounted for: supported and
unresolved edges both retain their original source graph row. -/
theorem checkedGraphInventoryExact (graph : Json) (kb : PKB) :
    (checkGraphAgainstImportedKB graph kb).size =
      ((arr? graph "item_property_edges").getD #[]).size := by
  simp [checkGraphAgainstImportedKB]

end GwbWorldGraph
end Slr
end Wikidata
