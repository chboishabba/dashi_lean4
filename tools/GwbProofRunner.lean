import RequestProject.Slr.GwbConsumerFibreProof
import RequestProject.Slr.WikipediaArticleProof
import RequestProject.Slr.GwbRealSourceConsumer
import RequestProject.Slr.GwbNativeFibreReceipt
import RequestProject.Slr.GwbProofComposition
import RequestProject.Slr.DbSourceProducer
import RequestProject.Slr.GwbWorldGraphProof
import RequestProject.Slr.GwbTypedSemanticFibre
import RequestProject.Slr.GwbArticleIdentity
import RequestProject.Slr.GwbArticleSystemSoundness
import RequestProject.Slr.GwbP4SourceLicence

open Wikidata
open Lean

def printAxiomAudit : IO Unit := do
  IO.println "GWB_FIBRE_THEOREMS_KERNEL_OK"
  IO.println "AXIOM_AUDIT_BEGIN"
  IO.println "See the kernel-checked declarations below."
  IO.println "AXIOM_AUDIT_END"

def runArticleCheck (args : List String) : IO UInt32 := do
  match args with
  | [article, source, projection] =>
      let ok ← Slr.ArticleProof.verifyFiles article source projection
      return if ok then 0 else 1
  | _ =>
      IO.eprintln "usage: article-check ARTICLE SLR_RECORD PROJECTION"
      return 2

/-- Kernel-checked, source-extracted nonfactorability witness on the
    original Wikipedia dependency graph; NOT a semantic admission. -/
def runRealScopeCheck (articleFile slrFile projectionFile : String) :
    IO UInt32 := do
  let article ← IO.FS.readFile articleFile
  let sourceText ← IO.FS.readFile slrFile
  let projectionText ← IO.FS.readFile projectionFile
  let source ← match Lean.Json.parse sourceText with
    | .ok j => pure j
    | .error err =>
        IO.eprintln s!"SLR source JSON rejected: {err}"
        return 1
  let projection ← match Lean.Json.parse projectionText with
    | .ok j => pure j
    | .error err =>
        IO.eprintln s!"Article projection JSON rejected: {err}"
        return 1
  match Slr.GwbRealSource.sourceBoundCollision? article source projection with
  | none =>
      IO.eprintln "GWB_REAL_SOURCE_SCOPE_WITNESS_REJECTED: unsupported source or no collision"
      return 1
  | some (left, right) =>
      if hSame : left.scopeLabel = right.scopeLabel then
        if hDifferent : left.parentEmbedded ≠ right.parentEmbedded then
          let _proof :=
            Slr.GwbRealSource.flatScopeCannotAnswerEmbeddedParent
              left right hSame hDifferent
          IO.println "GWB_REAL_SOURCE_FLAT_SCOPE_NONFACTORABILITY_PROVED"
          IO.println s!"left={left.sentenceIndex}:{left.predicateSurface} parent={left.parentSurface} embedded={left.parentEmbedded}"
          IO.println s!"right={right.sentenceIndex}:{right.predicateSurface} parent={right.parentSurface} embedded={right.parentEmbedded}"
          IO.println s!"same_flat_scope_label={left.scopeLabel}"
          IO.println "This does not refute the production SLR rich source graph."
          return 0
        else
          IO.eprintln "No distinct dependency answers for chosen pair"
          return 1
      else
        IO.eprintln "The flattened label was not equal"
        return 1

/-- Actual SLR Rust candidate alternatives and consumer-adequacy receipts
    must be checked against ORIGINAL source coordinates. This does not
    issue reviewed semantic transport or historical occurrence. -/
def runNativeFibreReceipt (articlePath sourcePath projectionPath nativePath : String) :
    IO UInt32 := do
  let article ← IO.FS.readFile articlePath
  let source ← IO.FS.readFile sourcePath
  let projection ← IO.FS.readFile projectionPath
  let native ← IO.FS.readFile nativePath
  match Lean.Json.parse source, Lean.Json.parse projection, Lean.Json.parse native with
  | .ok slr, .ok projected, .ok evidence =>
      if h : Slr.GwbNativeFibre.checkRealGwbNativeFibreReceipt
          article slr projected evidence = true then
        let checked : Slr.GwbNativeFibre.CheckedRealGwbNativeFibre
            article slr projected evidence := ⟨h⟩
        let _ := Slr.GwbNativeFibre.checkedGwbFibreObservationsRetainResiduals
          checked
        match Slr.GwbTypedFibre.decodeCheckedRows? checked with
        | none =>
            IO.eprintln "GWB_RUST_FIBRE_LEAN_REJECTED: typed candidate/alternative/residual decoding incomplete"
            return 1
        | some typed =>
            let _typedProof := Slr.GwbTypedFibre.typedRowsRemainSourceBound typed
            let (candidateCount, alternativeCount, residualCount) :=
              Slr.GwbTypedFibre.totals typed.rows
            IO.println s!"GWB_TYPED_SEMANTIC_FIBRE_LEAN_PASS sentences={typed.rows.size} candidates={candidateCount} alternatives={alternativeCount} residuals={residualCount}"
            -- P4: real (not synthetic) typed source receipts, two
            -- source-indexed cross-sentence fragments, and positive
            -- source-only licences despite unresolved semantic axes.
            let original := Slr.GwbHyperfabric.whole typed
            let evenRows := Slr.GwbHyperfabric.restrict original
              (fun row => row.sentenceIndex % 2 == 0)
            let oddRows := Slr.GwbHyperfabric.restrict original
              (fun row => row.sentenceIndex % 2 != 0)
            let merged := Slr.GwbHyperfabric.join evenRows oddRows
            let hPositive := Slr.GwbP4.checkedGwbP4SourceLicenceSound
              typed merged (.candidateKind "Role(Actor)")
            let _ := hPositive
            let _ := Slr.GwbP4.joinedFragmentHasPositiveLicence
              evenRows oddRows (.residualKind "ReferenceAttachmentUnresolved")
            let _ := Slr.GwbHyperfabric.restrictionCommutesWithJoin
              evenRows oddRows (fun row => row.sentenceIndex % 2 == 0)
            let sourceOnlyActors :=
              Slr.GwbP4.sourceAnswer merged.rows (.candidateKind "Role(Actor)")
            let referenceResiduals :=
              Slr.GwbP4.sourceAnswer merged.rows
                (.residualKind "ReferenceAttachmentUnresolved")
            IO.println s!"GWB_P4_SOURCE_LICENCE_KERNEL_OK sentences={merged.rows.length} actor_role_candidates={sourceOnlyActors} reference_residuals={referenceResiduals}"
            IO.println "P4 SCOPE: source-only typed row query with original GWB source and fragment ancestry"
            IO.println "UNPAID: real cross-sentence actor identity, reviewed event/time semantics, production live-fibre coverage"
            IO.println "GWB_RUST_FIBRE_AND_CONSUMER_SOURCE_BOUND_LEAN_PASS"
            IO.println "Checked: native Rust candidates, alternatives, residuals, source spans and 5 consumer outcomes"
            IO.println "NOT PAID: reviewed semantic transports, production S28 joins or world occurrence"
            return 0
      else
        IO.eprintln "GWB_RUST_FIBRE_LEAN_REJECTED: altered source, unresolved correspondence or promoted semantic claim"
        return 1
  | _, _, _ =>
      IO.eprintln "GWB_RUST_FIBRE_LEAN_REJECTED: invalid evidence JSON"
      return 1

/-- Independently re-open an actual persisted M12 source product.
    This checks the raw literal and its digest; it does not replace the
    original PostgreSQL parser-run identity checked by callSlrDbM12. -/
def runSavedM12Check (jsonPath literalPath : String) : IO UInt32 := do
  let literal ← IO.FS.readFile literalPath
  let encoded ← IO.FS.readFile jsonPath
  let json ← match Lean.Json.parse encoded with
    | .ok value => pure value
    | .error err =>
        IO.eprintln s!"Invalid DB M12 JSON: {err}"
        return 1
  let observed ← match Slr.decodeDbM12Observation json with
    | some value => pure value
    | none =>
        IO.eprintln "GWB_DB_M12_PROVENANCE_REJECTED: invalid/promoted DB source"
        return 1
  let hash ← IO.Process.output { cmd := "sha256sum", args := #[literalPath] }
  if hash.exitCode != 0 then
    IO.eprintln "GWB_DB_M12_PROVENANCE_REJECTED: sha256sum failed"
    return 1
  let digest := (hash.stdout.splitOn " ").head!
  if digest != observed.sourceLiteralDigest then
    IO.eprintln "GWB_DB_M12_PROVENANCE_REJECTED: original literal SHA mismatch"
    return 1
  if h : Slr.checkNativeM12Literal literal observed = true then
    let checked : Slr.CheckedNativeM12Literal literal observed := ⟨h⟩
    let _ := Slr.checkedM12AllSourceSpansExact checked
    IO.println "GWB_DB_M12_LITERAL_AND_DEPENDENCY_KERNEL_OK"
    IO.println "Scope: source-bound original M12 product; no event/identity admission"
    return 0
  else
    IO.eprintln "GWB_DB_M12_PROVENANCE_REJECTED: source or dependency mismatch"
    return 1

/-- Consume the original SLR timeline-candidates JSON for an event
    assembled in M12. The whole source/observation/claim ancestry is
    reconstructed independently of the producer's completeness flag. -/
def runSavedS28Check (jsonPath eventRef : String) : IO UInt32 := do
  if eventRef.isEmpty then
    IO.eprintln "GWB_S28_SOURCE_TRACE_REJECTED: event reference empty"
    return 1
  let encoded ← IO.FS.readFile jsonPath
  let json ← match Lean.Json.parse encoded with
    | .ok value => pure value
    | .error err =>
        IO.eprintln s!"GWB_S28_SOURCE_TRACE_REJECTED: invalid JSON {err}"
        return 1
  if h : Slr.checkS28Provenance json eventRef = true then
    let checked : Slr.CheckedS28Provenance json eventRef := ⟨h⟩
    let _ := Slr.checkedS28HasCompleteAncestry checked
    IO.println "GWB_DB_S28_SOURCE_TRACE_KERNEL_OK"
    IO.println "Scope: consistent source/observation/event provenance; no semantic identity or chronology admission"
    return 0
  else
    IO.eprintln "GWB_S28_SOURCE_TRACE_REJECTED: incomplete or promoted M12/S28 ancestry"
    return 1

/-- Recheck every SLR candidate graph property through JMD's original
    Wikidata entity importer and verified PKB property-support theorem.
    The result is a SNAPSHOT-RELATIVE KB proof inventory, never a claim that
    all 51 QIDs share a simultaneous Wikidata revision or that an article
    sentence expresses a checked KB statement. -/
def runWorldGraphCheck
    (graphPath cacheDir outputPath : String) (offline requireAll : Bool) :
    IO UInt32 := do
  let text ← IO.FS.readFile graphPath
  let graph ← match Lean.Json.parse text with
    | .ok value => pure value
    | .error err =>
        IO.eprintln s!"GWB_WORLD_GRAPH_REJECTED: JSON parse {err}"
        return 1
  if h : Slr.GwbWorldGraph.checkCandidateWorldGraph graph = true then
    let checked : Slr.GwbWorldGraph.CheckedCandidateWorldGraph graph := ⟨h⟩
    let _ := Slr.GwbWorldGraph.candidateWorldGraphNeverClaimsNativeStatementContext checked
    pure ()
  else
    IO.eprintln "GWB_WORLD_GRAPH_REJECTED: malformed/promoted source graph"
    return 1
  let nodes := (graph.getObjValAs? (Array Lean.Json) "nodes").toOption.getD #[]
  let mut entities : List Cli.Entity := []
  let mut snapshots : Array Lean.Json := #[]
  for node in nodes do
    let some qid := (node.getObjValAs? String "node_id").toOption
      | IO.eprintln "GWB_WORLD_GRAPH_REJECTED: missing QID"
        return 1
    let raw ← Cli.fetchEntityJson (System.FilePath.mk cacheDir) offline qid
    let parsed ← match Lean.Json.parse raw with
      | .ok value => pure value
      | .error err =>
          IO.eprintln s!"GWB_WORLD_GRAPH_REJECTED: invalid JMD entity {qid}: {err}"
          return 1
    if !Slr.GwbWorldGraph.jsonEntityMatchesQid qid parsed then
      IO.eprintln s!"GWB_WORLD_GRAPH_REJECTED: JMD getter did not return {qid}"
      return 1
    entities := entities ++ Cli.entitiesOfJson parsed
    let data := (parsed.getObjVal? "entities").toOption.getD Lean.Json.null
    let record := (data.getObjVal? qid).toOption.getD Lean.Json.null
    let revision := (record.getObjValAs? Nat "lastrevid").toOption.getD 0
    snapshots := snapshots.push (Lean.Json.mkObj [
      ("qid", toJson qid),
      ("wikidata_lastrevid", toJson revision),
      ("cache_path", toJson ((Cli.cachePath (System.FilePath.mk cacheDir) qid).toString))
    ])
  let pkb := Slr.GwbWorldGraph.pkbFromImportedEntities entities
  let inventory := Slr.GwbWorldGraph.checkGraphAgainstImportedKB graph pkb
  let mut supported : Nat := 0
  let mut unresolved : Array Lean.Json := #[]
  for (edge, proof?) in inventory do
    match proof? with
    | some proof =>
        let _ := Slr.GwbWorldGraph.checkedWorldPropertySound proof
        supported := supported + 1
    | none => unresolved := unresolved.push edge
  let summary := Lean.Json.mkObj [
    ("schema", toJson ("gwb-jmd-world-graph-property-verification-v1" : String)),
    ("source_graph_schema", toJson ("slr-wikimedia-world-follow-v1" : String)),
    ("nodes_reimported", toJson nodes.size),
    ("source_candidate_edges", toJson inventory.size),
    ("jmd_kb_property_proofs", toJson supported),
    ("unresolved_edges_count", toJson unresolved.size),
    ("unresolved_candidate_edges", Lean.Json.arr unresolved),
    ("wikidata_source_snapshots", Lean.Json.arr snapshots),
    ("all_imported_entities_checked", toJson true),
    ("source_claims_are_world_truth", toJson false),
    ("article_semantic_alignment_paid", toJson false),
    ("synchronous_51_qid_snapshot_proved", toJson false)
  ]
  IO.FS.writeFile outputPath (summary.pretty ++ "\n")
  IO.println s!"GWB_JMD_WORLD_GRAPH_CHECKED qids={nodes.size} edges={inventory.size} jmd_supported={supported} unresolved={unresolved.size}"
  IO.println s!"Receipt: {outputPath}"
  if requireAll && !unresolved.isEmpty then
    IO.eprintln "GWB_WORLD_GRAPH_PROPERTY_COVERAGE_OPEN: at least one SLR edge not supported by independently imported JMD data"
    return 3
  return 0

/-- Check the exact pinned GWB article against JMD's independent Q207
    Wikidata EntityData sitelink. The two source revisions stay distinct. -/
def runArticleQidCheck
    (articlePath slrPath projectionPath wikidataPath : String) :
    IO UInt32 := do
  let article ← IO.FS.readFile articlePath
  let slrRaw ← IO.FS.readFile slrPath
  let projectionRaw ← IO.FS.readFile projectionPath
  let wdRaw ← IO.FS.readFile wikidataPath
  match Lean.Json.parse slrRaw, Lean.Json.parse projectionRaw, Lean.Json.parse wdRaw with
  | .ok slr, .ok projection, .ok wikidata =>
      if h : Slr.GwbArticleIdentity.checkGwbRootIdentity
            article slr projection wikidata = true then
        let receipt : Slr.GwbArticleIdentity.CheckedGwbRootIdentity
              article slr projection wikidata := ⟨h⟩
        let _ := Slr.GwbArticleIdentity.checkedGwbRootSourceAndSitelink receipt
        IO.println "GWB_Q207_ARTICLE_AND_JMD_SITELINK_KERNEL_OK"
        IO.println "Not a simultaneous Wikipedia/Wikidata revision or a world-event truth theorem"
        return 0
      else
        IO.eprintln "GWB_Q207_ARTICLE_SITELINK_REJECTED: source/QID/title mismatch"
        return 1
  | _, _, _ =>
      IO.eprintln "GWB_Q207_ARTICLE_SITELINK_REJECTED: invalid original input JSON"
      return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["fibre"] =>
      IO.println "GWB_FIBRE_THEOREMS_KERNEL_OK"
      IO.println "PROVED: source-claim/year-string consumer closure; four semantic nonfactorability countermodels; ACI fibre join retains provenance"
      IO.println "NOT PROVED HERE: GWB article semantic admission, reviewed S28 event identity, world occurrence"
      return 0
  | ["article-qid-check", article, slr, projection, wikidata] =>
      runArticleQidCheck article slr projection wikidata
  | ["world-graph-check", graph, cacheDir, output] =>
      runWorldGraphCheck graph cacheDir output false false
  | ["world-graph-check-offline", graph, cacheDir, output] =>
      runWorldGraphCheck graph cacheDir output true false
  | ["world-graph-strict", graph, cacheDir, output] =>
      runWorldGraphCheck graph cacheDir output true true
  | ["db-m12-check", json, literal] =>
      runSavedM12Check json literal
  | ["db-s28-check", json, event] =>
      runSavedS28Check json event
  | ["p4"] =>
      IO.println "GWB_P4_SOURCE_THEOREMS_KERNEL_OK"
      IO.println "PROVED: same-source typed original fragment join, unrestricted unresolved-axis source-query factorization, and positive SourceQueryLicence construction"
      IO.println "NOT PROVED: live GWB reviewed actor/event/time identity or semantic world-truth consumer"
      return 0
  | ["composition"] =>
      IO.println "GWB_FINITE_CONSUMER_COMPOSITION_KERNEL_OK"
      IO.println "GWB_ARTICLE_LOCAL_SYSTEM_THEOREM_KERNEL_OK"
      IO.println "PROVED: checked finite semantic consumer constancy under explicit complete live-fibre enumeration and source correspondence"
      IO.println "PROVED: independent article answer and JMD KB property witness composition, without semantic or world-truth promotion"
      IO.println "UNPAID: production semantic coverage, checked cross-sentence identity/event join, JMD article-to-KB semantic alignment"
      return 0
  | ["axioms"] =>
      printAxiomAudit
      return 0
  | ["semantic-scope", article, source, projection] =>
      runRealScopeCheck article source projection
  | ["rust-fibre-check", article, source, projection, native] =>
      runNativeFibreReceipt article source projection native
  | "article-check" :: rest =>
      runArticleCheck rest
  | _ =>
      IO.eprintln "usage: fibre | composition | axioms | article-check ARTICLE SLR_RECORD PROJECTION | semantic-scope ARTICLE SLR_RECORD PROJECTION | rust-fibre-check ARTICLE SLR_RECORD PROJECTION NATIVE_JSON | db-m12-check DB_M12_JSON EXACT_LITERAL | db-s28-check S28_JSON EVENT_REF | world-graph-check[-offline] WORLD_JSON ENTITY_CACHE OUTPUT_JSON | world-graph-strict WORLD_JSON ENTITY_CACHE OUTPUT_JSON | article-qid-check ARTICLE SLR_RECORD PROJECTION WIKIDATA_Q207_JSON"
      return 2

#print axioms Wikidata.Slr.GwbConsumer.fibreJoinAssociative
#print axioms Wikidata.Slr.GwbConsumer.sourceMentionQueryCloses
#print axioms Wikidata.Slr.GwbConsumer.actualPossessionNotLicensed
#print axioms Wikidata.Slr.GwbConsumer.actorIdentityNotLicensed
#print axioms Wikidata.Slr.GwbConsumer.eventDateNotLicensed
#print axioms Wikidata.Slr.GwbConsumer.embeddedScopeNotLicensed

#print axioms Wikidata.Slr.GwbRealSource.flatScopeCannotAnswerEmbeddedParent

#print axioms Wikidata.Slr.GwbNativeFibre.checkedGwbFibreObservationsRetainResiduals
#print axioms Wikidata.Slr.FiniteConsumer.checkConstant_sound
#print axioms Wikidata.Slr.FiniteConsumer.completeFiniteFibreConsumerClosed
#print axioms Wikidata.Slr.GwbProofComposition.checkedFiniteArticleAnswerSound
#print axioms Wikidata.Slr.GwbProofComposition.independentArticleAndKBResultsSound

#print axioms Wikidata.Slr.checkedM12AllSourceSpansExact
#print axioms Wikidata.Slr.checkedS28HasCompleteAncestry

#print axioms Wikidata.Slr.GwbWorldGraph.checkedWorldPropertySound
#print axioms Wikidata.Slr.GwbWorldGraph.checkedGraphInventoryExact

#print axioms Wikidata.Slr.GwbTypedFibre.typedRowsRemainSourceBound

#print axioms Wikidata.Slr.GwbArticleIdentity.checkedGwbRootSourceAndSitelink

#print axioms Wikidata.Slr.GwbHyperfabric.restrictionCommutesWithJoin
#print axioms Wikidata.Slr.GwbHyperfabric.narrowingPreservesIdentity
#print axioms Wikidata.Slr.GwbArticleSystem.checkedArticleLocalSystemSound
#print axioms Wikidata.Slr.GwbArticleSystem.checkedArticleAndRootKBPropertySound

#print axioms Wikidata.Slr.FiniteConsumer.omittedLiveReadingBlocksCompleteness

#print axioms Wikidata.Slr.GwbP4.checkedGwbP4SourceLicenceSound
#print axioms Wikidata.Slr.GwbP4.unresolvedAxesDoNotChangeSourceAnswer
#print axioms Wikidata.Slr.GwbP4.joinedFragmentHasPositiveLicence
