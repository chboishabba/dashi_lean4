import RequestProject.Slr.GwbProductionTrace
import RequestProject.Slr.GwbCanonicalSourceProof
import RequestProject.Slr.GwbRelationTransport
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
import RequestProject.Slr.GwbP4ArticleEndToEnd
import RequestProject.Slr.GwbP5P10ExactWeld

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
    if (json.getObjVal? "reporting_clauses").isOk then
      if hReport : Slr.checkNativeReportingRows json observed = true then
        let _ := Slr.checkedNativeReportingRowsExact json observed hReport
        IO.println "GWB_DB_M12_REPORTING_REFERENCE_PARITY_OK"
      else
        IO.eprintln "GWB_DB_M12_REPORTING_REFERENCE_PARITY_REJECTED"
        return 1
    else
      IO.println "GWB_DB_M12_LEGACY_NO_REPORTING_PROJECTION"
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
  let mut sourceRecords : List (String × Lean.Json) := []
  let graphSha ← IO.Process.output { cmd := "sha256sum", args := #[graphPath] }
  if graphSha.exitCode != 0 || (← IO.FS.readFile graphPath) != text then
    IO.eprintln "GWB_WORLD_GRAPH_REJECTED: source graph digest/readback"
    return 1
  let graphDigest := (graphSha.stdout.splitOn " ").head!
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
    let path := Cli.cachePath (System.FilePath.mk cacheDir) qid
    let sha ← IO.Process.output { cmd := "sha256sum", args := #[path.toString] }
    if sha.exitCode != 0 || (← IO.FS.readFile path) != raw then
      IO.eprintln s!"GWB_WORLD_GRAPH_REJECTED: snapshot digest/readback {qid}"
      return 1
    let snapshot := Lean.Json.mkObj [
      ("qid", toJson qid),
      ("wikidata_lastrevid", toJson revision),
      ("revision_available", toJson (revision != 0)),
      ("source_sha256", toJson ((sha.stdout.splitOn " ").head!)),
      ("cache_path", toJson path.toString),
      ("original_candidate_node", node)
    ]
    snapshots := snapshots.push snapshot
    sourceRecords := (qid, record) :: sourceRecords
  let pkb := Slr.GwbWorldGraph.pkbFromImportedEntities entities
  let inventory := Slr.GwbWorldGraph.checkGraphAgainstImportedKB graph pkb
  let mut supported : Nat := 0
  let mut unresolved : Array Lean.Json := #[]
  let mut edgeReceipts : Array Lean.Json := #[]
  let mut originalStatementContextCount : Nat := 0
  for (edge, proof?) in inventory do
    let source := (edge.getObjValAs? String "source").toOption.getD ""
    let property := (edge.getObjValAs? String "property_id").toOption.getD ""
    let target := (edge.getObjValAs? String "target").toOption.getD ""
    let record := (sourceRecords.lookup source).getD Lean.Json.null
    let claims := (record.getObjVal? "claims").toOption.getD Lean.Json.null
    let rows := (claims.getObjValAs? (Array Lean.Json) property).toOption.getD #[]
    -- Reuse the original JMD JSON import's value/rank rules. Preserve the
    -- whole native statement (GUID, rank, main snak, qualifiers, references)
    -- and its ordinal, including deprecated matches as excluded evidence.
    let mut context : Array Lean.Json := #[]
    let mut admitted : Nat := 0
    let mut ordinal : Nat := 0
    for row in rows do
      if Cli.statementValueId? row == some target then
        let imported := Cli.statementRank row != "deprecated"
        if imported then admitted := admitted + 1
        context := context.push (Lean.Json.mkObj [
          ("property_statement_ordinal", toJson ordinal),
          ("jmd_imported_item_statement", toJson imported),
          ("original_statement", row)])
      ordinal := ordinal + 1
    let jmdSupported := proof?.isSome
    match proof? with
    | some proof =>
        let _ := Slr.GwbWorldGraph.checkedWorldPropertySound proof
        supported := supported + 1
        -- This PKB constructor has no extra subproperty edges. Refuse to
        -- publish a positive property result without its raw import inverse.
        if admitted == 0 then
          IO.eprintln "GWB_WORLD_GRAPH_REJECTED: supported edge has no original nondeprecated item statement"
          return 1
    | none => unresolved := unresolved.push edge
    originalStatementContextCount := originalStatementContextCount + context.size
    let snapshot := (snapshots.toList.find? fun s =>
      (s.getObjValAs? String "qid").toOption == some source).getD Lean.Json.null
    edgeReceipts := edgeReceipts.push (Lean.Json.mkObj [
      ("source_edge_ordinal", toJson edgeReceipts.size),
      ("original_candidate_edge", edge),
      ("source_snapshot", snapshot),
      ("jmd_property_supported", toJson jmdSupported),
      ("direct_imported_statement_count", toJson admitted),
      ("matching_original_statement_contexts", Lean.Json.arr context),
      ("qualifier_alignment_paid", toJson false),
      ("world_truth_paid", toJson false)
    ])
  if edgeReceipts.size != inventory.size || supported + unresolved.size != inventory.size then
    IO.eprintln "GWB_WORLD_GRAPH_REJECTED: edge inventory accounting"
    return 1
  let summary := Lean.Json.mkObj [
    ("schema", toJson ("gwb-jmd-world-graph-property-verification-v1" : String)),
    ("source_graph_schema", toJson ("slr-wikimedia-world-follow-v1" : String)),
    ("source_graph_sha256", toJson graphDigest),
    ("edge_receipts", Lean.Json.arr edgeReceipts),
    ("matching_original_statement_context_count", toJson originalStatementContextCount),
    ("all_edge_ordinals_retained", toJson true),
    ("qualifier_alignment_paid", toJson false),
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

/-- P4 end-to-end original-source proof: exact original Wikipedia
    parser/revision, JMD Q207 sitelink, native Rust fibre and automatically
    constructed source-only SourceQueryLicence. -/
def runArticleP4Check
    (articlePath slrPath projectionPath nativePath wikidataPath : String) :
    IO UInt32 := do
  let article ← IO.FS.readFile articlePath
  let slrText ← IO.FS.readFile slrPath
  let projectionText ← IO.FS.readFile projectionPath
  let nativeText ← IO.FS.readFile nativePath
  let wikidataText ← IO.FS.readFile wikidataPath
  match Lean.Json.parse slrText, Lean.Json.parse projectionText,
        Lean.Json.parse nativeText, Lean.Json.parse wikidataText with
  | .ok slr, .ok projection, .ok native, .ok wikidata =>
      if hRoot : Slr.GwbArticleIdentity.checkGwbRootIdentity
          article slr projection wikidata = true then
        if hNative : Slr.GwbNativeFibre.checkRealGwbNativeFibreReceipt
            article slr projection native = true then
          let root : Slr.GwbArticleIdentity.CheckedGwbRootIdentity
              article slr projection wikidata := ⟨hRoot⟩
          let original : Slr.GwbNativeFibre.CheckedRealGwbNativeFibre
              article slr projection native := ⟨hNative⟩
          match Slr.GwbTypedFibre.decodeCheckedRows? original with
          | none =>
              IO.eprintln "GWB_P4_ARTICLE_REJECTED: incomplete original typed fibre"
              return 1
          | some rows =>
              let _ := Slr.GwbP4Article.originalGwbArticlePositiveSourceQuery
                root rows (.candidateKind "Role(Actor)")
              let _ := Slr.GwbP4Article.sourceActorCandidatesAndReferenceResiduals
                root rows
              let count := Slr.GwbP4.sourceAnswer rows.rows.toList
                (.candidateKind "Role(Actor)")
              IO.println s!"GWB_P4_ORIGINAL_ARTICLE_SOURCE_LICENCE_KERNEL_OK sentences={rows.rows.size} actor_role_candidates={count}"
              IO.println "Q207/article and original Rust fibre checked; positive query is source-syntactic only"
              return 0
        else
          IO.eprintln "GWB_P4_ARTICLE_REJECTED: native Rust receipt was not source bound"
          return 1
      else
        IO.eprintln "GWB_P4_ARTICLE_REJECTED: Q207/article source correspondence failed"
        return 1
  | _, _, _, _ =>
      IO.eprintln "GWB_P4_ARTICLE_REJECTED: invalid input JSON"
      return 1

/-- Real bounded article-to-property agreement. No caller-supplied
    review flag, synthetic PKB, or historical truth promotion. -/
def runOfficeClaimCheck
    (articlePath slrPath projectionPath rootPath officePath outputPath : String) :
    IO UInt32 := do
  let ok ← Slr.ArticleProof.verifyFiles articlePath slrPath projectionPath
  if !ok then return 1
  let article ← IO.FS.readFile articlePath
  let sha ← IO.Process.output { cmd := "sha256sum", args := #[articlePath] }
  let rootSha ← IO.Process.output { cmd := "sha256sum", args := #[rootPath] }
  let officeSha ← IO.Process.output { cmd := "sha256sum", args := #[officePath] }
  let digest := (sha.stdout.splitOn " ").head!
  if sha.exitCode != 0 || rootSha.exitCode != 0 || officeSha.exitCode != 0 ||
      digest != "a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233" then
    IO.eprintln "GWB_OFFICE_CLAIM_REJECTED: original source or snapshot digest"
    return 1
  match Lean.Json.parse (← IO.FS.readFile slrPath),
        Lean.Json.parse (← IO.FS.readFile projectionPath),
        Lean.Json.parse (← IO.FS.readFile rootPath),
        Lean.Json.parse (← IO.FS.readFile officePath) with
  | .ok slr, .ok projection, .ok root, .ok office =>
    if hRoot : Slr.GwbArticleIdentity.checkGwbRootIdentity
          article slr projection root = true then
      if !Slr.GwbWorldGraph.jsonEntityMatchesQid "Q207" root then
        IO.eprintln "GWB_OFFICE_CLAIM_REJECTED: root EntityData inventory"
        return 1
      let some rootRev := Slr.GwbArticleSystem.entityRevision root "Q207"
        | IO.eprintln "GWB_OFFICE_CLAIM_REJECTED: root revision absent"
          return 1
      let some officeRev := Slr.GwbArticleSystem.entityRevision office "Q11696"
        | IO.eprintln "GWB_OFFICE_CLAIM_REJECTED: office revision absent"
          return 1
      if rootRev == 0 || officeRev == 0 then return 1
      if hClaim : Slr.GwbArticleSystem.officeClaim article = true then
        if hLabel : Slr.GwbArticleSystem.officeLabelChecked office = true then
          if hSupport : Slr.GwbArticleSystem.officePropertySupported root office = true then
            let checked : Slr.GwbArticleIdentity.CheckedGwbRootIdentity
              article slr projection root := ⟨hRoot⟩
            let _ := Slr.GwbArticleSystem.checkedOfficeClaimAndKB
              checked hClaim hLabel hSupport
            let qualified := Slr.GwbWorldGraph.qualifiedYearRows root "Q207" "P39" "Q11696" 2001 2009
            let yearSupport := !qualified.isEmpty
            for statement in qualified.attach do
              let _ := Slr.GwbArticleSystem.checkedOfficeClaimAndQualifiedYears
                checked hClaim hLabel hSupport statement.property
            IO.FS.writeFile outputPath ((Lean.Json.mkObj [
              ("schema", toJson ("gwb-bounded-office-claim-kb-agreement-v1" : String)),
              ("source_revision", toJson ("enwiki-revid:1385850169" : String)),
              ("source_sha256", toJson digest),
              ("source_start_char", toJson (0 : Nat)),
              ("source_end_char", toJson Slr.GwbArticleSystem.officeLead.toList.length),
              ("source_literal", toJson Slr.GwbArticleSystem.officeLead),
              ("subject", toJson ("Q207" : String)),
              ("property", toJson ("P39" : String)),
              ("object", toJson ("Q11696" : String)),
              ("root_revision", toJson rootRev),
              ("root_sha256", toJson ((rootSha.stdout.splitOn " ").head!)),
              ("office_revision", toJson officeRev),
              ("office_sha256", toJson ((officeSha.stdout.splitOn " ").head!)),
              ("scope", toJson ("bounded-explicit-lead-rule-and-independent-kb-support" : String)),
              ("year_interval_consumer", toJson ("P580/P582 Gregorian year only" : String)),
              ("source_start_year", toJson (2001 : Nat)),
              ("source_end_year", toJson (2009 : Nat)),
              ("bounded_year_interval_alignment_paid", toJson yearSupport),
              ("matching_original_year_interval_statements", toJson qualified),
              ("year_interval_disposition", toJson (if yearSupport then "matched" else "unresolved")),
              ("governed_identity_paid", toJson false),
              ("general_semantic_alignment_paid", toJson false),
              ("qualifier_alignment_paid", toJson false),
              ("world_truth_paid", toJson false)]).pretty ++ "\n")
            IO.println "GWB_BOUNDED_OFFICE_CLAIM_JMD_AGREEMENT_OK"
            return 0
          else
            IO.eprintln "GWB_OFFICE_CLAIM_REJECTED: independent P39 support absent"
            return 1
        else
          IO.eprintln "GWB_OFFICE_CLAIM_REJECTED: office entity or label mismatch"
          return 1
      else
        IO.eprintln "GWB_OFFICE_CLAIM_REJECTED: exact source rule not matched"
        return 1
    else
      IO.eprintln "GWB_OFFICE_CLAIM_REJECTED: original Q207/article mismatch"
      return 1
  | _, _, _, _ =>
    IO.eprintln "GWB_OFFICE_CLAIM_REJECTED: invalid input JSON"
    return 1

/-- Independent article observation and original KB interval witnesses.
    This is a generic indexed producer, not an automatic semantic alignment.
    Preserve complete original rows and original statement qualifiers. -/
def runIndexedArticleKBCheck
    (articlePath slrPath projectionPath entityPath subject property target
      kind value startStr endStr outputPath : String) : IO UInt32 := do
  let some startYear := startStr.toNat? | return 2
  let some endYear := endStr.toNat? | return 2
  let some query := Slr.ArticleProof.parseArticleQuery? kind value | return 2
  let article ← IO.FS.readFile articlePath
  let sha ← IO.Process.output { cmd := "sha256sum", args := #[articlePath] }
  let kbSha ← IO.Process.output { cmd := "sha256sum", args := #[entityPath] }
  let slrSha ← IO.Process.output { cmd := "sha256sum", args := #[slrPath] }
  let projectionSha ← IO.Process.output { cmd := "sha256sum", args := #[projectionPath] }
  if sha.exitCode != 0 || kbSha.exitCode != 0 || slrSha.exitCode != 0 ||
      projectionSha.exitCode != 0 then return 1
  let digest := (sha.stdout.splitOn " ").head!
  match Lean.Json.parse (← IO.FS.readFile slrPath),
        Lean.Json.parse (← IO.FS.readFile projectionPath),
        Lean.Json.parse (← IO.FS.readFile entityPath) with
  | .ok slr, .ok projection, .ok entity =>
    let manifestation := (slr.getObjVal? "manifestation").toOption.getD Lean.Json.null
    if (manifestation.getObjValAs? String "source_text_sha256").toOption != some digest ||
        (projection.getObjValAs? String "source_text_sha256").toOption != some digest then
      return 1
    let some checked := Slr.ArticleProof.checkedIndexedArticle? subject article slr projection
      | return 1
    let some revision := Slr.GwbArticleSystem.entityRevision entity subject | return 1
    if revision == 0 || !Slr.GwbWorldGraph.jsonEntityMatchesQid subject entity then return 1
    let rows := Slr.ArticleProof.queryIndexedArticle checked query
    for row in rows.attach do
      let _ := Slr.ArticleProof.indexedArticleQuerySound checked query row.val row.property
    let qualified := Slr.GwbWorldGraph.originalQualifiedYearWitnesses
      entity subject property target startYear endYear
    for witness in qualified do
      let _ := Slr.GwbWorldGraph.originalQualifiedYearWitnessSound witness
      let _ := Slr.GwbWorldGraph.checkedWorldPropertySound witness.propertyProof
    let propertySupported := (Slr.GwbWorldGraph.originalEntityPropertyProof?
      entity subject property target).isSome
    IO.FS.writeFile outputPath ((Lean.Json.mkObj [
      ("schema", toJson ("jmd-indexed-independent-article-kb-v1" : String)),
      ("source_sha256", toJson digest),
      ("source_revision", (slr.getObjVal? "revision_ref").toOption.getD Lean.Json.null),
      ("source_unit_ref", (slr.getObjVal? "source_unit_ref").toOption.getD Lean.Json.null),
      ("slr_sha256", toJson ((slrSha.stdout.splitOn " ").head!)),
      ("projection_sha256", toJson ((projectionSha.stdout.splitOn " ").head!)),
      ("entity_sha256", toJson ((kbSha.stdout.splitOn " ").head!)),
      ("entity_revision", toJson revision),
      ("subject", toJson subject), ("property", toJson property), ("object", toJson target),
      ("query_kind", toJson kind), ("query_value", toJson value),
      ("original_observation_rows", toJson rows),
      ("start_year", toJson startYear), ("end_year", toJson endYear),
      ("independent_property_supported", toJson propertySupported),
      ("original_qualified_statements", toJson (qualified.map (fun w => w.statement))),
      ("interval_supported", toJson (!qualified.isEmpty)),
      ("semantic_alignment_paid", toJson false), ("governed_identity_paid", toJson false),
      ("world_truth_paid", toJson false)]).pretty ++ "\n")
    return 0
  | _, _, _ => return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["native-trace", article, source, projection, executable, parserRun,
      statement, document, revision, region, startStr, endStr, literal, event, output] =>
      match startStr.toNat?, endStr.toNat? with
      | some startChar, some endChar =>
          Slr.GwbProductionTrace.run article source projection executable parserRun
            statement document revision region literal event output startChar endChar
      | _, _ => return 2
  | ["relation-check", article, source, projection, receipt] =>
      Slr.GwbRelationTransport.run article source projection receipt
  | ["canonical-populate", article, source, projection, output] =>
      Slr.GwbCanonicalSource.run article source projection output
  | ["fibre"] =>
      IO.println "GWB_FIBRE_THEOREMS_KERNEL_OK"
      IO.println "PROVED: source-claim/year-string consumer closure; four semantic nonfactorability countermodels; ACI fibre join retains provenance"
      IO.println "NOT PROVED HERE: GWB article semantic admission, reviewed S28 event identity, world occurrence"
      return 0
  | ["indexed-article-kb-check", article, slr, projection, entity, subject,
      property, target, kind, value, startYear, endYear, output] =>
      runIndexedArticleKBCheck article slr projection entity subject property target
        kind value startYear endYear output
  | ["article-p4-check", article, slr, projection, native, wikidata] =>
      runArticleP4Check article slr projection native wikidata
  | ["article-office-check", article, slr, projection, root, office, output] =>
      runOfficeClaimCheck article slr projection root office output
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
  | ["article-query", article, source, projection, kind, value] =>
      let ok ← Slr.ArticleProof.verifyFiles article source projection (some (kind, value))
      return if ok then 0 else 1
  | "article-check" :: rest =>
      runArticleCheck rest
  | _ =>
      IO.eprintln "usage: indexed-article-kb-check ARTICLE SLR PROJECTION ENTITY SUBJECT PROPERTY TARGET KIND VALUE START_YEAR END_YEAR OUTPUT | fibre | composition | axioms | article-query ARTICLE SLR_RECORD PROJECTION KIND VALUE | article-check ARTICLE SLR_RECORD PROJECTION | semantic-scope ARTICLE SLR_RECORD PROJECTION | rust-fibre-check ARTICLE SLR_RECORD PROJECTION NATIVE_JSON | db-m12-check DB_M12_JSON EXACT_LITERAL | db-s28-check S28_JSON EVENT_REF | world-graph-check[-offline] WORLD_JSON ENTITY_CACHE OUTPUT_JSON | world-graph-strict WORLD_JSON ENTITY_CACHE OUTPUT_JSON | article-qid-check ARTICLE SLR_RECORD PROJECTION WIKIDATA_Q207_JSON | article-office-check ARTICLE SLR_RECORD PROJECTION Q207_JSON Q11696_JSON OUTPUT"
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

#print axioms Wikidata.Slr.GwbP4Article.originalGwbArticlePositiveSourceQuery
#print axioms Wikidata.Slr.GwbP4Article.sourceActorCandidatesAndReferenceResiduals

#print axioms Wikidata.Slr.GwbP5P10.p5OriginalSourceSurvivesReview
#print axioms Wikidata.Slr.GwbP5P10.p6PreservesBothOriginalChecks
#print axioms Wikidata.Slr.GwbP5P10.p8ConsumerAnswerSound
#print axioms Wikidata.Slr.GwbP5P10.p9AlignmentRetainsIndependentChecks
#print axioms Wikidata.Slr.GwbP5P10.p10AllEdgesJmdSupported
#print axioms Wikidata.Slr.GwbP5P10.fullChainKeepsSeparateEvidence

#print axioms Wikidata.Slr.GwbCanonicalSource.anchorRetainsOriginal
#print axioms Wikidata.Slr.GwbCanonicalSource.predicateQuerySound

#print axioms Wikidata.Slr.GwbProductionTrace.checkedTraceSound
#print axioms Wikidata.Slr.GwbProductionTrace.temporalQueryOriginal

#print axioms Wikidata.Slr.ArticleProof.queryCheckedArticleExact
#print axioms Wikidata.Slr.ArticleProof.checkedArticleQuerySound

#print axioms Wikidata.Slr.GwbCanonicalSource.licensedPredicateQuerySound
#print axioms Wikidata.Slr.GwbCanonicalSource.reportingReadingInvariant
#print axioms Wikidata.Slr.GwbCanonicalSource.checkedReportingAnswerSound
#print axioms Wikidata.Slr.GwbArticleSystem.checkedOfficeClaimAndKB

#print axioms Wikidata.Slr.checkedNativeReportingRowsExact

#print axioms Wikidata.Slr.GwbWorldGraph.qualifiedYearRowsExact
#print axioms Wikidata.Slr.GwbArticleSystem.checkedOfficeClaimAndQualifiedYears
