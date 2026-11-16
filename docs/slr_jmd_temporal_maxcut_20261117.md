# SLR → JMD Lean: source-licensed document/event/temporal queries
**Status: 17 November 2026.** Implementation and acceptance roadmap. Nothing here
turns parser evidence, an S28 review reference, or a Lean import into world truth.

## Ownership and existing reusable results

- Agda golden: `DASHI/Core/ConsumerDescentMinimalObserverExact.agda`,
  `DASHI/Reasoning/SemanticConsumerRelativeClosureExact.agda`,
  `DASHI/Core/IntersectionalNonFactorability.agda`.
- Agda parser/PNF: `SpacyDependencyToCandidateLogicalPNFExact`,
  `SensibLawAttributedSourcePNFCandidateWeldExact`,
  `SensibLawSemanticStatusProductExact`.
- Agda event/time/revision: `SensibLawAttributionPropositionOccurrenceBidiExact`,
  `SensibLawPersistentStatementObservationEventSpineExact`,
  `SensibLawChronologyContestationSpineExact`, `SentenceParagraphNaturalDeltaExact`,
  `HierarchicalDeltaFusionExact`.
- Source runtime: `chboishabba/slr`; original DB-native M12
  `compile_db_statement_pnf_checked`, S28 claim/temporal/contestation store,
  and M12 source/observation/event links. Avoid duplicate parsers.
- JMD Wikidata prover: `RequestProject/Cli/Fetch.lean`, `Enrich.lean`,
  `Derive.lean`, `PropertyEngine.lean`, `PropertyConstraints.lean`,
  `StatementConstraints.lean`, `Queries.lean`. Original author attribution:
  meta-introspector/JMD. The extension must not imply that JMD independently
  proved natural-language interpretation.

## Source-backed integration made in this cut

- SLR PR #78 `pnf-db-checked`: existing DB-native M12 compiler and exact
  parser source-literal, source-revision, token/head/entity/compilation parity.
  Output contains full parser observations, source coordinates, and
  **candidate-only** status. The old TSV route is compatibility-only.
- SLR PR #78 `timeline-candidates`: read-only original S28 temporal assertions,
  claim leaves and contestation; reopens M12 source statements and
  statement→observation→event links; calculates `source_trace_join_complete`
  without claiming identity, semantic admission, or world-event occurrence.
- JMD Lean `Slr/DbSourceProducer.lean`: direct subprocess invocation with
  exact run, revision, region and receipt checks, nested non-promotion
  validation. `Cli/Tool.lean` exposes `slr-db-pnf` and `slr-timeline`.
- JMD Lean `Slr/DocumentQuerySound.lean`: observation-polymorphic
  `SourceQueryLicence`, consumer factorisation across observational fibres,
  disagreement/collision obstruction, and conditional document-query soundness.
- JMD Lean `Slr/TemporalDocumentProof.lean`: conditional, context-indexed
  transitive closure; acyclicity requirement; non-collapse negative controls;
  append-only evidence preservation. This is *not* yet a licensed S28 edge
  extraction or a proof of a real-world event order.

## Phase gates, deliverables and acceptance tests

| Phase | Deliverable | Status | Acceptance |
|---|---|---|---|
| P0 | Existing golden Agda semantic/event/chronology owners located | Present | Exact imports and ownership retained |
| P1 | Real M12 source/parser observation exposed directly to Lean | Source written; live verification OPEN | Run DB fixtures against exact PostgreSQL source/revision, prove forged head/digest/run/region fail |
| P2 | M12→semantic fibre and consumer-specific licence | OPEN | A reviewed/resolved source interpretation gives checked `SourceQueryLicence`; wrong scope/QID/predicate rejected |
| P3 | Event roles, identity, trace to persisted source | Trace carriers wired; positive semantic join OPEN | Roles and co-reference backed by exact dependency + resolution witness; shared person/date alone rejected |
| P4 | Scoped time, consistency, correction, current reading | Abstract closure/source traces wired; concrete S28→Lean semantic proof OPEN | Relative before/after path certificate within account; cross-account leakage and cycles rejected; correction retains prior evidence |
| P5 | Sentence→paragraph→page→article sufficient summary | Abstract Agda laws present; actual PNF instantiation OPEN | Incremental=fused for selected query; no lost attribution/time; counterexample blocks coarse summary |
| P6 | JMD Lean checked answer and trustworthy SLR evidence payment | Generic conditional theorem source written; executable/kernel OPEN | Recompute answer from source, kernel-check exact proof, authenticate checker/artifact and dependency revisions; replay after edit |

### Exact remaining lemma instances

1. `m12ObservationExactSource`: direct M12 run, revision, region,
   literal and token/entity coordinates match persisted source. Rust checked
   compiler exists; execute it on real DB fixture (P1).
2. `slrCandidateSemanticResolutionLicensed`: actual parser dependency and
   reviewed source/context resolution inhabit existing Agda semantic fibre (P2).
3. `consumerSpecificFactorisationPaid`: actual source→observation fibres
   preserve the requested query, or return an explicit counterexample/residual
   (P2/P5). The Lean implication currently takes this proof as an input.
4. `licensedEventRoleExtractionSound`: dependencies, negation and scoped
   event roles correspond to selected/admissible PNF (P3).
5. `reviewedEventIdentityJoinSound`: a same-event join is backed by reviewed
   source/observation relationship, not shared label/QID/time (P3).
6. `licensedTemporalAssertionSoundOnS28`: original S28 TemporalForm joined
   to the same event/account/speaker and source-bound selected reading (P4).
7. `scopedTemporalOrderClosureSoundOnS28`: only licence-bearing compatible
   edges may enter closure; reject cycles as strict order (P4).
8. `temporalCorrectionPreservesHistoryAndCurrentReading`: S28 supersession/
   contestation retains prior claim and computes consumer-relative current
   reading without erasing source or manufacturing occurrence (P4).
9. `sentenceParagraphPNFTransportNaturality`: concrete SLR PNF deltas
   instantiate existing Agda fusion law (P5).
10. `pageArticleQueryFactorsThroughSummary`: selected mention/event/time/order
    consumers factor through retained source summaries or return WrongType (P5).
11. `slrJmdDocumentQuerySoundInstantiated`: generic Lean theorem paid by actual
    producer→reading→query correspondences and JMD's checked evaluator (P6).
12. `authenticatedKernelReceiptPaysExactDemand`: original SLR formal-evidence
    DB accepts only an actually executed and independently checked proof tied
    to source, checker, artifact, target proposition and dependencies (P6).

## Critical trust distinctions

- Raw candidate ≠ reviewed candidate ≠ semantic licence ≠ document assertion
  ≠ occurrence ≠ legal/world truth.
- Text order ≠ narrator order ≠ account-relative asserted event order
  ≠ independently admitted world-event order.
- A review reference is not a proof of what a sentence means.
- S28 `source_trace_join_complete` is a provenance check, not semantic
  sufficiency, source authority or a truth oracle.
- The existing SLR formal proof bridge checks a `kernel-certified` string in
  its receipt validation. That string alone is **not independently authenticated
  kernel execution**; P6 requires an actual checker invocation and verified
  artifact/demand binding.
- Arbitrary text cannot be promised a unique admitted interpretation. A
  consumer may nevertheless close when all admissible readings agree; otherwise
  preserve residuals and ask for evidence.

## Evidence as of this review

Local Python/SymPy: 2,145 finite-model event/order checks; 13 source-unit
PNF structural checks; 32 new DB M12/S28 synthetic handoff checks (28 negative).
The newer checks are *fixtures*, not a PostgreSQL or Rust run. Python syntax
checks pass. No `rustc`, `cargo`, `lean`, `lake`, `agda`, trained spaCy
model, or database is available in the current local runtime. GitHub returned
no completed exact-head CI runs. Accordingly none of P1-P6 is claimed closed
by independent runtime/kernel acceptance.

## Execution order at the next machine with required toolchains

1. Check exact SLR PR #78 with `cargo test -p sensiblaw-cli` and
   `cargo test -p sensiblaw-pg-source-store`; run M12 against a retained
   PostgreSQL fixture including adversarial source/revision/token changes.
2. Compile JMD Lean's existing `wikidata` target with its pinned Lake
   toolchain. Invoke `slr-db-pnf`, `slr-timeline`; replay parser and source
   counterexamples with falsified receipts and check exit failures.
3. Reopen Mabo fixtures first (reporting, negation, condition, viewpoint),
   then GWB reviewed event/account and chronology candidates.
4. Prove P2-P5 *concrete* semantics in Agda and their Lean equivalent,
   reusing existing factorisation, scope, chronology and fusion owners.
5. Run full arbitrary-source→candidate→licensed query→kernel answer→exact
   SLR formal-evidence-payment replay, including source and KB edits.

Everything above is an integration/verification task; do not introduce a
parallel ontology, temporal algebra, or parser.
