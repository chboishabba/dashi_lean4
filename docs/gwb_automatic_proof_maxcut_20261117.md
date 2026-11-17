# GWB → JMD → SLR → Lean/Agda automatic proof programme
Updated: 2026-11-17 · execution branch: dashi_lean4 PR #112

## Acceptance objective

Given a QID or a Wikipedia article title, automatically obtain a pinned article
revision, check source and Wikidata identity using the existing JMD machinery,
reuse the native SLR parser/M12/semantic candidate evidence, produce typed Lean
proof objects for source-local and cross-sentence consumers, and elaborate
checked KB proofs and unresolved obligations over the discovered GWB world.

The *system theorem* must prove that every certified answer is justified by its
premises. It need NOT claim completeness of all possible historical or
linguistic readings. No parser observation, QID topic anchor, candidate fibre,
review-ref string or JSON success flag independently licenses world truth.

## Current exact-head result

* PR #112 `e1d8df2a87698dc4919424f2f68a91d2facc51c5`: 24 Git-tracked
  receipt files, 643 sentences, 4,190 candidates, 814 alternative fibres,
  15,595 residuals, five consumer outcomes, ten adversarial controls.
* `7a0177a7424b8bf3026f312d70946fa1e2f9a9dc`: reused the existing
  PR #111 `DbSourceProducer.lean`, retaining independent literal-span,
  token-head and S28 provenance-graph checks. The source copied from PR #111
  has *not* been rebuilt in this execution environment.
* `5d590a088df8f1a648c55e5e4bf59cdf8eb747da`: added
  `FiniteConsumerCertificate.lean` with executable list constancy,
  proof-level soundness, explicit completeness requirement and construction
  of the existing `SourceQueryLicence` when all premises are supplied.
  **Source-written; Lean 4.28.0 kernel acceptance pending.**

Earlier Agda runtime roadmap numbers (10 documents / 41,134 sentences /
51 QIDs / 850 property edges) are a *different evidence scope*. Do not
mistake them for the single-article PR #112 certificate.

## Exact cut register

| ID | Obligation | Existing owner | Current gate | Decisive acceptance |
|---|---|---|---|---|
| P3 | Preserve complete original Rust/Lean execution receipts | PR #112 artifacts/gwb-semantic-proof | CLOSED, pushed | Remote digest and complete logs |
| L1 | QID/title ↔ pinned Wikipedia revision/sitelink identity | JMD Wikidata.Identity, Cli.Fetch, Cli.Import | OPEN | Snapshot-bound Lean equality/sitelink witness; title alone insufficient |
| L2 | Wikipedia/source ↔ checked DB-native M12 | Slr.DbSourceProducer, SLR PR #78, PR #111 | SOURCE-WRITTEN REUSE | Lean 4.28.0 compile + real PostgreSQL original parser source receipt + negative controls |
| L3 | Real Rust JSON rows ↔ typed Lean semantic fibre | GwbNativeFibreReceipt, SLR expansion | PARTIAL | Typed dependent witness for all admitted rows, retained alternatives/residuals; no fabricated semantic coverage |
| L4 | Cross-sentence antecedent ↔ actor identity refinement | Agda AntecedentIdentityRefinementBidiExact, SemanticStatusProductExact | AGDA LAW PRESENT, SAME GWB WELD OPEN | Checked actual mentions, governed identity evidence and preserved history; unique candidate alone insufficient |
| L5 | Hyperfabric/local section restrictions and M12 trace | Agda PersistentStatementObservationEventSpineExact, PNFHyperfabric369, SLR canonical evidence | OPEN CONCRETE WELD | Prove commuting same-source joins and consumer-relevant distinctions; carrier alone insufficient |
| L6 | Distinct actor identity vs event equivalence | Agda GWBHeterogeneousChronologyCapstoneExact | OPEN CONCRETE WELD | Separate event-equivalence witness with retained competing source accounts |
| L7 | Event time, source time, scoped chronology | Agda ChronologyContestationSpineExact, Lean TemporalDocumentProof, S28 | OPEN CONCRETE WELD | DB-native S28 trace, licensed temporal relation, scoped acyclicity and uncertainty preservation |
| L8a | Finite-list query constancy → semantic consumer closure | Lean Slr.FiniteConsumerCertificate + DocumentQuerySound | SOURCE WRITTEN; KERNEL PENDING | Build targeted Lean module and run finite positive/negative controls |
| L8b | Real semantic fibre exhaustiveness | SLR native producer/semantic owners | OPEN | Checked proof that *every* production-live reading is represented or that consumer is stable over unenumerated readings |
| L9 | Source proposition ↔ JMD KB property statement | Slr.Proof, JMD PKB.supportsB_iff, JMD KB.checkSubChain_sound | OPEN | Reviewed semantic alignment with independently checked KB statement; keep asserted vs world true apart |
| L10 | Article-local certificate → discovered 51-QID elaboration | JMD Wikidata importer/query engine, SLR world-follow, Agda GWB roadmap | OPEN | Same prover/checker on per-QID immutable snapshots, proof-preserving positive extension, explicit residual ledger |

## Maximum cut / proof dependency graph

```text
QID/title --L1--> pinned source identity
                      |
JMD import ------------+--L2--> checked M12 source / parser
                                   |
PR #112 source receipts --L3--------+--> typed semantic fibre
                                             |
       Agda parity: antecedent/identity --L4--+
       Agda parity: trace/hyperfabric ---L5--+--L8a+L8b--> SourceQueryLicence
       reviewed event equivalence ------L6--+
       S28 temporal --------------------L7--+       |
JMD checked property/query ------L9-----------------+--> article theorem
                                                          |
GWB 51-QID world / exact revisions ---------L10-----------+--> elaboration
```

The *maximum cut* is L3 + L5 + L8b: the real-data representation,
coherent cross-sentence transport, and proof that the tested consumer covers
the actual semantic fibre. L8a alone is not semantic completeness.

## Exact runnable checks

From the existing PR #112 branch with pinned Lean 4.28.0 and cached olean files:

```bash
lake env lean DASHI/output-final_aristotle/RequestProject/Slr/FiniteConsumerCertificate.lean
lake env lean DASHI/output-final_aristotle/RequestProject/Slr/DbSourceProducer.lean
```

Use the repository's targeted Lean proof runner and original SLR PostgreSQL
setup for integration; do not rerun spaCy as an alternative language producer,
generate a new TAR, or rebuild world facts from an experimental JSON label.

Required negative controls: absent/false S28 `source_trace_join_complete`;
forged source literal; changed token dependency head; missing statement ancestry;
duplicate provenance ref; false actor identity; false event equivalence; false
time attachment; truncated fibre misrepresented as exhaustive; changed QID
sitelink/revision; world-truth promotion.

## Proof/authority policy

* Preserve meta-introspector/JMD attribution for Wikidata checker theorems.
* Reuse existing original SLR and golden Agda owners; no duplicate ontology.
* Keep source assertion, proposition, event occurrence and proof-in-a-snapshot
  as independent semantic axes.
* Negative results (unresolved/contradicted) are certified results, not failed
  or silently replaced answers.
* Lean kernel checking of generated certificates is required; no runtime exit
  status, cached OLEAN or `sorry` provides an external-evidence theorem.
* The new code in this update is SOURCE-WRITTEN and not reported as kernel
  accepted until an actual Lean 4.28.0 run succeeds.
