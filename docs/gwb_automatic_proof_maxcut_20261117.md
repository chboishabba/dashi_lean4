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

## Implementation added after the initial roadmap snapshot

The active PR #112 branch now contains the following additional source-written
Lean proof/adapter declarations and runners. **None is declared kernel-passed
before the operator runs pinned Lean 4.28.0.**

* `Slr.GwbTypedFibre.decodeCheckedRows?`: parses every candidate, clause
  alternative and unresolved residual into a typed, source-indexed Lean
  observation after the existing original-source GWB checker has passed.
  Failure to decode any row rejects the entire fibre.
* `Slr.GwbProofComposition.checkedFiniteArticleAnswerSound`: composes
  exhaustive finite consumer constancy and the existing real
  `SourceQueryLicence` into JMD/SLR document-query soundness; source/semantic
  correspondence is still an explicit premise.
* `Slr.GwbProofComposition.independentArticleAndKBResultsSound`: preserves
  both an article-relative answer and a JMD KB property witness as
  independent results, without manufacturing an alignment.
* `Slr.GwbWorldGraph.checkCandidateWorldGraph`: checks original
  `slr-wikimedia-world-follow-v1` graph shape and provenance status.
* `Slr.GwbWorldGraph.checkedWorldPropertySound`: checks each independently
  re-imported item-valued Wikidata property by the original JMD
  `PKB.supportsB_iff` theorem. Unsupported edges remain obligations;
  this does not prove a shared historical Wikidata snapshot.
* `tools/GwbProofRunner.lean` now offers `db-m12-check`, `db-s28-check`
  and `world-graph-check` (online/cache-first or offline) with explicit
  kernel-auditable positive receipts.
* `scripts/run_gwb_maxcut_acceptance.sh` builds the targeted owner
  modules and runs the proof-composition audit; `--full` also replays
  the original Rust/Lean source and negative-control suite without TAR.
  `--strict` never claims production semantic completeness from these
  checks alone.
* `tools/publish_gwb_proof_receipts.py` now requires typed semantic
  decoding, the conditional composition proof execution, and the
  original intended Lean rejection marker for every negative control.

**Important:** The GWB property graph edges were initially acquired
without native Wikidata statement context. Therefore the graph is not
itself a proof. The new JMD reimporter can prove positive
`PKB.supportsB` statements for the separately fetched snapshots and
records the unproved remainder. An eventual article-to-property semantics
theorem still requires a checked alignment.

## Operator one-command handoff

From the existing PR #112 working branch, with Lean 4.28.0 and JMD dependencies
already cached:

```bash
bash scripts/run_gwb_maxcut_acceptance.sh --proof-only
```

To replay the actual original Wikipedia source and Rust semantic observations:

```bash
SLR_ROOT=/home/c/Documents/code/slr \
  bash scripts/run_gwb_maxcut_acceptance.sh --full
```

The original source fixture must already be present in
`.dashi/gwb-source/`; no TAR, parser reimplementation, extra archive,
or whole-`wikidata` executable build is required.

Optional original DB-native outputs:

```bash
GWB_DB_M12_JSON=/path/to/slr-db-m12-product.json \
GWB_DB_M12_LITERAL=/path/to/exact-source-literal.txt \
GWB_DB_S28_JSON=/path/to/slr-s28-event-chronology-candidates.json \
GWB_DB_S28_EVENT_REF=original-event-ref \
bash scripts/run_gwb_maxcut_acceptance.sh --proof-only
```

Optional existing 51-QID world graph, rechecked against JMD's original
Wikidata getter/importer:

```bash
GWB_WORLD_GRAPH_JSON=/path/to/gwb-wikimedia-world-graph.json \
GWB_JMD_ENTITY_CACHE=.dashi/gwb-world/jmd-entity-cache \
GWB_WORLD_JMD_REPORT=.dashi/gwb-world/jmd-property-proof.json \
bash scripts/run_gwb_maxcut_acceptance.sh --proof-only
```

For a deterministic cache-only replay set `GWB_WIKIDATA_OFFLINE=1` and
populate the JMD entity cache first. The property report records per-QID
Wikidata `lastrevid` when available, all original graph edges, supported
edge count, and the complete unresolved candidate edge inventory. It does
not assert that Wikidata was acquired as one simultaneous snapshot.

### Exact remaining empirical/theorem gates after this source patch

1. Lean 4.28.0 kernel acceptance of the newly source-written modules and
   original M12/S28 restoration.
2. Original PostgreSQL parser-run and reviewed M12/S28 receipts on the same
   source object, including negative controls for missing ancestry.
3. A proof that the finite emitted readings cover all *production-live*
   readings relevant to each consumer, or an alternative direct semantic
   invariance theorem that covers unenumerated readings.
4. Checked GWB cross-sentence identity/event equivalence and temporal
   assertions, not just source-bound syntactic roles.
5. Checked article-proposition ↔ JMD property alignment (separate from
   independently proved KB support).
6. A reproducible per-QID graph acquisition/reimport/revision ledger,
   and eventually a proof-preserving elaboration across all discovered
   QIDs; the initial historical 51 is not a permanent closed-world count.

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

## Final source implementation / first-run gates (PR #112)

The source implementation has advanced beyond the original L1–L10 table:

| Cut | Concrete executable / theorem | Source state |
|---|---|---|
| L1 | `GwbArticleIdentity.checkGwbRootIdentity`, `article-qid-check` | Checked Q207/sitelink/revision **code written**; needs original EntityData and Lean run |
| L2 | Reused PR #111 `checkNativeM12Literal`, `checkS28Provenance`; `db-m12-check`, `db-s28-check` | Structural checker written, actual DB receipt still required |
| L3 | `GwbTypedFibre.decodeCheckedRows?`, `typedRowsRemainSourceBound` | Exact original Rust candidate/alternative/residual view written; semantic completeness not implied |
| L4/L5 | `GwbHyperfabric.Fragment`, `join`, `restrict`, `restrictionCommutesWithJoin`, `narrowMention` | Same-checked-source transport and candidate-history laws written; positive real actor identity still open |
| L6/L7 | Existing S28 provenance reconstruction and Agda event/chronology owners | Real governed event/time admission still open |
| L8 | `FiniteConsumer.completeFiniteFibreConsumerClosed`, `omittedLiveReadingBlocksCompleteness` | Generic theorem and negative theorem source written; production-live reading coverage open |
| L9 | `GwbProofComposition.independentArticleAndKBResultsSound` | KB proof kept separate from article reading; actual semantic alignment open |
| L10 | `GwbWorldGraph.checkCandidateWorldGraph`, `proofForEdge?`, `checkedWorldPropertySound`, `world-graph-check` | JMD snapshot-relative per-edge proof and unresolved inventory written; automatic article-semantic graph elaboration still open |
| System | `GwbArticleSystem.checkedArticleLocalSystemSound`, `checkedArticleAndRootKBPropertySound` | Conditional end-to-end article-local theorem source written |

**Every row above remains unaccepted as a new Lean kernel result until your
pinned local run passes.** The pre-existing PR #112 Rust and Lean receipts
remain the last completed empirical evidence. Compile success of this new
code will close source-level and conditional theorem gates; it will not by
itself establish a complete semantic resolver or independent historical
event truth. The original SLR native output, JMD entity data and live
M12/S28 ledger must be consumed under their own checked scopes.

### Recommended first run

```bash
cd /home/c/Documents/code/dashi_lean4
git switch feat/gwb-targeted-proof-cache
git pull --ff-only
bash scripts/run_gwb_maxcut_acceptance.sh --proof-only
```

Then, using your existing original SLR checkout and locally retained
`.dashi/gwb-source/` data:

```bash
SLR_ROOT=/home/c/Documents/code/slr \
  bash scripts/run_gwb_maxcut_acceptance.sh --full
```

If the larger GWB graph is available from the original `dashi_agda` world
follow, set `GWB_WORLD_GRAPH_JSON` to that JSON before the first command
to include source-backed 51-QID JMD reimport. Do not run the historical
`run_gwb_wikimedia_world_follow.sh` solely to get a TAR: that legacy
script packages a TAR on exit. The new proof handoff consumes an existing
graph JSON directly and creates no TAR.

The `--strict` option deliberately exits nonzero while full production
semantic coverage, reviewed event/time and article-to-world alignment are
unpaid, even if all existing structural certificates pass.
