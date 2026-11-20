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

## 2026-11-17 first-run dependency fix

Operator's first `--proof-only` run passed `Producer`,
`DocumentQuerySound`, `TemporalDocumentProof` and
`WikipediaArticleProof`, then stopped at `GwbArticleIdentity`
because `RequestProject.Cli.Import.olean` was absent from the targeted
cache. This is an import-build ordering issue; it does **not**
establish a failure of an article theorem.

The proof-only and full entrypoints now first invoke the shared
`scripts/build_gwb_jmd_prerequisites.sh` to compile precisely the
original JMD `Core`, `Reachability`, `Engine`, `Merge`,
`Properties`, `PropertyEngine`, `Cli.Import`, `Cli.Format`,
`Cli.Fetch`, `Cli.Derive` import closure. This is **not**
`lake build wikidata`, and runs no new parser, data getter or TAR.

A source-level finite-list decidability correction was also made to
`FiniteConsumerCertificate.checkConstant`: the checker now
evaluates all actual list pairs with `List.all` instead of
attempting an unbounded `Decidable (∀ reading : Reading, ...)`.
The general soundness result continues to rely on an explicit
live-fibre completeness witness.

Re-run:
```bash
git pull --ff-only
bash scripts/run_gwb_maxcut_acceptance.sh --proof-only
```

**Status:** pushed source fix, not yet tested with Lean 4.28.0.
If the next compile reports a theorem error, capture the precise
module, line and diagnostics. Do not fall back to the whole
`wikidata` build or assert that a partial compile is a proof receipt.

## P4 source-indexed consumer maximum cut — 17 Nov 2026

The production-backed candidate fixture and full original Rust/Lean run
were previously accepted at PR #112 head `336488ccf`, with 643 source
sentences, 4,190 candidate rows, 814 alternative fibres and 15,595
residuals. The original receipt manifest still says that *full production*
semantic identity, chronology and consumer coverage remain unpaid.

New source-written owner: `RequestProject.Slr.GwbP4SourceLicence`.

This is the first *real GWB source-observation* positive
`SourceQueryLicence`, rather than a synthetic finite countermodel.
The checked original article and Rust receipt are decoded into the
existing `GwbTypedFibre.CheckedRows`, then indexed by the existing
`GwbHyperfabric.Fragment`. The executable consumer counts source
sentences, syntactic candidates, clause alternatives, typed residuals,
or source candidate/residual kinds. Two fragments, selected by original
sentence parity, are rejoined as the same indexed source object.
`checkedGwbP4SourceLicenceSound` derives jointly:

* the original `checkRealGwbNativeFibreReceipt = true` proof;
* every joined-fragment row belongs to the original checked receipt;
* the positive query answer follows from an actual `SourceQueryLicence`
  for those rows, independent of abstract unresolved semantic axes.

The key mathematical cut is that source-observable queries are
**consumer-sufficient even without enumerating all world/actor/event/time
interpretations**. That does NOT mean an identity, occurrence or
event-time consumer is closed. `unresolvedAxesDoNotChangeSourceAnswer`
makes this boundary explicit.

Existing Agda owners remain golden for semantic identity, event and
chronology refinements. No new NLP producer or alternate event ontology
is added.

Acceptance path:

```bash
bash scripts/run_gwb_maxcut_acceptance.sh --proof-only
SLR_ROOT=/path/to/original/slr bash scripts/run_gwb_maxcut_acceptance.sh --full
```

The proof-only run compiles/audits `GwbP4SourceLicence.lean`.
The full run requires the original ignored GWB source fixture and demands
the new `GWB_P4_SOURCE_LICENCE_KERNEL_OK` marker from the **actual Rust
receipt** after Lean verifies original source binding and typed decoding.
Receipt publication also requires the new P4 build log and marker.
The 10 existing negative controls remain mandatory.

**Status of this P4 addition: source written and committed; no claim of
Lean acceptance until the operator runs it.**

Outstanding P4 semantic frontier (different from the positive source-only
cut above): reviewed cross-sentence referent identity, original M12/S28
event joining, a semantic interpretation interface for those same
source objects, and a query-specific `SourceQueryLicence` for an identity
or event-time question under independently checked producer/review
evidence. A source-only positive result is not authority for those
different queries.

### P4 final composition extension

`GwbP4ArticleEndToEnd.originalGwbArticlePositiveSourceQuery` closes the
previously unconstructed **source-only** `SourceQueryLicence` premise of
`GwbArticleSystem.checkedArticleLocalSystemSound`: with the independently
checked Q207 Wikipedia/Wikidata sitelink and the original source-checked
GWB Rust typed rows, the theorem supplies the actual licence and proves
the source-observable result end to end. The specialisation
`sourceActorCandidatesAndReferenceResiduals` proves the actor-*role
candidate* and unresolved-reference-*residual* source counts. These do
not prove referent identity, claim truth or historical event time.

The exact five-input proof runner command is:

```bash
lake env lean --run tools/GwbProofRunner.lean article-p4-check \
  .dashi/gwb-source/article.txt \
  .dashi/gwb-source/slr-record.json \
  .dashi/gwb-source/article-candidates.json \
  artifacts/gwb-semantic-proof/slr-rust-semantic-expansion.json \
  /path/to/original-Q207-EntityData.json
```

If `GWB_Q207_ENTITY_JSON` is set, the unified proof-only script now
rechecks the Q207 sitelink and (where the original native Rust receipt is
available) additionally runs the source-QID/native-fibre P4 theorem.
The original SLR full runner compiles the composed theorem and retains
`p4-article-end-to-end-build.log` as a required receipt. No Q207
document is invented when one is absent.

P4 source-only theorem acceptance and the five-input real Q207 join have
**not** been locally executed by the author of this source patch.
The pre-existing PR #112 `336488ccf` run remains the accepted P3 proof
substrate.

## P5–P10 integrated maximum cut — 17 November 2026

The verified P4 source proof substrate is PR #112 `eada25574`.
The **actual committed manifest** states:
`reviewed_semantic_transports: NOT_TESTED`,
`production_db_s28: NOT_TESTED`,
`full_consumer_factors_through_certificate: NOT_PAID`,
and `historical_occurrence: NOT_LICENSED`.

### New implementation

`Slr/GwbP5P10ExactWeld.lean` reuses original source owners without
inserting a simulated semantics:

- **P5** `SourceAnchor` and `ReviewedIdentity`: real
  `CheckedRows` and sentence member; reviewed mention/referent
  relation is separately required. `p5OriginalSourceSurvivesReview`
  transports the original native receipt.
- **P6** `ReviewedEvent`: original `CheckedNativeM12Literal`,
  `CheckedS28Provenance`, source-statement link and independently
  reviewed event equivalence. `p6PreservesBothOriginalChecks`.
- **P7** `ReviewedTemporal`: time-event/source meaning is explicit
  additional evidence, not extracted from S28 candidate-only flags.
- **P8** `ReviewedConsumer`: requires the EXISTING
  `SourceQueryLicence`. Its soundness is `p8ConsumerAnswerSound`;
  `FiniteConsumer.CompleteEnumeration` remains available when all
  production-live interpretations can actually be proven covered.
- **P9** `ReviewedArticleKBAlignment`: explicit reviewed
  article-proposition ↔ JMD statement alignment, not just a Q207
  sitelink; `p9AlignmentRetainsIndependentChecks`.
- **P10** `CompletelyCheckedWorld`: all original candidate world edges
  need an independently reimported JMD
  `GwbWorldGraph.proofForEdge?` witness, otherwise the inventory is
  unresolved. `p10AllEdgesJmdSupported`.

`fullChainKeepsSeparateEvidence` is a compositional theorem
requiring actual review objects for P5/P6/P7/P9 and full JMD edge
coverage. It **does not** construct those witnesses from names,
unpaid parser candidates, review-reference strings or success flags.

Original Agda research **already contains a relevant reviewed
Wikimedia identity overlay**, in
`chboishabba/dashi_agda/fixtures/slr/gwb-reviewed-wikimedia-identities-v1.jsonl`
with 10 document-level coordinates and
`SLRGWBReviewedWikimediaIdentityAndTieredTransportExact.agda`.
Those records are **candidate-only** and explicitly distinguish
`topic-anchor-not-source-object` from exact-work identity. In
particular, the six Q207 subject-person topic anchors are not a
sentence-level mention→referent review for the pinned GWB article.
The source-work entry for *Family of Secrets* intentionally has no
reviewed QID. P5 cannot promote this overlay into actor identity.

A new fail-closed audit
`tools/gwb_p5_p10_evidence_audit.py` classifies existing real
receipts and optionally the exact overlay, S28 candidate record and
JMD world report. Its negative tests reject unreviewed promotion and
forged source revisions, and it never marks a semantic gate closed on
a `candidate_only=true` document. The proof-only runner now compiles
the integrated Lean owner, runs these negative tests and audits the
previous actual P4 manifest. This audit passage is not a claim that
reviewed witnesses exist.

### Acceptance and next decisive source requests

```bash
git pull --ff-only
bash scripts/run_gwb_maxcut_acceptance.sh --proof-only
SLR_ROOT=/home/c/Documents/code/slr bash scripts/run_gwb_maxcut_acceptance.sh --full
```

To inspect an original reviewed overlay without promotion:

```bash
python3 tools/gwb_p5_p10_evidence_audit.py \
  --overlay /path/to/dashi_agda/fixtures/slr/gwb-reviewed-wikimedia-identities-v1.jsonl
```

**Status:** full proof architecture and fail-closed evidence discriminator
implemented and pushed; *new* Lean 4.28 execution not yet run by the
operator. None of P5–P10's substantive GWB-specific reviewed identity,
event equivalence, temporal admission, complete semantic coverage,
semantic article/KB equivalence or universal 51-QID statements is yet
established. A proof whose positive conclusions depend on those
external evidence premises is NOT a closed empirical semantic gate.

## 18 November: P5–P10 actual acceptance audit and JMD scope correction

The executed local P5–P10 acceptance commit is `f429e5573`.
The original GWB Rust/Lean receipt rechecks all 643 sentences, 4,190
candidates, 814 alternative fibres and 15,595 typed residuals. It
also reports 1,146 source-syntactic `Role(Actor)` candidates and
62 `ReferenceAttachmentUnresolved` residuals; neither proves an
actor's external identity. The P5–P10 compiler emitted three
unused-variable warnings and no Lean errors, with normal
`#print axioms` foundations rather than `sorryAx`.

**Important architectural ownership correction:** original JMD
`Engine`, `PropertyEngine`, `Cli.Import` and `Cli.Derive`
formalize the imported Wikidata KB's internal consistency,
hierarchy, property constraints, saturation, and KB-relative
derivations. They are not an article parser, actor-identity
resolver, event evaluator, source-truth judge or semantic
reading engine. SLR/DASHI exclusively owns the article-internal
semantic interpretation. Any article–JMD comparison must first
provide an independently reviewed alignment; JMD then verifies
only the ontology/KB-relative consequence.

A source-anchored, non-promoting original evidence inventory is
committed at
`artifacts/gwb-semantic-proof/p5_p10_original_evidence_inventory.json`.
It reuses the original DASHI Agda
`fixtures/slr/gwb-reviewed-wikimedia-identities-v1.jsonl`:
10 candidate-only acquisition coordinates, eight topic anchors,
one exact source-work coordinate, and one unresolved work QID
(*Family of Secrets*). Six Q207 coordinates identify subject
topic documents; none is an original 643-sentence actor mention
identity certificate. These are useful *actual original review data*
for acquisition and source attribution, but **do not instantiate**
the `ReviewedIdentity` premise of P5.

The committed acceptance still has no DB-native M12/S28
instance and no independently imported 51-QID JMD property-coverage
receipt. Accordingly P6/P7/P10 have no positive instance here.
P8 production-live semantic completeness and P9 article proposition
↔ KB statement alignment are separately open. The integrated Lean
theorems are reusable *conditional welds*, not executed semantic
completion.

Highest-alpha next cut: construct the original source-span anchored
review identity/temporal data in SLR; replay M12/S28 in their
original DB-owning runtime; only then query JMD's imported KB for
independent consistency of explicitly aligned propositions.
Do NOT require Wikidata coverage for an entirely article-internal
consumer and do NOT treat a QID sitelink as an article proposition.


## 2026-11-20 — authoritative ownership and canonical proof population

Supersedes earlier commands that made the experimental Rust observer
mandatory. SLR (chboishabba/slr) is the production runtime; SensibLaw
is historical planning/prototype prior art, not the production owner.
Lean and Agda are golden. ITIR orchestrates. Original JMD supplies
independent Wikidata ontology and KB-relative reasoning.

Accepted baseline 891d4e7ca: original source acceptance, 1468 predicate
observations, 17547 parser tokens, 43 dependency labels. Do not confuse
these with reviewed events or historical claims.

Implemented canonical first cut: GwbCanonicalSourceProof.lean constructs
SourceAnchor from CheckedArticleExtraction and actual original event
membership; populate elaborates one instance per event. The canonical
runner invokes canonical-populate and publishes the full unchanged event
values, checking equality against the original projection. Expected 1468
instances, pending local Lean execution. No new semantic producer.
These are runtime proof-bearing values; JSON is a replayable result
inventory, not a serialized Lean kernel proof.

The historical GwbP5P10ExactWeld still contains unconstrained Prop
premises and Rust-indexed anchors. Do not use it as a production semantic
certificate. The next migration must use concrete source/mention and
review coordinates, actual admitted identity/binding evidence and
event joins, and the existing SourceQueryLicence consumer theorem.

Production prior art recovered:
- slr/crates/sl-pg-source-store/src/gwb_chronology_capstone.rs and
  examples/gwb_chronology_capstone.rs: reviewed GWB statement/observation/
  event/temporal/claim/contestation materialisation and persisted ancestry.
  The capstone uses a heterogeneous reviewed corpus; do not assume it
  is identical to the pinned single Wikipedia article.
- slr/docs/architecture/formal_proof_bridge.md:
  FormalProofDemand -> independent kernel checker -> FormalEvidenceReceipt
  -> exact obligation/digest payment -> sparse_wake recurrence.
  Consume this contract rather than inventing a parallel payment ledger.

Remaining cuts:
P5 actual original SLR admitted identity witness transport; P6/P7 persisted
same-source M12/S28 event and time coordinates; P8 evaluate a real producer
consumer with its source-relative licence and return proof-bearing answers;
P9 independently reviewed proposition alignment; P10 original JMD KB
consistency/derivation, followed by existing formal proof bridge payment.
P9/P10 are optional for article-internal queries.

Run canonical acceptance with bash scripts/run_gwb_maxcut_acceptance.sh --full.
Historical Rust probe remains opt-in. TAR and unrelated local outputs are
untouched. The newly written Lean module has not yet been kernel checked
in the patch author's environment.
