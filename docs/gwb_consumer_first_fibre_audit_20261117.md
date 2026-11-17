# GWB Rust-first source/semantic proof boundary (17 November 2026)

**Production rule:** SLR Rust and its original PostgreSQL source/parser run
are authoritative for source observation. Do NOT call SensibLaw/spaCy/Python
producers or construct another GWB-specific fibre. Proofs precede any
interpretive promotion. JMD/meta-introspector original ontology work retains
its attribution. This PR is the one working PR for this Lean repository.

## Existing systems before new construction

- SLR Rust PR #78: native pnf-db-checked, sealed M12 parser evidence, original
  dependency token/region parity, and timeline-candidates over persisted S28.
- SLR original full GWB tranche: 10 narrative sources (six public biographies,
  four books), canonical projection, direct/reference parity, expanded frontier,
  and GWB-reviewed M12/S28/S29 capstone. The older controller imports Python
  spaCy; it is NOT the selected production entry point.
- SensibLaw GWB local binding baseline: 6 public biographies, PartialPNF,
  immutable reference revisions, set-valued referents, revision-local demands.
  P0c typed resolution and H3/H6/H9 consumer-dependent runtime already exist.
- ITIR GWB linkage audit/braid: nonempty multi-source semantic relations,
  source-to-review lineage and unresolved historical timeline reconciliation.
- Golden Agda: ConsumerDescentMinimalObserverExact,
  SemanticConsumerRelativeClosureExact,
  AdaptiveSemanticReasoningLoopExact, SLRConsumerRequirementV2Exact,
  SLRGWBHeterogeneousChronologyCapstoneExact.
- JMD Lean: DbSourceProducer, DocumentQuerySound, TemporalDocumentProof.
  A checked Q207 KB fact is not a licensed statement about the article.

## SufficientConsumer is query-indexed

ConsumerSufficient(O,q) means that equal O observations imply equal q
answers, or equivalently that q factors through O. It is not a licence to
force all source readings into one identity or one total timeline.

| Query result | Sufficient observer | Status on pinned GWB source |
|---|---|---|
| literal text mention | source digest, run/region, exact span and token | M12 DB-native checking implemented; real DB replay pending |
| proposed grammatical roles | M12 dependencies, scope and original head/span coordinates | SLR native candidate compiler implemented |
| which actors / who did what | PartialPNF alternatives and query-relevant identity/scope; collision or reviewed correspondence | real-source q-specific closure pending |
| lexical year mentioned | exact source/token literal | saved archive contains 311; not a temporal attachment |
| source-asserted event date | typed S28 event/time edge, speaker, scope and source lineage | review/attachment gate pending |
| source-relative order | compatible S28 before/after in one account, plus identity and temporal transitivity | S28 carrier and proof theorem present; concrete active edges pending |
| paragraph/page summary | q-factorisation through hierarchical fusion with source/scope retained | generic Agda proof; concrete SLR binding pending |
| actual historical occurrence | external occurrence evidence with independent admissibility | explicitly outside article-only proof |

## Concrete bug fixed

The previous Lean S28 decoder checked only that source_trace_join_complete
was *present*, accepting false. That cannot satisfy a proof-sensitive JMD
consumer. This PR changes the check to require some true, while SLR PR #78
now fails the native Rust S28 command on incomplete M12 statement ->
observation -> event chains. Neither boolean by itself establishes a
semantic interpretation; this is a necessary structural gate.

## Canonical Rust-only local acceptance

The shell command below uses *the original PostgreSQL run*, not the archived
article PNF JSON or a reconstituted source record. Set all required
environment values from the actual SLR run receipts; do not invent IDs.

    export SLR_BIN=/absolute/path/to/slr/target/debug/sensiblaw
    export DATABASE_URL=...    # original migrated SLR PostgreSQL database
    export PARSER_RUN=...      # original parser run
    export STATEMENT_REF=...   # M12 source statement
    export DOCUMENT_REF=...
    export SOURCE_REV=...      # revision reference
    export REGION_REF=...      # original persisted region
    export START_CHAR=... END_CHAR=...
    export LITERAL_FILE=...    # exact original region text
    export EVENT_REF=...       # optional reviewed S28 event
    bash scripts/run_gwb_native_proof_acceptance.sh

The script compiles JMD and invokes:
- JMD slr-db-pnf -> Rust pnf-db-checked -> sealed M12/parser/source checks;
- optionally JMD slr-timeline -> Rust timeline-candidates -> S28 source trace.

S28 rejection on incomplete M12 lineage is expected; it is an evidence
discriminator, not an excuse to create event identity from a label or year.

No independent Python P0b bridge remains in the production path. The old
scripts/replay_gwb_article_from_files.sh requires
ALLOW_LEGACY_GWB_PYTHON_REPLAY=1 as an explicit historical-only opt-in. Its
Wikipedia/SLR JSON replay and Q207 getter are not the production M12/S28
proof and cannot discharge SourceQueryLicence.

## Exact remaining proof/runtime obligations

1. Execute SLR Rust original parser/run ingestion and M12 DB-native gate
   on pinned GWB Wikipedia source revision. Flat tar is regression evidence
   only; no original PostgreSQL run is present in that archive.
2. Read S28 reviewed event joins and ensure complete M12 provenance. The
   Boolean must be true and checked, never just included.
3. For each declared q, compute the actual admissible semantic fibre and
   exhibit factorisation/closure OR a pair of incompatible readings. Reuse
   SensibLaw typed resolution and H3/H6/H9 consumer run; no parallel model.
4. Instantiate source-query licence and scope-preserving hierarchy in JMD
   Lean. Existing conditional theorem cannot prove a particular article
   query until source interpretation and adequate q correspondence are paid.
5. Run pinned Lean kernel and Rust cargo tests locally; no cargo/lean/lake
   toolchains are present in this sandbox. Do not claim kernel completion.

The uploaded flat archive (revision 1385850169) reports 643 sentences,
17547 parser tokens, 1468 candidate predicates, 311 lexical years and
11975 materialised P0b mentions from the previous Python P0b replay. Those
counts do not establish identity, event dates, article meaning, or historical
occurrence and do not authorise Python as production.
