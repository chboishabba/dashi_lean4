# GWB source/PNF → consumer-fibre → JMD Lean proof acceptance

**Working PR:** [dashi_lean4 #111](https://github.com/chboishabba/dashi_lean4/pull/111);
reuse SLR [#78](https://github.com/chboishabba/slr/pull/78) for native M12/S28.
Agda is golden; SLR Rust is production; SensibLaw Python is historical.
All actual source and fibre correctness claims must retain that separation.

## 1. Run the full available proof suite against the exact TAR

From the root of **dashi_lean4**, with the repository's root
`leanprover/lean4:v4.35.0-rc3` toolchain installed:

```bash
bash scripts/run_gwb_lean_proof_suite.sh /path/to/gwb_article_proof.tar
```

The script pins archive SHA-256
`6bbad0f9bcc2f0aa2e0e6f77f15692a945c1331a6337cfe202c19a58e2460f9e`,
checks the active Lean version, unpacks only the three original source/parser
observation files to a temporary directory, executes `lake build wikidata`,
then invokes two commands:

```bash
lake exe wikidata gwb-fibre-proof
lake exe wikidata gwb-article-check ARTICLE.txt SLR-RECORD.json CANDIDATES.json
```

**No spaCy, Python parsing, simulated world state or external historical fact
acquisition.** The TAR is a historical, parser-observation *fixture*.
The executable's import graph checks the new Lean theorems at build time.

Expected on success:
- `GWB_FIBRE_THEOREMS_KERNEL_OK`
- `JMD_LEAN_SOURCE_PROOF_OK sha256=a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233`
- `GWB_LEAN_CONSUMER_AND_ARCHIVE_PROOF_SUITE_PASS`

Output logs: `.gwb_lean_proof/lean-build.log`,
`consumer-fibre-proof.log`, `axiom-audit.log`,
`article-source-proof.log`, `proof-boundary.txt`.
The explicit `#print axioms` step inspects kernel dependencies and rejects
`sorryAx`/`admitAx`; ordinary Lean `propext` is not an admission shortcut.

## 2. What is actually proved

Module:
`DASHI/output-final_aristotle/RequestProject/Slr/GwbConsumerFibreProof.lean`

- Joins two typed fibres of meaning + provenance annotations by union, with
  **idempotence, commutativity, associativity** and retention of both distinct
  execution annotations. This is a Lean witness of the established
  Agda `TypedEventuallyConsistentFibreSystemExact` interaction law,
  not a replacement for SLR's production fabric.
- Fully constructs `SourceQueryLicence` for two **source-observation**
  consumers (reporting of a claim and presence of a year string); no globally
  resolved actor, event or timeline is required.
- Defines two competing semantic completions of the *same* quoted GWB source
  observation. Proves nonfactorability for **world occurrence**, unique actor
  identity, attached event date and embedding scope. These are mathematical
  countermodels, not a claim about actual Iraqi WMD or historical events.
- Reuses `TemporalDocumentProof.scopedTemporalOrderClosureSound`: only
  scope-indexed, independently licensed edges may enter temporal closure.

Module:
`RequestProject/Slr/WikipediaArticleProof.lean`

- Independently checks the **actual archived** literal and its raw UTF-8
  SHA-256, every emitted candidate's original token/role source support,
  and now *exhaustively* checks all original eligible predicate positions,
  all immediate actor/patient dependencies, PROPN token cardinality and
  uniqueness, year-index completeness/uniqueness and source paragraph blocks.
- This is syntactic *source-observation* adequacy only. It intentionally does
  **not** certify the flattened `by` token as a semantic actor or the
  embedded `had` as world occurrence.

Independent local reference comparison on the exact uploaded source before
the Lean run: eligible predicates **1,468/1,468**, zero actor/patient child
mismatches, PROPN **2,620/2,620**, literal-year index **311/311**.

## 3. Native Rust-only production M12 + S28

Use genuine original persisted PostgreSQL parser receipts, **not identifiers
fabricated from the flat TAR**. See the existing script's argument names:

```bash
SLR_BIN=/absolute/path/to/slr/target/debug/sensiblaw \
DATABASE_URL=... PARSER_RUN=... STATEMENT_REF=... \
DOCUMENT_REF=... SOURCE_REV=... REGION_REF=... \
START_CHAR=... END_CHAR=... LITERAL_FILE=... \
EVENT_REF=... \
bash scripts/run_gwb_native_proof_acceptance.sh
```

`RequestProject/Slr/DbSourceProducer.lean` now checks **again, independently
in Lean**:
- exact raw UTF-8 literal SHA-256 supplied by native SLR and the actual bytes;
- every candidate/token/entity source span and token-head ordinal;
- the real source run / region / statement / revision identity;
- **all S28 source-statement, statement-observation, observation-event,
  temporal, claim and contestation reference joins**, and no semantic/truth
  promotion. The prior `source_trace_join_complete=true` flag is necessary
  but *not itself sufficient*.

A saved S28 native JSON response can be examined separately:
```bash
lake exe wikidata slr-s28-proof-check /path/to/s28-candidates.json EVENT_REF
```
A forged missing link, scope/source mismatch, changed event ref or promoted
truth/authority flag must return a nonzero exit status.

## 4. Limits / explicit gates

The actual **GWB semantic-fibre ledger**, reviewed event interpretation and
query-relative source meaning have not been supplied in this TAR and are
not manufactured by the new proofs. In particular:
- Source text *mentions* a WMD proposition: source-relative query.
- World actually possessed WMD: different consumer; requires evidence outside
  this article, not inferable from parsing.
- `He`/Bush identity: not a grammatical synonym; source-local alternatives
  stay live until resolved for the selected consumer.
- `2003` in a sentence: not a temporal event attachment.
- Source order: not world chronological order.

A complete historical/event query needs genuine reviewed/admitted SLR
`SourceQueryLicence` premises and matching S28 account edges. This remains a
separate open empirical input, not an unproved Lean `sorry`.

## 5. Verification reality

The authoring runtime has **no Lean, Lake or Rust compiler** and no original
SLR PostgreSQL fixture. Thus the files are SOURCE-WRITTEN and logically
reviewed but **NOT YET KERNEL-VERIFIED**. Run the exact commands above
and retain `lean-build.log`; do not accept this note as a successful run.
The root toolchain is `4.35.0-rc3` whereas the nested archived Aristotle
Lean directory has `4.28.0`. Use the **root** Lake build. A pinned mathlib
version mismatch or unrelated imported module failure is a genuine build
failure to fix, not a reason to weaken proof gates or replace tooling.
