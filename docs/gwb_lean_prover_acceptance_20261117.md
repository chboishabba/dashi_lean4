# GWB consumer-level acceptance — one TAR, one working PR

Working branch: [dashi_lean4 PR #112](https://github.com/chboishabba/dashi_lean4/pull/112).
SLR Rust is the production evidence owner; dashi_agda/Lean are golden;
SensibLaw Python is historical. Keep JMD/meta-introspector attribution.

## Single-artifact policy

**Only** `gwb_article_proof.tar` is retained for the round trip between
assistant and operator. The original seven evidence members are preserved
**byte for byte**. New diagnostic/Lean proof outputs go under `proof/`
inside the same TAR. There is no second TAR and no surviving extracted
working directory. Temporary staging is under the active repository, never
`/tmp`.

The tarball's SHA-256 necessarily changes after each refresh. Identity is
therefore pinned by the **original decoded UTF-8 article text** SHA-256
`a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233`
and revision `enwiki-revid:1385850169`, NOT by the old entire TAR SHA.
The old P0b JSON-string source hash remains historical evidence, not a
canonical replacement for the raw source hash.

## One-command targeted proof + refresh

From the root of `dashi_lean4`, with Lean **4.28.0** and its previously
built mathlib/Batteries `.olean` cache:

```bash
bash scripts/run_gwb_lean_proof_suite.sh gwb_article_proof.tar
```

The command executes the cached targeted Lean runner, the exact source
verifier, its axiom audit and **all five** forged-evidence negative controls.
`jq` is mandatory; no quiet skipping. It then runs the read-only
`tools/gwb_semantic_observer_audit.py`, checks real-source invariants, and
atomically refreshes the original tarball through
`tools/refresh_gwb_single_tar.py`.

The refresh tool independently **recomputes** the semantic observer audit
from the unchanged original TAR before accepting the report. It also
checks every original evidence member byte-for-byte before replacing the TAR.
On failure, the original TAR remains unchanged.

On success, inspect the ONE TAR:

```bash
tar -tf gwb_article_proof.tar
tar -xOf gwb_article_proof.tar proof/proof_run_manifest.json
tar -xOf gwb_article_proof.tar proof/semantic_observer_audit.md
tar -xOf gwb_article_proof.tar proof/semantic_observer_audit.json
tar -xOf gwb_article_proof.tar proof/axiom-audit.log
```

Temporary proof outputs are cleaned after packaging. The manifest records
the exact Lean version, Git head, proof execution status and **unpaid**
production semantic obligations. Archive refresh without a genuine Lean
run must state `NOT_EXECUTED_IN_THIS_REFRESH` and cannot fabricate logs.

## Actual GWB semantic discrimination

The uploaded revision has **643 original SLR sentences**, **1,468
candidate predicates**, **311 lexical year observations**, **11,975 P0b
mentions**, **16,034 candidate licences**, and **no admitted SLR semantic
fibre or S28 review receipt** in the archive.

The new source-grounded audit checks:
- **57** coordinated verbs with an embedded immediate parent, all
  flattened to `unresolved-source-assertion`. Sentence 18 has
  `claims → possessed (acl) → had (conj)`. A root-relative conjunction
  such as `set` (sentence 9) shares the same flat label. The consumer
  `is_conj_parent_embedded` therefore cannot factor through the single
  flat scope-label field. The ORIGINAL parser dependency rows do retain
  the distinction; this is not an SLR hyperfabric counterexample.
- **73** projected grammatical role tokens without corresponding
  materialised P0b mention spans: **59 actor `by`** tokens, one
  actor hyphen, nine patient `to`, three patient hyphens, and one
  patient percent symbol. These are *syntactic attachments*, not
  settled semantic actors/objects.
- The **311** lexical-year candidates stay unpromoted even in
  multi-predicate sentences. Mere co-sentential association does not
  provide a reviewed S28 event-date attachment.
- Named surfaces `George Walker Bush`, `Laura Welch`, `Bush`,
  `He`, `he`, `1977`, and `possessed` retain the P0b candidate
  type alternatives, **not unique identities or world claims**.

The script fails if the pinned real article no longer produces these
specific negative controls. The JSON ledger records source sentences,
predicate coordinates, parser dependency heads and exact source spans.

## Execute actual SLR Rust alternatives, residuals, and consumer answers

The single targeted runner now requires the **existing SLR Rust checkout**.
Set `SLR_ROOT` when it is not the sibling directory `../slr`:

```bash
SLR_ROOT=/path/to/slr \
  bash scripts/run_gwb_lean_proof_suite.sh gwb_article_proof.tar
```

This does **not** invoke SensibLaw Python, spaCy or another parser.
The caller reopens precisely the 643 original sentence dependency graphs
and invokes existing SLR Rust crate
`sensiblaw-semantic-expansion::check_expanded_parity` on all 17,547
original tokens. Its normalised **direct and reference** observations must
agree. All emitted candidate deltas, alternative-fibre coordinates, typed
residuals and projection failures are recorded source-span by source-span.

Important classification: **SLR itself labels that semantic-expansion
crate experimental/outside the certified direct path.** It is still the
real SLR Rust implementation, not a synthetic Python fibre; it is not a
reviewed DB-native GWB hyperfabric ledger or semantic transport.

This round also executes production SLR
`sensiblaw-legal-runtime::assess_consumer_adequacy` with five declared
real-article consumers. The source/text and syntactic-role observers can
be operationally adequate for source-only queries. The historical actor,
event-date and world-occurrence consumers must produce genuine
`NeedsResearch` receipts with missing `SemanticIdentity`,
`Temporal` and/or `FactualPredicate` axes, **not** silently close.
Each runtime receipt retains `factors_through_formally_proved=false`.
Abstract Lean source-closure theorems do not change those missing axes.

An important defect discovered while inspecting the production
consumer evaluator: when `required_semantic_refs` is empty, its
`graph_paid_axes` can add `SemanticIdentity` vacuously (0/0 matching
refs). **That is not evidence of actor identity.** The GWB person/time/
occurrence demands now target the *actual* sentence-18 source claim
candidate (not an empty or invented identity). The Rust receipt records
the empty-reference diagnostic, and neither the Rust nor Lean consumer
may treat it as reviewed identity/payment. Correcting that upstream SLR
edge case remains separate from the current PR #112.

The Rust runner also **tests the source content**:
- In the 2003 Iraq sentence, `possessed` (ACL) must produce a
  `ClauseInterpretationAmbiguous` residual and an alternative fibre;
  coordinated `had` must retain an `UnsupportedDependency` residual.
- All **59** original `agent:by` prepositions must be
  `ReferenceRelation` + `ReferenceAttachmentUnresolved`, never
  `Role(Actor)`.
- Ordinary `nummod` years must not become reviewed temporal anchors.
- Production review/occurrence/semantic-transport flags remain unpaid.

Five new mutated **native SLR Rust** receipts must be rejected by
the same cached Lean consumer: `agent:by` changed to `Role(Actor)`,
a falsely closed event-time query, forged world occurrence, dropped
alternative fibre, and a falsely closed residual. Their rejection logs
are kept only inside the TAR generated by the local Lean runner.

A new Lean module,
`RequestProject.Slr.GwbNativeFibreReceipt.lean`, checks the **actual
Rust-produced evidence rows** against the original parser-token
positions and source projection, including alternative-fibre
attachment, typed residuals and all five production consumer-adequacy
outcomes. It refuses semantic/occurrence promotion. The cached Lean
runner builds only this module and the previous source-consumer module,
not the large `wikidata` executable.

If and ONLY if Rust tests, original-source parity, the Lean kernel
and all negative controls pass, the same existing TAR is **refreshed
locally by that runner** to contain:

- `proof/slr-rust-semantic-expansion.json` — complete actual
  per-sentence SLR Rust candidate/fibre/residual emission.
- `proof/slr-rust-test.log`, `proof/slr-rust-expansion.log` —
  actual executed Rust test/runner logs.
- `proof/native-fibre-lean-build.log`,
  `proof/native-fibre-source-proof.log` — actual Lean kernel/receipt
  verification logs.
- `proof/proof_run_manifest.json` — explicit native SLR head,
  tested Lean head, exact source SHA, and remaining open gates.

Nothing in this PR regenerates or repackages the TAR before the local
Lean runner is invoked. New files are source code **inside PR #112**.
A refresh preserves externally owned `proof/` receipts and the seven
original evidence members; it changes the overall TAR SHA.

### Gate still open after this round

The experimental SLR expansion API does not emit the reviewed,
production **semantic transport ledger**, DB-native S28 joins, or
query-relative theorem payment for actual historical answers. These
remain explicitly reported absent. The next step requires original
production SLR DB evidence rather than counterfeit identities.

## Source-specific Lean consumer proof

New `RequestProject.Slr.GwbRealSourceConsumer` constructs dependency-
parent witnesses **from the actual saved 643-sentence SLR record and
1,468 projected events**, after rerunning the exact-source Lean checker.

The theorem `flatScopeCannotAnswerEmbeddedParent` proves that no
function of the *single flattened scope-label string* can answer
`is_conj_parent_embedded` for two source-backed witnesses with the
same label but different original dependency-parent kinds.

The targeted runner executes this as `semantic-scope`, emitting
`GWB_REAL_SOURCE_FLAT_SCOPE_NONFACTORABILITY_PROVED` and the actual
sentence/predicate/parent pair. Its kernel build is compiled narrowly
into the project-local `.olean` cache; there is no `lake build
wikidata`. The source-specific log is included in the refreshed TAR
as `proof/semantic-scope-proof.log`. The packer will NOT mark the
targeted proof run successful if this log or its expected marker is
missing.

**Scope of theorem:** this refutes only a lossy projection,
not SLR's production fibre/coordination semantics. The full SLR
semantic-fibre ledger and review receipts remain an independent,
still-unpaid empirical obligation.

## What the Lean kernel establishes

`GwbConsumerFibreProof.lean` proves the abstract ACI fibre union,
source-relative claim/year-string closure, and four non-factorability
countermodels (occurrence, actor identity, event date and scope).
`WikipediaArticleProof.lean` checks the actual source, exhaustive
selected syntax roles/predicates, years, and article source blocks.
The targeted `GwbProofRunner.lean` tests these without rebuilding
the full Wikidata executable.

The user reported a passing kernel run at the previous PR #112 head
`048c08375`; this is **not** evidence that the newer semantic-audit/
archive-refresh changes have executed. The authoring sandbox does not
contain Lean/Lake, so its new code remains uncompiled here.

## Still open — required production evidence

No real GWB `SemanticFibreLedger`, live alternatives/transports,
query-indexed H3/H6/H9 closure receipts, or reviewed S28 join exists in
the seven original members. Abstract countermodels alone cannot prove
that production Rust meets those obligations on the 643 sentences.

A future production Rust extraction must append **original,
source-bound semantic-fibre evidence and review receipts** to the same
TAR. Compare those directly against these witnessed source
counterexamples and the existing Agda/Lean consumer laws. Do not
substitute a Python NLP producer, synthetic provenance ID, or a
success flag for actual semantic evidence.
