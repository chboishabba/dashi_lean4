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
